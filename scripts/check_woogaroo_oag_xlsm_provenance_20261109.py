#!/usr/bin/env python3
"""Read-only OOXML XLSM provenance inventory, NOT regulator authentication.

No VBA execution, workbook recalculation, external-link opening, or
claim of agency approval. Reject malformed/unsafe/oversized ZIP inputs.
"""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path
from tempfile import TemporaryDirectory
from xml.etree import ElementTree as ET
from zipfile import ZipFile, BadZipFile, ZIP_DEFLATED
from posixpath import normpath, join

M='{http://schemas.openxmlformats.org/spreadsheetml/2006/main}'
R='{http://schemas.openxmlformats.org/officeDocument/2006/relationships}'
PR='{http://schemas.openxmlformats.org/package/2006/relationships}'
MAX_BYTES=150*1024*1024
MAX_MEMBER=40*1024*1024
MAX_TOTAL=200*1024*1024

def scan(path:Path)->dict:
    if not path.is_file() or path.suffix.lower()!='.xlsm':
        raise ValueError('Expected existing .xlsm candidate')
    size=path.stat().st_size
    if not 0<size<=MAX_BYTES:
        raise ValueError('Empty or oversized workbook')
    h=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(1048576),b''):
            h.update(block)
    with ZipFile(path) as z:
        infos=z.infolist()
        names={i.filename for i in infos}
        if len(infos)>5000 or len(names)!=len(infos) or sum(i.file_size for i in infos)>MAX_TOTAL:
            raise ValueError('Oversized or duplicate archive parts')
        if any(i.file_size>MAX_MEMBER or i.filename.startswith('/') or
               '..' in Path(i.filename).parts or '\\' in i.filename
               for i in infos):
            raise ValueError('Unsafe OOXML archive member')
        if '[Content_Types].xml' not in names or 'xl/workbook.xml' not in names:
            raise ValueError('Missing required OOXML workbook parts')
        root=ET.fromstring(z.read('xl/workbook.xml'))
        sheets=[{'name':s.get('name'),'sheetId':s.get('sheetId'),
                 'relationshipId':s.get(R+'id')}
                for s in root.findall('.//'+M+'sheets/'+M+'sheet')]
        # XLSX/XLSM sheet names are linked through workbook.xml.rels.
        # Never guess that sheet1.xml means the first named worksheet.
        relmap={}
        if 'xl/_rels/workbook.xml.rels' in names:
            relroot=ET.fromstring(z.read('xl/_rels/workbook.xml.rels'))
            for rel in relroot.findall(PR+'Relationship'):
                rid=rel.get('Id')
                target=rel.get('Target','')
                if rel.get('TargetMode')=='External' or not rid or not target:
                    continue
                candidate=normpath(join('xl',target)) if not target.startswith('/') else target.lstrip('/')
                if candidate.startswith('xl/worksheets/') and candidate in names:
                    relmap[rid]=candidate
        for sheet in sheets:
            sheet['worksheet_part']=relmap.get(sheet['relationshipId'])
        unresolved=[s['name'] for s in sheets if s['worksheet_part'] is None]
        # Do not silently accept a workbook where the reported logical
        # sheet name has no authenticated-in-package worksheet join.
        if not sheets or unresolved:
            raise ValueError('Unresolved declared worksheet relationship: '+repr(unresolved))
        extracted=[]
        for name in sorted(n for n in names if n.startswith('xl/worksheets/')
                           and n.endswith('.xml') and '/_rels/' not in n):
            xml=ET.fromstring(z.read(name))
            cells=[]
            for c in xml.findall('.//'+M+'sheetData/'+M+'row/'+M+'c'):
                f=c.find(M+'f')
                v=c.find(M+'v')
                if f is not None or v is not None:
                    cells.append({'cell':c.get('r'),'type':c.get('t'),
                                  'formula':f.text if f is not None else None,
                                  'formula_attributes':dict(f.attrib) if f is not None else None,
                                  'cached_value':v.text if v is not None else None})
            extracted.append({'part':name,'cells':cells})
        return {'case':'EPBC 2019/8575','status':'UNVERIFIED_WORKBOOK_CANDIDATE',
                'sha256':h.hexdigest(),'bytes':size,'sheets_declared':sheets,
                'sheet_cells':extracted,
                'declared_sheet_links_resolved':bool(sheets) and all(x['worksheet_part'] for x in sheets),
                'worksheet_relationships_checked':bool(relmap),
                'formula_count':sum(sum(c['formula_attributes'] is not None for c in s['cells'])
                                    for s in extracted),
                'vba_present':any(n.lower().endswith('vbaproject.bin') for n in names),
                'external_links_present':any('externallinks/' in n.lower() for n in names),
                'connections_present':'xl/connections.xml' in names,
                'signatures_present':any(n.startswith('_xmlsignatures/') for n in names),
                'formulas_recalculated':False,'approved_original_authenticated':False,
                'approved_cell_join_completed':False}

def selftest():
    with TemporaryDirectory() as d:
        p=Path(d)/'example.xlsm'
        wb='<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><sheets><sheet name="Inputs" sheetId="1"/></sheets></workbook>'
        rels='<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId5" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/></Relationships>'
        wb=wb.replace('sheetId="1"', 'sheetId="1" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships" r:id="rId5"')
        ws='<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><sheetData><row r="1"><c r="A1"><v>75</v></c><c r="B1"><f>A1*4</f><v>300</v></c></row></sheetData></worksheet>'
        with ZipFile(p,'w',compression=ZIP_DEFLATED) as z:
            z.writestr('[Content_Types].xml','<Types/>')
            z.writestr('xl/workbook.xml',wb)
            z.writestr('xl/_rels/workbook.xml.rels',rels)
            z.writestr('xl/worksheets/sheet1.xml',ws)
        good=scan(p)
        assert good['formula_count']==1 and not good['approved_original_authenticated']
        assert good['sheet_cells'][0]['cells'][1]['formula']=='A1*4'
        assert good['sheets_declared'][0]['worksheet_part']=='xl/worksheets/sheet1.xml'
        assert good['declared_sheet_links_resolved']
        # A shared-formula continuation has an f tag but no formula text.
        shared_ws=ws.replace('</row>', '<c r="C1"><f t="shared" si="1"/><v>300</v></c></row>')
        with ZipFile(p,'w',compression=ZIP_DEFLATED) as z:
            z.writestr('[Content_Types].xml','<Types/>')
            z.writestr('xl/workbook.xml',wb)
            z.writestr('xl/_rels/workbook.xml.rels',rels)
            z.writestr('xl/worksheets/sheet1.xml',shared_ws)
        shared=scan(p)
        assert shared['formula_count']==2
        assert shared['sheet_cells'][0]['cells'][2]['formula_attributes']=={'t':'shared','si':'1'}
        # Missing relationship mapping must fail closed.
        bad_wb=wb.replace('r:id="rId5"','r:id="rId999"')
        with ZipFile(p,'w',compression=ZIP_DEFLATED) as z:
            z.writestr('[Content_Types].xml','<Types/>')
            z.writestr('xl/workbook.xml',bad_wb)
            z.writestr('xl/_rels/workbook.xml.rels',rels)
            z.writestr('xl/worksheets/sheet1.xml',ws)
        try:
            scan(p)
            raise AssertionError('missing sheet relationship accepted')
        except ValueError as exc:
            assert 'Unresolved' in str(exc)
        # Restore a valid package and test macro/external-part flagging.
        with ZipFile(p,'w',compression=ZIP_DEFLATED) as z:
            z.writestr('[Content_Types].xml','<Types/>')
            z.writestr('xl/workbook.xml',wb)
            z.writestr('xl/_rels/workbook.xml.rels',rels)
            z.writestr('xl/worksheets/sheet1.xml',ws)
        with ZipFile(p,'a') as z:
            z.writestr('xl/vbaProject.bin',b'FAKE-VBA-NOT-EXECUTED')
            z.writestr('xl/externalLinks/externalLink1.xml',b'<externalLink/>')
        flagged=scan(p)
        assert flagged['vba_present'] and flagged['external_links_present']
        p.write_bytes(b'NOT-A-ZIP')
        try:scan(p);raise AssertionError('malformed input accepted')
        except BadZipFile:pass
        p.write_bytes(b'')
        try:scan(p);raise AssertionError('empty input accepted')
        except ValueError as e:assert 'Empty' in str(e)
    return {'tests':6,'passed':6,'synthetic_fixtures_only':True,
            'accepted_OAG_workbook_obtained':False}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',type=Path)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--self-test',action='store_true')
    args=ap.parse_args()
    result=selftest() if args.self_test else scan(args.input) if args.input else ap.error('Need --input or --self-test')
    data=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(data,encoding='utf-8')
    print(data,end='')

if __name__=='__main__':main()
