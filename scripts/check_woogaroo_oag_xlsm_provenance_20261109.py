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

M='{http://schemas.openxmlformats.org/spreadsheetml/2006/main}'
R='{http://schemas.openxmlformats.org/officeDocument/2006/relationships}'
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
                                  'cached_value':v.text if v is not None else None})
            extracted.append({'part':name,'cells':cells})
        return {'case':'EPBC 2019/8575','status':'UNVERIFIED_WORKBOOK_CANDIDATE',
                'sha256':h.hexdigest(),'bytes':size,'sheets_declared':sheets,
                'sheet_cells':extracted,
                'formula_count':sum(sum(c['formula'] is not None for c in s['cells'])
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
        ws='<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><sheetData><row r="1"><c r="A1"><v>75</v></c><c r="B1"><f>A1*4</f><v>300</v></c></row></sheetData></worksheet>'
        with ZipFile(p,'w',compression=ZIP_DEFLATED) as z:
            z.writestr('[Content_Types].xml','<Types/>')
            z.writestr('xl/workbook.xml',wb)
            z.writestr('xl/worksheets/sheet1.xml',ws)
        good=scan(p)
        assert good['formula_count']==1 and not good['approved_original_authenticated']
        assert good['sheet_cells'][0]['cells'][1]['formula']=='A1*4'
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
    return {'tests':4,'passed':4,'synthetic_fixtures_only':True,
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
