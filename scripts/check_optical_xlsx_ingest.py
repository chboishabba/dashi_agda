"""Inspect XLSX source sheets; extract explicitly mapped, provenance-gated traces.
Caller manifests are not independent authentication of published measurements.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import tempfile
from xml.etree import ElementTree as ET
from zipfile import ZipFile

M='{http://schemas.openxmlformats.org/spreadsheetml/2006/main}'
R='{http://schemas.openxmlformats.org/officeDocument/2006/relationships}'
P='{http://schemas.openxmlformats.org/package/2006/relationships}'
DOI='10.6084/m9.figshare.21968435'

def col(ref):
    match=re.fullmatch(r'([A-Z]+)[0-9]+',ref)
    assert match, 'bad cell address'
    n=0
    for c in match[1]: n=n*26+ord(c)-64
    return n-1

def sheets(path):
    with ZipFile(path) as z:
        wb=ET.fromstring(z.read('xl/workbook.xml'))
        rels={r.get('Id'):r.get('Target') for r in ET.fromstring(z.read('xl/_rels/workbook.xml.rels')).findall(P+'Relationship')}
        shared=[]
        if 'xl/sharedStrings.xml' in z.namelist():
            shared=[''.join(t.text or '' for t in si.iter(M+'t')) for si in ET.fromstring(z.read('xl/sharedStrings.xml')).findall(M+'si')]
        result={}
        for item in wb.find(M+'sheets'):
            target=rels[item.get(R+'id')].lstrip('/')
            if not target.startswith('xl/'):target='xl/'+target
            assert '..' not in target.split('/'),'unsafe sheet path'
            root=ET.fromstring(z.read(target));rows={}
            data=root.find(M+'sheetData')
            for row in ([] if data is None else data):
                values={}
                for cell in row.findall(M+'c'):
                    i=col(cell.get('r'));v=cell.find(M+'v');typ=cell.get('t')
                    if typ=='inlineStr':values[i]=''.join(t.text or '' for t in cell.iter(M+'t'))
                    elif v is not None:
                        assert typ!='e','error-valued cell'
                        values[i]=shared[int(v.text)] if typ=='s' else (v.text if typ=='str' else float(v.text))
                    elif cell.find(M+'f') is not None:raise ValueError('formula lacks cached value')
                rows[int(row.get('r'))]=values
            result[item.get('name')]=rows
    return result

def inspect(path):
    return {name:[{'row':i,'cells':{str(k+1):v for k,v in sorted(rows[i].items())}} for i in sorted(rows)[:4]] for name,rows in sheets(path).items()}

def ingest(path,manifest_path,require_measured=True,return_pairs=False):
    raw=Path(path).read_bytes();m=json.loads(Path(manifest_path).read_text())
    assert m.get('sha256')==hashlib.sha256(raw).hexdigest(),'hash mismatch'
    assert m.get('source_reference') and m.get('frequency_unit') and m.get('intensity_unit'),'provenance/units missing'
    assert m.get('source_kind') in ('measured','synthetic','modelled')
    assert m.get('trace_kind') in ('raw','smoothed','modelled')
    if require_measured:
        assert m['source_kind']=='measured' and m['trace_kind']=='raw' and DOI in m['source_reference'],'not identified as 2023 raw measurement'
    name=m.get('worksheet');first=m.get('first_data_row');fc=m.get('frequency_column');ic=m.get('intensity_column')
    assert isinstance(name,str) and isinstance(first,int) and first>0
    assert isinstance(fc,int) and isinstance(ic,int) and fc>0 and ic>0 and fc!=ic
    all_sheets=sheets(path);assert name in all_sheets,'missing selected worksheet'
    pairs=[]
    for rowno,row in sorted(all_sheets[name].items()):
        if rowno<first:continue
        x,y=row.get(fc-1),row.get(ic-1)
        if x is None and y is None:continue
        assert type(x)==float and type(y)==float and math.isfinite(x) and math.isfinite(y) and y>=0,('invalid data',rowno)
        pairs.append((x,y))
    assert len(pairs)>1 and all(pairs[i][0]<pairs[i+1][0] for i in range(len(pairs)-1)),'missing or unsorted trace'
    result={'rows':len(pairs),'frequency_min':pairs[0][0],'frequency_max':pairs[-1][0],
            'sha256':m['sha256'],'trace_kind':m['trace_kind'],
            'source_kind':m['source_kind'],'frequency_unit':m['frequency_unit'],
            'intensity_unit':m['intensity_unit'], 'publication_authenticated':False}
    if return_pairs: result['pairs']=pairs
    return result

def test(path):
    count=0
    with tempfile.TemporaryDirectory() as d:
        f=Path(d)/'manifest.json'
        m=dict(sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest(),source_reference='synthetic fixture',
               source_kind='synthetic',trace_kind='raw',frequency_unit='arbitrary',intensity_unit='arbitrary',
               worksheet='Synthetic Raw',first_data_row=2,frequency_column=1,intensity_column=2)
        def put(obj):f.write_text(json.dumps(obj))
        put(m);assert ingest(path,f,False)['rows']==3;count+=1
        for changed in ({},{'worksheet':'missing'},{'sha256':'0'*64},{'intensity_column':1}):
            put({**m,**changed})
            try:ingest(path,f,True if not changed else False)
            except AssertionError:count+=1
            else:raise AssertionError('invalid source accepted')
        assert set(inspect(path))=={'Synthetic Raw','Modelled Curve'};count+=1
    print(f'{count}/{count} PASS XLSX fail-closed controls')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('xlsx');parser.add_argument('manifest',nargs='?')
    parser.add_argument('--inspect',action='store_true');parser.add_argument('--test',action='store_true');a=parser.parse_args()
    if a.test:test(a.xlsx)
    elif a.inspect:print(json.dumps(inspect(a.xlsx),indent=2))
    elif a.manifest:print(json.dumps(ingest(a.xlsx,a.manifest),indent=2))
    else:parser.error('supply manifest, --inspect or --test')
