"""Replay original IRI-2016 on radar geometry, preserving unavailable ion channels."""
import datetime as dt
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import tarfile
import tempfile
import numpy as np
from solar_earth_model_inputs import radar

DRIVER='''program replay
implicit none
logical jf(50)
real outf(20,1000),oarr(100),lat,lon,h,ut
integer id,ios
call read_ig_rz
call readapf107
do
 read(*,*,iostat=ios) id,lat,lon,h,ut
 if(ios/=0) exit
 jf=.true.
 jf([4,5,6,12,21,22,23,28,29,30,33,35,39,40,47])=.false.
 oarr=-1.
 call iri_sub(jf,0,lat,lon,2017,1218,ut+25.,h,h,1.,outf,oarr)
 write(*,'(A,I6,11ES19.10)') 'ROW ',id,outf(1:11,1)
enddo
end program
'''

def bounded_index(text):
    update,period,ig,rz=re.split(r'\n\s*\n',text.strip())
    fields=lambda x:[v.strip() for v in x.split(',') if v.strip()]
    start,year,end,last=map(int,fields(period)); a,b=fields(ig),fields(rz)
    assert len(a)==len(b)==3-start+(last-year)*12+end
    assert (year,start)<(2017,12)<(2019,12)<=(last,end)
    count=3-start+(2019-year)*12+12
    assert count<=806 and len(a)>806
    return update+'\n\n'+f'{start},{year},12,2019,\n\n'+','.join(a[:count])+',\n\n'+','.join(b[:count])+',\n',len(a),count

def main(root):
    rows=radar(root); manifest=json.loads((root/'source_manifest.json').read_text()); hashes={x['local_file']:x['sha256'] for x in manifest['sources']}
    for name in ('00_iri.tar','00_ccir-ursi.tar','ig_rz.dat','apf107.dat'):
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==hashes[name]
    text,original,kept=bounded_index((root/'ig_rz.dat').read_text())
    assert len((root/'apf107.dat').read_text().splitlines())<27000
    with tempfile.TemporaryDirectory() as tmp:
        p=pathlib.Path(tmp)
        for name in ('00_iri.tar','00_ccir-ursi.tar'):
            with tarfile.open(root/name) as ar:
                for x in ar.getmembers():
                    assert x.isfile() and pathlib.PurePosixPath(x.name).name==x.name
                    (p/x.name).write_bytes(ar.extractfile(x).read())
        (p/'ig_rz.dat').write_text(text); (p/'apf107.dat').write_bytes((root/'apf107.dat').read_bytes()); (p/'driver.f90').write_text(DRIVER)
        args=['gfortran','-std=legacy','-fallow-argument-mismatch','-O0','-o','replay','driver.f90','irisub.for','irifun.for','iritec.for','iridreg.for','igrf.for','cira.for','iriflip.for']
        compile=subprocess.run(args,cwd=p,check=True,capture_output=True,text=True)
        def call(ids):
            lines=[]
            for i in ids:
                r=rows[i]; t=dt.datetime.fromisoformat(r['utc']); assert t.date()==dt.date(2017,12,18)
                ut=t.hour+t.minute/60+t.second/3600+t.microsecond/3.6e9
                lines.append(f"{i} {r['lat']} {r['lon']} {r['height_km']} {ut}\n")
            result=subprocess.run([str(p/'replay')],cwd=p,input=''.join(lines),check=True,capture_output=True,text=True,timeout=90)
            x=np.array([[float(v) for v in line.split()[1:]] for line in result.stdout.splitlines() if line.startswith('ROW ')])
            assert x.shape==(len(ids),12) and np.array_equal(x[:,0],ids) and np.all(np.isfinite(x))
            return x[:,1:]
        v=call(list(range(len(rows)))); first=call(list(range(10))); reverse=call(list(range(9,-1,-1)))[::-1]
    assert np.array_equal(first,v[:10]); assert np.all(v[:,:4]>0)
    # The cluster channel is an unavailable percentage sentinel scaled by Ne/100.
    assert np.allclose(v[:,9],-v[:,0]/100,rtol=1e-7,atol=0)
    valid=[4,5,6,7,8,10]; assert np.all(v[:,valid]>=0)
    q=lambda x:np.quantile(x,[0,.5,1]).tolist(); s=v[:,valid].sum(axis=1)/v[:,0]
    result=dict(status='SOURCE_BACKED_IRI_MODEL_WITH_UNAVAILABLE_CLUSTER_CHANNEL',rows=len(rows),original_index_values=original,retained_index_values=kept,bounded_index_sha256=hashlib.sha256(text.encode()).hexdigest(),compiler_warning_count=compile.stderr.count('Warning:'),cluster_unavailable_rows=int(np.sum(v[:,9]<0)),positive_model_density_rows=int(np.sum(v[:,0]>0)),available_ion_sum_over_model_ne=q(s),iri_ne_over_observed_ne=q(v[:,0]/np.array([r['ne'] for r in rows])),iri_Oplus_fraction=q(v[:,4]/v[:,0]),first10_fresh_exact_match=True,first10_reverse_max_relative_difference=float(np.max(np.abs(first-reverse)/np.maximum(np.abs(first),1e-30))),physical_admission=False)
    print(json.dumps(result,indent=2))
if __name__=='__main__': main(pathlib.Path(sys.argv[1]))
