"""Prepare dated GFZ forcing and original EISCAT row coordinates for MSIS.
No atmospheric defaults; --self-test uses artificial indices only.
"""
import datetime as dt
import hashlib
import json
import sys
from pathlib import Path
import numpy as np
import h5py
from pyproj import Transformer

DAY=dt.timedelta(days=1)
EVENT=dt.date(2017,12,18)

def parse_gfz(lines):
    rows={}
    for line in lines:
        if not line.strip() or line.lstrip().startswith('#'): continue
        p=line.split()
        if len(p)!=28: raise ValueError('unexpected GFZ daily column count')
        day=dt.date(*map(int,p[:3]))
        if day in rows: raise ValueError('duplicate GFZ day')
        if int(p[3])!=(day-dt.date(1932,1,1)).days: raise ValueError('date index mismatch')
        rows[day]=(tuple(map(int,p[15:23])),int(p[23]),float(p[25]),int(p[27]))
    return rows

def forcing(rows, when):
    if when.utcoffset()!=dt.timedelta(0): raise ValueError('UTC required')
    day=when.date(); slot=when.hour//3
    def get(d):
        a,ap,f,flag=rows[d]
        if flag not in (1,2): raise ValueError('nondefinitive Kp')
        return a,ap,f
    fs=[get(day+i*DAY)[2] for i in range(-40,41)]
    if not all(np.isfinite(f) and f>0 for f in fs): raise ValueError('missing observed solar flux')
    def past(k):
        d,h=divmod(slot-k,8); a=get(day+d*DAY)[0][h]
        if not 0<=a<=400: raise ValueError('missing ap')
        return a
    a=[past(k) for k in range(20)]; ap=get(day)[1]
    if not 0<=ap<=400: raise ValueError('missing daily Ap')
    return dict(f107a=float(np.mean(fs)),f107=get(day-DAY)[2],ap=ap,
                ap_a=[ap,*a[:4],sum(a[4:12])/8,sum(a[12:20])/8])

def radar(root):
    p=Path(root)/'MAD6400_2017-12-18_bella_60@vhf.hdf5'
    digest=hashlib.sha256(p.read_bytes()).hexdigest()
    if digest!='d62180251bf74884910831c522ada43d9bec084d3f9ca6323f67c575ee05708d': raise ValueError('radar digest mismatch')
    with h5py.File(p) as f: a=f['Data/Table Layout'][:]
    start=dt.datetime(2017,12,18,2,30,tzinfo=dt.timezone.utc).timestamp()
    keep=(a['ut1_unix']<start+12600)&(a['ut2_unix']>start)&(a['gfit']==0)&(a['ne']>0)&(a['dne']/a['ne']<.5)&(a['chisq']<10)&(a['ti']>50)&((a['gdalt']>=95)|(a['ne']<1e12))
    a=a[keep&(a['gdalt']>=80)&(a['gdalt']<200)]; assert len(a)==3087
    # Preserve previous rounded-site straight ray, not exact GUISDAP geolocation.
    lat,lon=np.deg2rad([69.6,19.2]); f=Transformer.from_crs(4979,4978,always_xy=True); inv=Transformer.from_crs(4978,4979,always_xy=True)
    site=np.array(f.transform(19.2,69.6,30.)); E=np.array([-np.sin(lon),np.cos(lon),0]); N=np.array([-np.sin(lat)*np.cos(lon),-np.sin(lat)*np.sin(lon),np.cos(lat)]); U=np.array([np.cos(lat)*np.cos(lon),np.cos(lat)*np.sin(lon),np.sin(lat)])
    az,el=np.deg2rad(a['azm']),np.deg2rad(a['elm']); r=np.cos(el)[:,None]*(np.sin(az)[:,None]*E+np.cos(az)[:,None]*N)+np.sin(el)[:,None]*U
    glon,glat,alt=inv.transform(*(site+1000*a['range'][:,None]*r).T)
    out=[]
    for x,la,lo,h in zip(a,glat,glon,alt):
        t=dt.datetime.fromtimestamp((x['ut1_unix']+x['ut2_unix'])/2,dt.timezone.utc)
        out.append(dict(record=int(x['recno']),range_km=float(x['range']),utc=t.isoformat(),lat=float(la),lon=float(lo),height_km=float(h/1000),original_gdalt_km=float(x['gdalt']),ne=float(x['ne']),ti=float(x['ti']),te=float(x['ti']*x['tr'])))
    assert len({(x['record'],x['range_km']) for x in out})==len(out)
    return out

def self_test():
    rows={}
    for i in range(-40,41):
        d=EVENT+i*DAY; rows[d]=(tuple(range(8)),4,100+i,2)
    # Deliberately distinguish the previous and current day and midnight slots.
    rows[EVENT-DAY]=(tuple(range(10,18)),14,99,2)
    t=dt.datetime(2017,12,18,2,59,tzinfo=dt.timezone.utc)
    a=forcing(rows,t); b=forcing(rows,t+dt.timedelta(minutes=1))
    assert a['f107a']==100 and a['f107']==99
    assert a['ap_a'][:5]==[4,0,17,16,15] and b['ap_a'][:5]==[4,1,0,17,16]
    assert a['ap_a'][5:]==[sum([14,13,12,11,10,7,6,5])/8,sum([4,3,2,1,0,7,6,5])/8]
    d=EVENT; line=' '.join(map(str,[d.year,d.month,d.day,(d-dt.date(1932,1,1)).days,0,0,0,*([0]*8),*range(8),4,0,100,99,2]))
    assert parse_gfz([line])[d]==rows[d]
    for bad in ([line,line], [line.rsplit(' ',1)[0]]):
        try: parse_gfz(bad)
        except ValueError: pass
        else: raise AssertionError('bad GFZ accepted')
    rows[EVENT+DAY]=(tuple(range(8)),4,-1,2)
    try: forcing(rows,t)
    except ValueError: pass
    else: raise AssertionError('missing flux accepted')

if __name__=='__main__':
    self_test(); root=sys.argv[1]; out=radar(root)
    times=sorted({x['utc'] for x in out}); bins={t[:13] for t in times}
    receipt=dict(status='RADAR_MODEL_INPUT_GEOMETRY_ONLY',rows=len(out),records=len(times),midpoint_first=times[0],midpoint_last=times[-1],hour_bins=sorted(bins),height_difference_m=[float(x) for x in np.quantile([1000*(r['height_km']-r['original_gdalt_km']) for r in out],[0,.5,1])],synthetic_gfz_tests='PASS',physical_admission=False)
    if len(sys.argv)>2:
        p=Path(sys.argv[2]); rows=parse_gfz(p.read_text().splitlines()); forc={t:forcing(rows,dt.datetime.fromisoformat(t)) for t in times}
        receipt.update(status='RADAR_AND_GFZ_INPUTS_ONLY',gfz_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),forcing_by_utc=forc)
        # A prepared packet is not a model evaluation.
        if len(sys.argv)>3:
            Path(sys.argv[3]).write_text(json.dumps([dict(r,**forc[r['utc']]) for r in out],indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
