"""Original 2017-12-18 VHF source audit; not calibrated conductivity or flux.
Usage: python check_solar_earth_eiscat_replay.py /path/to/original/files
"""
import hashlib,json,sys
from pathlib import Path
from datetime import datetime,timezone
import h5py,numpy as np
root=Path(sys.argv[1]); start=datetime(2017,12,18,2,30,tzinfo=timezone.utc).timestamp(); stop=start+12600
hashes={6400:'d62180251bf74884910831c522ada43d9bec084d3f9ca6323f67c575ee05708d',6300:'a6a52500c3937f9beed9aa5ce941c45d08fae652fbef3174cf964a1c45b95b25',6301:'eed18b6fd8f54b780446a370a6373fbbb250db5278b43cb67e7f1fab90090eb8',6302:'344c31d5db5d661d59ec2deb4a0d6867773c1dc064bb3dc236aaf3e2f50ae5ad'}
A={}; records={}; inventory={}
for k,h in hashes.items():
    p=root/f'MAD{k}_2017-12-18_bella_60@vhf.hdf5'; assert hashlib.sha256(p.read_bytes()).hexdigest()==h
    with h5py.File(p) as f:
        a=f['Data/Table Layout'][:]
        assert set(a['kindat'])=={k} and set(a['kinst'])=={74}
        meta={row[0].decode():row[3].decode() for row in f['Metadata/Data Parameters'][:]}
        assert meta['RANGE']=='km'
        if k==6400: assert meta['NE']=='m-3' and meta['GDALT']=='km' and meta['CO']=='s-1'
        else: assert meta['POP']=='m-3' and meta['RGATE']=='km'
    b=a[(a['ut1_unix']<stop)&(a['ut2_unix']>start)]; A[k]=b
    records[k]=[b[b['recno']==i] for i in np.unique(b['recno'])]
    for r in records[k]:
        assert all(np.isfinite(r[n]).all() for n in r.dtype.names)
        assert all(np.all(r[n]==r[n][0]) for n in ('ut1_unix','ut2_unix','azm','elm'))
        assert np.all(np.diff(r['range'])>0) and r['ut2_unix'][0]>=r['ut1_unix'][0]
    inventory[k]=dict(sha256=h,rows=len(a),context_rows=len(b),records=len(records[k]))
assert len(A[6302])==0
# Explicit published 2025 empirical-conductance study screen, not a replay of 2024 paper's screen.
def good(a):
    return (a['gfit']==0)&(a['ne']>0)&(a['dne']/a['ne']<.5)&(a['chisq']<10)&(a['ti']>50)&((a['gdalt']>=95)|(a['ne']<1e12))
a=A[6400]; g=good(a); t=(a['ut1_unix']+a['ut2_unix'])/2-start
windows=[(0,2700),(2700,10800),(10800,12600)]
bands=[]
for lo,hi in [(80,100),(100,120),(120,150),(150,180),(180,200)]:
    band=[]
    for x,y in windows:
        b=a[g&(a['gdalt']>=lo)&(a['gdalt']<hi)&(t>=x)&(t<y)]
        band.append(dict(rows=len(b),median_ne=float(np.median(b['ne'])),median_co=float(np.median(b['co'])),median_te=float(np.median(b['ti']*b['tr']))))
    bands.append(dict(alt_km=[lo,hi],windows=band))
comp={}; base=records[6400]; times=lambda r:np.array([[x['ut1_unix'][0],x['ut2_unix'][0]] for x in r])
for k in (6300,6301):
    r=records[k]; assert len(r)==len(base)==208
    assert all(x['recno'][0]==y['recno'][0] and x['azm'][0]==y['azm'][0] and x['elm'][0]==y['elm'][0] for x,y in zip(base,r))
    dt=float(np.max(abs(times(r)-times(base))));assert dt<1
    v=[];p=[];dist=[]
    for x,y in zip(base,r):
        f=x[good(x)&(x['gdalt']>=80)&(x['gdalt']<200)]; ix=np.argmin(abs(f['range'][:,None]-y['range'][None,:]),axis=1); z=y[ix]
        v.extend(f['ne']);p.extend(z['pop']);dist.extend(abs(f['range']-z['range']))
    v=np.array(v);p=np.array(p)
    comp[k]=dict(max_clock_difference_s=dt,pairs=len(v),max_range_center_distance_km=float(max(dist)),negative_pop=int(sum(p<0)),pop_to_ne_quartiles=np.percentile(p/v,[25,50,75]).tolist(),pearson=float(np.corrcoef(p,v)[0,1]),rgate_km_minmax=[float(A[k]['rgate'].min()),float(A[k]['rgate'].max())])
T=times(base); gaps=T[1:,0]-T[:-1,1]; assert np.all(gaps>=0)
print(json.dumps(dict(status='ORIGINAL_RADAR_REPLAY_OBSERVATION_ONLY',inventory=inventory,quality_pass=int(g.sum()),gfit_counts={int(k):int(v) for k,v in zip(*np.unique(a['gfit'],return_counts=True))},collision_floor_count=int(sum(a['co']==1)),zero_uncertainty={k:int(sum(a[k]==0)) for k in ['dco','dpm','dpo+']},max_composition_sum_error=float(max(abs(a['pm']+a['po+']-1))),gap_count=int(sum(gaps>0)),max_gap_s=float(max(gaps)),total_coverage_s=float(np.sum(T[:,1]-T[:,0])),beam_deg=[float(a['azm'][0]),float(a['elm'][0])],bands=bands,comparisons=comp,physical_conductivity_admission=False,basal_flux_admission=False),indent=2))
