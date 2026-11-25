"""Original Lin Figure 1 spatial carriers and flux-tube projection audit.
Usage: python check.py /path/to/source/files
No geographic site, propagation or atmospheric control design.
"""
import hashlib,json,sys
from pathlib import Path
import numpy as np
import sympy as s
import xarray as xr
root=Path(sys.argv[1])
hashes={'PF_fig_PF.nc':'8ff495be1ebdd6609813061880b8faf08ac8365540e8ac2d2d64961c9b3b6880','Lin25_PF_fig_PF.m':'03c65aac070842225bf705a82f6b7a82649f9a11f409ee1769166a655bd7e1aa'}
for file,h in hashes.items():assert hashlib.sha256((root/file).read_bytes()).hexdigest()==h
m=(root/'Lin25_PF_fig_PF.m').read_text()
for token in ['[~,ieq_flt] = min(abs(mlat_flt))','req_flt = r_flt(ieq_flt)','th0 = MLTi*15-180','lat0 = 0','r0s = req_flt','pcolor(tplt,dsfl,keo_plts{ikeo})']:assert token in m
# Published mapping law S_parallel/B constant, with magnetic flux conservation.
b1,b2,A1,c=s.symbols('b1 b2 A1 c',positive=True)
A2=b1*A1/b2
assert s.simplify(c*b1*A1-c*b2*A2)==0
# Oriented surface: signed area projection, not scalar field magnitude.
a,n1,n2=s.symbols('a n1 n2',real=True,nonzero=True)
assert s.simplify(c*b1*a*n1-c*b2*(b1*a*n1/(b2*n2))*n2)==0
# Arc length alone is not a spatial embedding. Two distinct curves with
# identical unit speed and a common origin, one curved, one straight.
t=s.symbols('t',real=True);p=s.Matrix([t,0,0]);q=s.Matrix([s.sin(t),1-s.cos(t),0])
assert p.subs(t,0)==q.subs(t,0) and p.diff(t).dot(p.diff(t))==1 and s.trigsimp(q.diff(t).dot(q.diff(t)))==1 and p!=q
# Read the exact figure data; source plots use MATLAB transposed dimensions.
with xr.open_dataset(root/'PF_fig_PF.nc',decode_cf=False) as D:
    p=D.fltraces.values.T;d=D.dsfl.values.ravel();eq=D.xyzeq_peak.values.ravel()
    mlt=float(D.MLTi.item());i=int(np.argmin(abs(p[:,2]/np.linalg.norm(p,axis=1))))
    req=float(np.linalg.norm(p[i]));theta=np.deg2rad(mlt*15-180);seed=req*np.array([np.cos(theta),np.sin(theta),0.])
    assert np.array_equal(p[i],eq)
    assert p.shape==(609,3) and D.emrd_plts.shape==D.bphi_plts.shape==(61,615) and d.shape==(615,)
    assert np.all(np.diff(d)>0) and np.count_nonzero(d==0)==1
    peak=np.unravel_index(np.argmax(D.S_par_plt.values),D.S_par_plt.shape);xy=np.array([D.xiplt.values[peak],D.yiplt.values[peak]])
    # Azimuth agreement is not a radial projection law.
    azerror=float(abs(np.arctan2(xy[1],xy[0])-np.arctan2(p[0,1],p[0,0])))
    assert azerror<1e-12
    matched=[];maxxy=0.
    for k in range(1,157):
        tag=f'{k:06d}';q=D['fltcols_'+tag].values.T
        rxy=D['fltrxys_'+tag].values.ravel();a=D['spacols_'+tag].values.ravel();b=D['bpscols_'+tag].values.ravel()
        assert len(q)==len(rxy)==len(a)==len(b)
        maxxy=max(maxxy,float(np.max(abs(np.linalg.norm(q[:,:2],axis=1)-rxy))))
        if len(q)==len(d):matched.append((k,q.copy()))
    assert len(matched)==1 and matched[0][0]==58 and maxxy<1e-12
q=matched[0][1];j=int(np.argmin(abs(q[:,2]/np.linalg.norm(q,axis=1))))
assert d[j]==0 and q[j,2]==0
# If dsfl is cumulative arclength, any chord between consecutive samples
# on the SAME embedding is <= its corresponding increment. Test both orders.
checks=[]
for label,Q in [('stored',q),('reversed',q[::-1])]:
    chord=np.linalg.norm(np.diff(Q,axis=0),axis=1);gap=chord-np.diff(d)
    arc=np.r_[0,np.cumsum(chord)];arc-=arc[j]
    checks.append(dict(order=label,chord_excess_count=int(sum(gap>1e-9)),max_chord_excess_RE=float(max(gap)),max_centered_polyline_difference_RE=float(max(abs(arc-d)))))
    assert max(gap)>1e-3
arc=np.r_[0,np.cumsum(np.linalg.norm(np.diff(p,axis=0),axis=1))]
print(json.dumps(dict(status='ORIGINAL_COORDINATE_AUDIT_AND_CONDITIONAL_FLUX_MAPPING',hashes=hashes,peak_trace_points=len(p),keogram_points=len(d),sampled_grid_lines=156,unique_count_match=58,peak_index_0based=i,keogram_zero_0based=int(np.argmin(abs(d))),peak_equatorial_point_RE=p[i].tolist(),peak_equatorial_radius_RE=req,plot_seed_RE=seed.tolist(),plot_seed_displacement_RE=float(np.linalg.norm(seed-p[i])),grid58_seed_RE=q[j].tolist(),grid58_radius_difference_RE=float(np.linalg.norm(q[j])-req),peak_map_azimuth_difference_rad=azerror,peak_polyline_lengths_RE=[float(arc[i]),float(arc[-1]-arc[i])],keogram_signed_endpoints_RE=[float(d[0]),float(d[-1])],max_grid_xy_error_RE=maxxy,conditional_chord_checks=checks,physical_admission=False),indent=2))
