"""Lower boundary signed work and original Lin FAC/potential diagnostic audit.
Usage: python check.py /path/to/source/files
No physical ground transmission or actuation model.
"""
import hashlib,json,sys
from pathlib import Path
import sympy as s
import numpy as np
import xarray as xr
root=Path(sys.argv[1]); hashes={'PF_fig_JH.nc':'2213a4fbcf2f3f7354dd16b53699decbcca5d4043b3ec71f73d2ae8fb9528255','Lin25_PF_fig_JH.m':'cd9193d648601c69f85c31e185214555df690ef5c8ee2ae72ff1321344a8d552'}
for name,h in hashes.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h
m=(root/'Lin25_PF_fig_JH.m').read_text();assert 'Average DC Poynting Flux' in m and 'Average FAC/Convection' in m and 'varplts = {avg_joun, avg_facn}' in m
# Thin stationary sheet, normal from upper (1) to lower (2), RMS phasors.
J=s.Matrix([[0,-1],[1,0]]);I=s.eye(2)
E=s.Matrix(s.symbols('E:2',real=True));w=s.Matrix(s.symbols('w:2',real=True));g=s.Matrix(s.symbols('g:2',real=True));h2=s.Matrix(s.symbols('h:2',real=True))
p,h=s.symbols('p h',real=True,nonnegative=True);Ep=E+w;K=(p*I+h*J)*Ep;h1=h2+K+g
H1=J*h1;H2=J*h2
assert J*(H2-H1)==K+g
assert s.expand(E.dot(h1-h2)-p*Ep.dot(Ep)+w.dot(K)-E.dot(g))==0
assert (Ep.T*J*Ep)[0].expand()==0
# Quasistatic sheet incidence: divergence-free cycle is invisible to FAC.
D=s.Matrix([[-1,0,1],[1,-1,0],[0,1,-1]]);phi=s.Matrix(s.symbols('v:3'));e=-D.T*phi;k=s.Matrix(s.symbols('k:3'));cycle=s.ones(3,1)
assert D*cycle==s.zeros(3,1) and D.rank()==2
assert s.expand(e.dot(k)+phi.dot(D*k))==0
assert e.dot(cycle).expand()==0
assert (D*(k+cycle))==D*k
assert (e.dot(k+cycle)-e.dot(k)).expand()==0
# Same upstream net power; separate nonnegative destinations, restored storage.
# In this restricted source-free downstream budget any allocation is allowed
# by conservation alone, not necessarily physically attainable.
for q,b,side in [(1,0,0),(0,1,0),(0,0,1),(s.Rational(1,3),s.Rational(1,3),s.Rational(1,3))]:assert q+b+side==1
with xr.open_dataset(root/'PF_fig_JH.nc',decode_cf=False) as ds:
    a=ds.PF_Tpd.values.ravel();d=ds.JH_Tpd.values.ravel();fac=ds.avg_facn.values;pot=ds.potn_avg.values;dc=ds.avg_joun.values
    assert fac.shape==pot.shape==dc.shape==(45,361)
    for key in ('xi','yi','avg_facn','potn_avg','avg_joun'):
        z=ds[key].values;assert np.array_equal(z[:,0],z[:,-1],equal_nan=True)
    # Duplicated plotting seam removed for diagnostic sample means ONLY.
    f=fac[:,:-1];v=pot[:,:-1];assert np.isfinite(f).all() and np.isfinite(v).all()
    # Units: kV*uA/m^2=mW/m^2. No area weights, FAC sign or radial projection assigned.
    means=[float(np.mean(f*v)),float(np.mean(f*(v+1)))];delta=float(np.mean(f))
    assert abs(means[1]-means[0]-delta)<1e-14
    totals=a+d;assert int(np.argmax(totals))==3
    out=dict(status='LOWER_BOUNDARY_CONDITIONAL_LEDGER_AND_ORIGINAL_DIAGNOSTICS',hashes=hashes,unique_plot_samples=int(f.size),duplicate_seam_samples=45,dc_missing_full=int(np.sum(~np.isfinite(dc))),fac_range_uA_m2=[float(f.min()),float(f.max())],potential_range_kV=[float(v.min()),float(v.max())],unweighted_fac_mean_uA_m2=delta,unweighted_product_mean_mW_m2=means[0],unweighted_product_mean_shifted_1kV_mW_m2=means[1],source_cases=[dict(period_s=t,upstream_net_GW=float(p),conditional_passive_no_other_input_lower_exit_interval_GW=[0,float(p)]) for t,p in zip([50,100,200,300,500,1000,None],totals)],physical_admission=False)
print(json.dumps(out,indent=2))
