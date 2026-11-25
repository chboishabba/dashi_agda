"""Source-relative covariance fibre repair using the original EDI tensors.
Conditional local signed flux, not a solar source attribution or control model.
Usage: python check_solar_earth_covariance_repair.py /path/to/edi.zip
"""
import sys,hashlib,json,re,zipfile
from pathlib import Path
import numpy as np
import sympy as s
p=Path(sys.argv[1]);sha=hashlib.sha256(p.read_bytes()).hexdigest()
assert sha=='26020ec6a1db00359a8703fad30219e6e2e9b20e8b87e968633576525b4fab49'
# Hermitian covariance in real coordinates, with diagonal observer.
a,b,u,v,d,e,x,y=s.symbols('a b u v d e x y',real=True)
Q=s.Matrix([[d,x+s.I*y],[x-s.I*y,e]]);C=s.Matrix([[a,u+s.I*v],[u-s.I*v,b]])
assert s.expand(s.trace(Q*C))==a*d+b*e+2*(u*x+v*y)
assert s.expand(C.det())==a*b-u*u-v*v
# Same autospectra, opposite signed contrast; imaginary coherence is independent.
for q,cs in [(s.Matrix([[0,1],[1,0]]),[1,-1]),(s.Matrix([[0,s.I],[-s.I,0]]),[s.I,-s.I])]:
    vals=[]
    for z in cs:
        c=s.Matrix([[1,z],[s.conjugate(z),1]])/2
        assert c.det()==0 and c.trace()==1;vals.append(s.trace(q*c))
    assert vals==[1,-1]
# All allowed real-linear scalar covariance measurements: rank increment is
# minimal additional count, provided measurements can realize the row span.
M=s.Matrix([[1,0,0,0],[0,1,0,0]]);N=s.Matrix([[2,3,4,6],[5,7,8,12]])
assert M.col_join(N).rank()-M.rank()==1
R=M.col_join(s.Matrix([[0,0,2,3]]))
assert N==N*R.pinv()*R
N2=N.col_join(s.Matrix([[0,0,1,0]]))
assert M.col_join(N2).rank()-M.rank()==2
mu=4*np.pi*1e-7;J=np.array([[0.,-1.],[1.,0.]])
rows=[];maxerr=0.;checks=0
with zipfile.ZipFile(p) as archive:
    assert archive.testzip() is None
    for name in archive.namelist():
        if not name.lower().endswith('.edi'):continue
        blocks={}
        for block in re.split(r'(?m)^>',archive.read(name).decode())[1:]:
            head,_,body=block.partition('\n');key=head.strip().split()[0]
            if '//' not in head or key=='!':continue
            try:blocks[key]=np.array([float(w) for w in body.split()])
            except ValueError:continue
        for i,f in enumerate(blocks['FREQ']):
            Z=np.array([[blocks['Z'+a+b+'R'][i]+1j*blocks['Z'+a+b+'I'][i] for b in 'XY'] for a in 'XY'])
            if not np.isfinite(Z).all() or np.max(abs(Z))>=1e30:continue
            P=J@(1000*mu*Z);Q=(P+P.conj().T)/2
            q=Q[0,1];center=Q.trace().real/2;radius=abs(q)
            # Equal diagonal magnetic covariance and unit trace: purely
            # hypothetical RMS H norm in A/m, not measured field amplitudes.
            # Sharp support over all complex coherences, no phase assumed.
            z=q/(2*abs(q)) if abs(q)>0 else 0j
            for sign in (-1,1):
                C=np.array([[.5,sign*z],[sign*z.conjugate(),.5]])
                assert np.linalg.eigvalsh(C)[0]>=-1e-14
                actual=np.trace(Q@C).real;expected=center+sign*radius
                maxerr=max(maxerr,abs(actual-expected));assert abs(actual-expected)<1e-12;checks+=1
            ev=np.linalg.eigvalsh(Q)
            assert ev[0]<=center-radius+1e-12 and center+radius<=ev[1]+1e-12
            rows.append(dict(f=float(f),radius=float(radius),center=float(center),lo=float(center-radius),hi=float(center+radius),negative_mode=bool(ev[0]<0),nonzero_cross=bool(abs(q)>1e-12*np.linalg.norm(Q,2))))
assert len(rows)==1467
out={}
for tag,target in [('all',None),('5mHz',.005),('50mHz',.05)]:
    rr=[r for r in rows if target is None or abs(r['f']/target-1)<1e-5]
    out[tag]=dict(n=len(rr),needs_cross_quadrature=sum(r['nonzero_cross'] for r in rr),strict_positive_equal_autospectra=sum(r['lo']>0 for r in rr),sign_ambiguous_equal_autospectra=sum(r['lo']<0<r['hi'] for r in rr),nonpositive_upper=sum(r['hi']<=0 for r in rr),negative_mode_unrestricted=sum(r['negative_mode'] for r in rr),cross_radius_ohm_min_median_max=np.percentile([r['radius'] for r in rr],[0,50,100]).tolist())
print(json.dumps(dict(status='CONDITIONAL_COVARIANCE_FIBRE_REPAIR',archive_sha256=sha,records=len(rows),attained_endpoints=checks,max_endpoint_error=maxerr,summary=out,physical_admission=False),indent=2))
