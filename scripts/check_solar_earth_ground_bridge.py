"""Measured EDI port algebra and missing-link discriminator; no physical control design.
Usage: python solar_ground_bridge.py /path/to/auslamp-qld-phase-3-edi.zip
"""
import hashlib,json,re,sys,zipfile
from pathlib import Path
import numpy as np
import sympy as s
p=Path(sys.argv[1]);sha=hashlib.sha256(p.read_bytes()).hexdigest()
assert sha=='26020ec6a1db00359a8703fad30219e6e2e9b20e8b87e968633576525b4fab49'
J=s.Matrix([[0,-1],[1,0]]); I=s.eye(2)
Z=s.Matrix(2,2,s.symbols('z:4',complex=True)); h=s.Matrix(s.symbols('h:2',complex=True))
H=J*h; E=Z*H; P=Z*J
herm=lambda A:(A+A.H)/2
assert s.simplify((H.H*herm(J*Z)*H-h.H*herm(P)*h)[0])==0
# Exact Cayley congruence for arbitrary complex impedance, positive reference R.
r=s.symbols('r',positive=True); A=P+r*I; D=P-r*I
assert (A.H*A-D.H*D-4*r*herm(P)).applyfunc(s.expand)==s.zeros(2)
# Missing transport can be any passive transmission fraction even with fixed load.
# Orthogonal two-channel dilation: a transmitted channel and an unobserved exit.
for t,v in [(0,1),(s.Rational(3,5),s.Rational(4,5)),(1,0)]:
    T=s.Matrix([[t,-v],[v,t]]);assert T.T*T==I
    assert (T*s.Matrix([1,0]))[0]**2==t*t
mu=4*np.pi*1e-7; J=np.array(J,dtype=float); I=np.eye(2)
herm=lambda A:(A+A.conj().T)/2
rows=[];counts={};maxerr=0.;maxpair=0.;minrows=[]
with zipfile.ZipFile(p) as archive:
    assert archive.testzip() is None
    for name in archive.namelist():
        if not name.lower().endswith('.edi'):continue
        text=archive.read(name).decode(); blocks={}
        for block in re.split(r'(?m)^>',text)[1:]:
            head,_,body=block.partition('\n'); key=head.strip().split()[0]
            if '//' not in head or key=='!':continue
            try:blocks[key]=np.array([float(v) for v in body.split()])
            except ValueError:continue
        for i,f in enumerate(blocks['FREQ']):
            Z=np.array([[blocks['Z'+a+b+'R'][i]+1j*blocks['Z'+a+b+'I'][i] for b in 'XY'] for a in 'XY'])
            var=np.array([[blocks['Z'+a+b+'.VAR'][i] for b in 'XY'] for a in 'XY'])
            if not np.isfinite(Z).all() or np.max(abs(Z))>=1e30 or not np.isfinite(var).all() or np.max(var)>=1e30 or np.min(var)<0:continue
            Z*=1000*mu; P=Z@J; Q=herm(P); ev=np.linalg.eigvalsh(Q)
            # Arbitrary positive reference for numerical Cayley identity only.
            r=np.linalg.norm(P,2); A=P+r*I; D=P-r*I
            assert r>0
            S=np.linalg.solve(A.T,D.T).T
            defect=I-S.conj().T@S
            check=4*r*np.linalg.solve(A.conj().T,Q)@np.linalg.inv(A)
            maxerr=max(maxerr,float(np.linalg.norm(defect-check,2)))
            maxpair=max(maxpair,float(np.linalg.norm(Q-J.T@herm(J@Z)@J,2)))
            # Distance to PSD Hermitian part (no repair applied).
            neg=max(0.,-float(ev[0])); scale=1000*mu*np.sqrt(var.sum())
            rows.append(dict(f=float(f),positive=bool(ev[0]>0),negative=bool(ev[0]<0),margin_ohm=float(ev[0]),psd_distance_ohm=neg,relative_variance_scale=float(ev[0]/scale) if scale>0 else None,condition=float(np.linalg.cond(P)),contractive=bool(np.linalg.eigvalsh(defect)[0]>=-1e-10)))
assert maxerr<1e-8 and maxpair<1e-12
for tag,target in [('all',None),('5mHz',.005),('50mHz',.05)]:
    rr=[x for x in rows if target is None or abs(x['f']/target-1)<1e-5]
    counts[tag]=dict(n=len(rr),positive=sum(x['positive'] for x in rr),negative=sum(x['negative'] for x in rr),contractive=sum(x['contractive'] for x in rr),margin_ohm_quantiles=np.percentile([x['margin_ohm'] for x in rr],[0,50,100]).tolist(),positive_after_assumed_1_scale=sum(x['relative_variance_scale'] is not None and x['relative_variance_scale']>1 for x in rr),positive_after_assumed_3_scale=sum(x['relative_variance_scale'] is not None and x['relative_variance_scale']>3 for x in rr),max_condition=max(x['condition'] for x in rr))
print(json.dumps(dict(status='CONDITIONAL_EDI_BOUNDARY_ALGEBRA',archive_sha256=sha,counts=counts,max_cayley_error=maxerr,max_pair_error_ohm=maxpair,physical_admission=False),indent=2))
