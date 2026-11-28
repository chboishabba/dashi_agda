"""Conditional indexed current-to-spherical boundary weld; not a physical source admission."""
import json
from itertools import product
import numpy as np
from scipy.integrate import solve_ivp, quad_vec
from solar_periodic_spatial import run

MU=4*np.pi*1e-7; EP=8.8541878128e-12; R=6371000.; H=110000.; ya=1/(MU*1e6)

# Same l=1 radial equation and power-normalized magnetic coordinate as
# check_smith_filsinger_oct369_layered_shell.py (exp(+i omega t)).
def layer(f,r0,r1,sigma,typ):
    w=2*np.pi*f; A=sigma+1j*w*EP
    def mat(r):
        a,b=(1j*w*MU,A+2/(1j*w*MU*r*r)) if typ=='TE' else (1j*w*MU+2/(A*r*r),A)
        return np.array([[0,-a*ya],[-b/ya,0]],complex)
    sol=solve_ivp(lambda r,t:(mat(r)@t.reshape(2,2)).ravel(),(r0,r1),np.eye(2,dtype=complex).ravel(),rtol=2e-11,atol=2e-12,dense_output=True)
    assert sol.success
    return sol


def project(j):
    # Selected angular embedding of a 1D vector, not observed spatial geometry.
    # P(n)j tangent current -> six TE/TM coefficients; preserve off-chart residual.
    B=[]; v=[]; weights=[]
    for site in product((-1,0,1),repeat=3):
        if not any(site): continue
        n=np.array(site)/np.linalg.norm(site); P=np.eye(3)-np.outer(n,n)
        B.append(np.sqrt(1.5)*np.column_stack((np.cross(n,np.eye(3)).T,P)))
        v.append(P@j); weights.append({1:1/21,2:4/105,3:9/280}[sum(x!=0 for x in site)])
    B=np.array(B); v=np.array(v); weights=np.array(weights)
    m=np.einsum('n,nij,ni->j',weights,B,v)
    residual=v-B@m
    assert np.linalg.norm(np.einsum('n,nij,ni->j',weights,B,residual))<1e-12
    assert np.allclose(m[3:],np.sqrt(2/3)*j) and np.linalg.norm(m[:3])<1e-12
    return m,float(np.linalg.norm(residual))


def radial(f,source,yg=1.,sigma=1e-9):
    if f<=0: raise ValueError('DC uses a separate electrostatic/magnetostatic boundary problem')
    layers=[(R,R+H/2,0.),(R+H/2,R+H,sigma)]
    sols={typ:[layer(f,*v,typ) for v in layers] for typ in ('TE','TM')}
    mats={typ:sols[typ][1].y[:,-1].reshape(2,2)@sols[typ][0].y[:,-1].reshape(2,2) for typ in sols}
    A,B,C,D=[np.diag(np.repeat([mats[t][i,j] for t in ('TE','TM')],3)) for i,j in ((0,0),(0,1),(1,0),(1,1))]
    # Source is an independently prescribed impressed sheet RHS, not a new natural reservoir.
    # h1=(I+S)e1-source. All powers normalized by ya.
    S=2*np.eye(6); U=np.eye(6)+S
    e0=np.linalg.solve(U@(A-B*yg)-(C-D*yg),source); h0=-yg*e0
    e1=A@e0+B@h0; h1=C@e0+D@h0
    heat=0.
    for typ,sl in (('TE',slice(0,3)),('TM',slice(3,6))):
        state=np.stack((e0[sl],h0[sl]))
        for (r0,r1,sg),sol in zip(layers,sols[typ]):
            w=2*np.pi*f; Ac=sg+1j*w*EP
            def dens(r):
                ee,hh=sol.sol(r).reshape(2,2)@state
                return sg/ya*(np.vdot(ee,ee).real+(2*ya**2*np.vdot(hh,hh).real/(abs(Ac)**2*r*r) if typ=='TM' else 0))
            heat+=float(quad_vec(dens,r0,r1,epsabs=1e-11,epsrel=1e-9)[0]); state=sol.y[:,-1].reshape(2,2)@state
    supplied=np.vdot(e1,source).real; top=np.vdot(e1,U@e1).real; bottom=yg*np.vdot(e0,e0).real
    err=float(supplied-top-bottom-heat)
    assert abs(err)<1e-8*max(1.,abs(supplied)) and heat>=0 and bottom>=0
    assert np.linalg.norm(h1-U@e1+source)<1e-8*max(1.,np.linalg.norm(source))
    return dict(f_Hz=f,sheet_work=float(supplied),top_loss=float(top),bottom_loss=float(bottom),radial_loss=float(heat),residual=err)


def fixtures():
    rows=[]; leftovers=[]
    for k,l in ((1,3),(2,3),(1,4),(2,4)):
        active=run(k,l,True,True); passive=run(k,l,True,False); n=2**k; dx=1/n; N=2**l
        # current in normalized cell variables; spatial integral = sum sqrt(dx)*j
        j=(active['history'][:-1,:6*n]-passive['history'][:-1,:6*n]).reshape(N,n,6)[...,3:].sum(axis=1)*np.sqrt(dx)
        # np.fft.fft coefficients reconstruct exp(+i omega t), radial convention.
        coeff=np.fft.fft(j,axis=0)/N; assert np.allclose(np.fft.ifft(coeff*N,axis=0).real,j)
        assert np.allclose(coeff[1:N//2],coeff[-1:N//2:-1].conj())
        leftovers.append(dict(k=k,l=l,dc=coeff[0].real.tolist(),nyquist=coeff[N//2].real.tolist()))
        # Selected clock 7.83 Hz fundamental. This is not physical time calibration.
        for m in range(1,N//2):
            source,res=project(np.sqrt(2)*coeff[m]); out=radial(7.83*m,source)
            rows.append(dict(k=k,l=l,harmonic=m,angular_residual=res,**out))
    z=radial(7.83,np.zeros(6)); assert z['bottom_loss']==0 and z['sheet_work']==0
    return dict(status='CONDITIONAL_ONE_WAY_INDEXED_RADIAL_COUPLING',rows=rows,retained_dc_and_nyquist=leftovers,max_balance=max(abs(x['residual']) for x in rows),physical_admission=False,scope='Synthetic periodic spatial current differences projected onto selected tangent dipole embedding and impressed sheet at top of existing l=1 radial equation; arbitrary scale and clock, no source backreaction into original grid, no physical power inference, DC and Nyquist retained but not propagated.')

if __name__=='__main__': print(json.dumps(fixtures(),indent=2))
