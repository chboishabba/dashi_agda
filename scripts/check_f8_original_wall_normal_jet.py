"""Original F8 characteristic wall second-normal jet and PDE residual receipt.

Uses the EXISTING evolve(...,sample_n) source without changing it. Three
interior samples at n=dn,2dn,3dn reconstruct h_nn(0) by a signed one-sided
four-point stencil. Exact imposed characteristic h_n=-6 ci*bump(t) enters
GN wave H_tt; compare an independent time derivative of the saved h_t.
The grid diagnostic is NOT a certified fourth normal derivative or stencil
error, and it does NOT establish continuum convergence or H7.
"""
import argparse
import numpy as np
import sympy as s


def wall_second(values,dn):
    if len(values)!=4 or dn<=0:raise ValueError('four normal nodes required')
    return (2*values[0]-5*values[1]+4*values[2]-values[3])/dn**2


def wave_acceleration(t,k,h,ht,hn,hnn):
    g=np.sqrt(1+t*t)
    bn_over_a=-t/g-3*g/t
    return hnn+bn_over_a*hn-3*ht/t-(k/t)**2*h


def exact():
    n=s.symbols('n',real=True);d=s.symbols('d',positive=True)
    weights=[2,-5,4,-1]
    for degree in range(4):
        got=sum(w*(j*d)**degree for j,w in enumerate(weights))/d**2
        want=2 if degree==2 else 0
        assert s.simplify(got-want)==0
    # Conservative Taylor remainder: sup|u_nnnn| * 25/4 * dn².
    assert sum(abs(w)*j**4 for j,w in enumerate(weights))==150
    assert s.Rational(150,24)==s.Rational(25,4)
    h=s.symbols('h',positive=True)
    p=1+2*n+3*n**2+4*n**3+5*n**4
    approx=wall_second([p.subs(n,j*h) for j in range(4)],h)
    assert s.simplify(approx-s.diff(p,n,2).subs(n,0))==-110*h*h
    # Validates actual F8 GN wall Bn/A, not flat normal coefficient.
    t=s.symbols('t',positive=True)
    B=s.sinh(s.asinh(t)-n)**3*s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    assert s.simplify(s.diff(B,n).subs(n,0)/t**3+t/s.sqrt(1+t*t)+3*s.sqrt(1+t*t)/t)==0
    # Independent 4-point one-sided first derivative (order-three) for V=H_n.
    assert sum(w*j*j for j,w in enumerate((-11,18,-9,2)))==0
    assert sum(w*j for j,w in enumerate((-11,18,-9,2)))==6
    # Negative control: first-normal Israel alone never fixes second normal.
    assert wall_second([0,0,0,1],1)==-1
    print('PASS one-sided normal stencil moments, exact F8 wall wave acceleration and derivative negative controls')


def original(cells=64,final=1.045):
    from check_f8_characteristic_history import evolve,coefficient,bump
    k=np.array([0.,5.,10.]);ci=coefficient(k)
    dn=.5/cells
    rows=[];normal_rows=[]
    for j in (1,2,3):
        got=evolve(k,ci,cells,final,sample_n=j*dn)
        if j==1:time,mass,flux,H,Ht,outer,_=got
        else:
            assert np.allclose(time,got[0],rtol=0,atol=0)
            assert np.allclose(H,got[3],rtol=0,atol=0)
        rows.append(got[-1][:,0])
        normal_rows.append(got[-1][:,2])
    values=[H[-1],*rows]
    Hnn=wall_second(values,dn)
    hn=-6*ci*bump(final)
    hnn_from_V=(-11*hn+18*normal_rows[0]-9*normal_rows[1]+2*normal_rows[2])/(6*dn)
    h_tt_pde=wave_acceleration(final,k,H[-1],Ht[-1],hn,Hnn)
    dt=time[1]-time[0]
    h_tt_time=(3*Ht[-1]-4*Ht[-2]+Ht[-3])/(2*dt)
    defect=h_tt_pde-h_tt_time
    assert np.all(np.isfinite(defect))
    assert abs(H[-1,0])+abs(Ht[-1,0])+abs(Hnn[0])<1e-12
    return {'cells':cells,'t':final,'k':k.tolist(),
            'normal2':Hnn.tolist(),'normal2_from_characteristic':hnn_from_V.tolist(),
            'mixed_normal_defect':(Hnn-hnn_from_V).tolist(),
            'pde_time_defect':defect.tolist(),
            'max_defect':float(np.max(abs(defect))),
            'source_wall_hn':hn.tolist()}


def run():
    exact()
    a=original(64);b=original(128)
    print('ORIGINAL first-order GN normal-jet comparison:',a,b,flush=True)
    print('NOT CERTIFIED: this checks only Hnn numerical and Htt residual; derivatives through N2_5 not admitted')
    return a,b

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--original',action='store_true')
    args=p.parse_args()
    if args.original:run()
    else:exact()
