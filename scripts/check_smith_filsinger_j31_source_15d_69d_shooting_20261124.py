#!/usr/bin/env python3
"""J31 seven-physical-chart source-specific 15D/69D shooting geometry.

Numerical source-equation diagnostic only. Does NOT prove a 15D/69D interval
Jacobian, all-ball branch validity, a Krawczyk inclusion or a periodic orbit.
Uses the original committed J25/J28B-equation independent numerical producers.
"""
import json, math, argparse
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
import independent_full_period_numerical_audit as b
import independent_full_period_monodromy_audit as m

P=b.P
MODES=((0,0,1),(0,1,1),(0,1,0),(0,1,1),(1,1,1),(1,0,1),(0,0,1))
TIMES=(3.389367008894,3.491292721190,3.515340479143,
       4.275489023275,4.323837945006,4.928751407316)
NAMES=("V_ON","SPARK_OFF","SPARK_ON","U_ON","V_OFF","U_OFF")
def guard(k,x):
    return (x[3]-x[4]-P['Vd']) if k in (0,4) else (
        (x[2]-x[4]-P['Vd']) if k in (3,5) else
        x[4]-(P['Voff'] if k==1 else P['Von']))
def normal(k):
    n=np.zeros(9)
    if k in (0,4): n[3]=1;n[4]=-1
    elif k in (3,5): n[2]=1;n[4]=-1
    else:n[4]=1
    return n
CU=np.array([0,0,-1.55/1.17,-1/1.17,1/P['Cb'],0,0,0,0])
CV=np.array([0,0,-1/1.17,-1.4/1.17,1/P['Cb'],0,0,0,0])
NU=normal(3); NV=normal(0)
def mode_f(t,x,mode):
    U,V,chi=mode
    gU=float(NU@x-P['Vd']);gV=float(NV@x-P['Vd'])
    actualU=max(0,gU/P['Rd']);actualV=max(0,gV/P['Rd'])
    forceU=(gU/P['Rd']) if U else 0.
    forceV=(gV/P['Rd']) if V else 0.
    return np.asarray(b.f(t,x,bool(chi)))+CU*(forceU-actualU)+CV*(forceV-actualV)
def mode_J(x,mode):
    U,V,chi=mode
    a=m.J(x,bool(chi)).copy()
    dU=(U-int((NU@x-P['Vd'])>0))/P['Rd']
    dV=(V-int((NV@x-P['Vd'])>0))/P['Rd']
    return a+dU*np.outer(CU,NU)+dV*np.outer(CV,NV)
def leg(t0,t1,x,mode,step=.012):
    y0=np.r_[x,np.eye(9).ravel()]
    def ode(t,y):
        xx=y[:9];Phi=y[9:].reshape(9,9)
        return np.r_[mode_f(t,xx,mode),(mode_J(xx,mode)@Phi).ravel()]
    sol=solve_ivp(ode,(t0,t1),y0,method="DOP853",rtol=4e-12,
                  atol=1e-13,max_step=step)
    if not sol.success:raise RuntimeError(sol.message)
    return sol.y[:9,-1],sol.y[9:,-1].reshape(9,9),len(sol.t)-1
def fifteen(z,step=.012):
    x0=np.array(z[:9]);tt=[0.,*z[9:],b.tau]
    if not np.all(np.diff(tt)>0):raise ValueError("event order invalid")
    states=[x0];Phi=[];steps=[]
    for k in range(7):
        x,T,n=leg(tt[k],tt[k+1],states[-1],MODES[k],step)
        states.append(x);Phi.append(T);steps.append(n)
    F=np.r_[states[-1]-x0,[guard(k,states[k+1]) for k in range(6)]]
    J=np.zeros((15,15));A=np.eye(9);prefix=[]
    for t in Phi:A=t@A;prefix.append(A.copy())
    J[:9,:9]=prefix[-1]-np.eye(9)
    jumps=[];slopes=[]
    for k in range(6):
        xx=states[k+1];pre=mode_f(tt[k+1],xx,MODES[k])
        post=mode_f(tt[k+1],xx,MODES[k+1])
        jumps.append(pre-post);slopes.append(float(normal(k)@pre))
        J[9+k,:9]=normal(k)@prefix[k]
        J[9+k,9+k]=slopes[k]
        w=pre-post
        for j in range(k+1,7):
            w=Phi[j]@w
            if j<6:J[9+j,9+k]=normal(j)@w
        J[:9,9+k]=w
    D=J[9:,9:];R=J[:9,:9]-J[:9,9:]@np.linalg.solve(D,J[9:,:9])
    M=R+np.eye(9)
    direct=np.eye(9)
    for k in range(7):
        direct=Phi[k]@direct
        if k<6:direct=(np.eye(9)-np.outer(jumps[k],normal(k))/slopes[k])@direct
    assert np.linalg.norm(M-direct,np.inf)<3e-11
    return dict(F=F,J=J,states=states,Phi=Phi,jumps=jumps,
                slopes=slopes,M=M,steps=steps,times=tt)
def sixty_nine(z,shot,step=.012):
    tt=shot['times'];Y=shot['states'][:7]
    J=np.zeros((69,69));f=np.zeros(69);legsteps=[]
    for k in range(7):
        x,T,n=leg(tt[k],tt[k+1],Y[k],MODES[k],step)
        legsteps.append(n)
        pre=mode_f(tt[k],Y[k],MODES[k])
        post=mode_f(tt[k+1],x,MODES[k])
        rows=slice(9*k,9*(k+1)) if k<6 else slice(54,63)
        if k<6:
            f[rows]=Y[k+1]-x
            J[rows,9*k:9*(k+1)]=-T
            J[rows,9*(k+1):9*(k+2)]=np.eye(9)
            J[rows,63+k]=-post
        else:
            f[rows]=x-Y[0]
            J[rows,:9]=-np.eye(9);J[rows,54:63]=T
        if k>0:
            # Lower endpoint: -Phi*f, reversed for matching residual.
            J[rows,63+k-1]=(-T@pre) if k==6 else (T@pre)
    for k in range(6):
        f[63+k]=guard(k,Y[k+1])
        J[63+k,9*(k+1):9*(k+2)]=normal(k)
    s69=np.linalg.solve(J,-f)
    s15=np.linalg.solve(shot['J'],-shot['F'])
    discrepancy=float(np.linalg.norm(np.r_[s69[:9],s69[63:]]-s15,np.inf))
    assert discrepancy<1e-12,("69D-15D Schur mismatch",discrepancy)
    assert np.linalg.norm(f[:54],np.inf)<1e-12
    return dict(unknowns=69,matching_equations=54,closure_equations=9,
        guard_equations=6,nonzero_jacobian_entries=int(np.count_nonzero(J)),
        total_jacobian_entries=69*69,
        state_matching_residual_inf=float(np.linalg.norm(f[:54],np.inf)),
        reduced_newton_step_discrepancy_inf=discrepancy,
        condition_two=float(np.linalg.cond(J)),legsteps=legsteps)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--fd",action="store_true")
    args=ap.parse_args()
    z=np.r_[b.root0,TIMES]
    a=fifteen(z);J=a["J"];F=a["F"]
    wide=sixty_nine(z,a)
    assert np.array_equal(np.sign(a["slopes"]),[1,-1,1,1,-1,-1])
    _,prior,_,_=m.hybrid_tangent(b.root0,rtol=8e-12,max_step=.008)
    prior_error=float(np.linalg.norm(prior-a["M"],np.inf))
    assert prior_error<1e-6
    C=np.linalg.inv(J)
    Crat=[[str(__import__('fractions').Fraction(round(float(x)*10**12),10**12))
           for x in row] for row in C]
    CC=np.array([[float(__import__('fractions').Fraction(x)) for x in row] for row in Crat])
    q0=float(np.linalg.norm(np.eye(15)-CC@J,np.inf))
    assert q0<5e-9
    step=np.linalg.solve(J,-F)
    fresh=fifteen(z+step)
    diffs=[]
    if args.fd:
        for k in range(15):
            d=1e-5 if k<9 else 1e-6
            zz=z.copy();zz[k]+=d;fp=fifteen(zz)['F']
            zz[k]-=2*d;fm=fifteen(zz)['F']
            diffs.append(float(np.linalg.norm((fp-fm)/(2*d)-J[:,k],np.inf)))
    result={
      "status":"PASS_J31_NUMERICAL_SOURCE_GEOMETRY_15D_69D_ONLY",
      "mode_graph":MODES,"original_guard_names":NAMES,
      "original_J29_nominal_roots":6,"original_J24_boxes":5,
      "15D_centre":list(map(float,z)),
      "15D_full_residual":list(map(float,F)),
      "15D_full_derivative":J.tolist(),
      "15D_initial_residual_infty":float(np.linalg.norm(F,np.inf)),
      "15D_newton_residual_infty":float(np.linalg.norm(fresh['F'],np.inf)),
      "15D_cross_independent_monodromy_infty":prior_error,
      "15D_guard_slopes":a["slopes"],
      "15D_rational_C_12dp":Crat,
      "15D_rounded_C_preconditioned_centre_error_infty":q0,
      "15D_fd_max_abs_error":max(diffs) if diffs else None,
      "69D_multiple_shooting":wide,
      "strict_nonzero_ball_interval_Krawczyk":False,
      "full_15D_interval_DF":False,
      "full_69D_interval_DF":False,
      "exact_periodic_orbit_proved":False,
      "original_metered_hardware":False,
      "github_ci":False}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ("status","15D_initial_residual_infty",
       "15D_newton_residual_infty","15D_cross_independent_monodromy_infty",
       "15D_fd_max_abs_error")},indent=2))
    print("69D matching Schur error",wide["reduced_newton_step_discrepancy_inf"])
if __name__=="__main__":main()
