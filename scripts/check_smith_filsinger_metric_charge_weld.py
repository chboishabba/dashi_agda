"""Original XCIII/XCIV incidence and XCV off-guard circuit, metric-work/DC weld.
Transcribed source matrices; conditional finite Hodge path, not Earth/GR calibration.
"""
import json
import sympy as s
import numpy as np
R=s.Rational
edges=[(1,4),(2,5),(0,1),(1,2),(3,4),(4,5),(0,3)]
G=s.zeros(7,6)
for i,(a,b) in enumerate(edges): G[i,a]=-1;G[i,b]=1
D=s.Matrix([[1,0,1,0,-1,0,-1],[-1,1,0,1,0,-1,0]])
Da=D[:,:4];Ga=G[:4,:];L=s.eye(4)[:,:2]
N0=s.diag(R(1,2),R(1,2),10,10)
assert D*G==s.zeros(2,6) and Ga.rank()==4
# Original clamp: inactive displacement and effort zero. Charge is injective
# on active flux; no nonzero neutral static polarization with original clamp.
px,py=s.symbols('px py',real=True);p=s.Matrix([px,py]);da=L*p
assert Ga.T*da==s.Matrix([0,-px,-py,0,px,py])
assert Ga.T.nullspace()==[]
assert Da*N0*L==s.Matrix([[R(1,2),0],[-R(1,2),R(1,2)]])
assert (Da*N0*L).det()!=0
# General static recovery for admitted charge in the original clamped model:
# closed active effort = F u, F includes the boundary return.
F=s.Matrix([[1,0],[0,1],[-1,0],[1,-1]])
assert Da*F==s.zeros(2) and F.rank()==4-Da.rank()
u=s.Matrix(s.symbols('u:2',real=True));ds=N0.inv()*F*u+L*p
rho=Ga.T*ds;left=(Ga*Ga.T).inv()*Ga
assert left*rho==ds
assert s.ones(1,6)*rho==s.zeros(1,1)
# Free unclamped comparison, illustrative SPD mass, not physical admission.
Gred=G[:,1:];Me=s.diag(2,2,R(1,10),R(1,10),1,1,1);p7=L*p
p7=p7.col_join(s.zeros(3,1));phi=-(Gred.T*Me*Gred).inv()*Gred.T*p7
e=Gred*phi;d=Me*e+p7
assert D*e==s.zeros(2,1) and G.T*d==s.zeros(6,1)
assert e!=s.zeros(7,1)
# Exact two-time discrete gradient, all non-diagonal inverse Hodge entries.
x=s.Matrix(s.symbols('x:2',real=True));y=s.Matrix(s.symbols('y:2',real=True));a,b,c,d0,f,g=s.symbols('a b c d f g',real=True)
N=s.Matrix([[a,b],[b,c]]);M=s.Matrix([[d0,f],[f,g]]);xb=(x+y)/2;Nb=(N+M)/2
assert s.expand((y.dot(M*y)-x.dot(N*x))/2-xb.dot(Nb*(y-x))-(y.dot((M-N)*y)+x.dot((M-N)*x))/4)==0
# Original XCV native off-guard linear circuit, including bank state.
Mi=s.Matrix([[2,R(3,5)],[R(3,5),R(3,2)]]);Mc=s.Matrix([[R(7,5),-1],[-1,R(31,20)]])
z=s.Matrix(s.symbols('i j u v b q r ih x',real=True));i,j,u,v,b,q,r,ih,xx=z
f=(Mi.inv()*s.Matrix([-R(35,100)*i,u-v-R(28,100)*j])).col_join(Mc.inv()*s.Matrix([-j+R(35,100)*q+2*ih,j])).col_join(s.Matrix([-R(18,1000)*b/R(65,100),R(11,10)*r-R(2,10000)*q-R(35,100)*u/2,-R(11,10)*q-R(2,10000)*r,(-xx-R(5,100)*ih-2*u)/R(15,100),(ih-R(52,100)*xx)/R(12,100)]))
Ac=f.jacobian(z);K=s.zeros(2,9);K[0,5]=K[1,6]=1
W=s.diag(Mi,Mc,R(65,100),2,2,R(15,100),R(12,100));loss=s.diag(R(35,100),R(28,100),0,0,R(18,1000),R(4,10000),R(4,10000),R(5,100),R(52,100))
assert Ac.T*W+W*Ac==-2*loss and W*K.T==2*K.T
# Same finite work-conjugate source/receiver at arbitrary Hodge. No actual
# metric path is inferred; prescribed shear is a paid external control.
Da,Ga,D,G,L,N0,Ac,K,W,loss=map(lambda a:np.array(a,float),(Da,Ga,D,G,L,N0,Ac,K,W,loss))
Y=np.diag([.1,1000.]);root=np.sqrt(Y);rad=np.sqrt(.03);beta=10.;dt=.025
Dloss=np.diag([.2,.2,20/9,20/9]);I=np.eye(19)
def hodge(k,amp):
    T=np.eye(4);T[0,1]=amp*np.sin(2*np.pi*k/16);T[1,2]=amp*np.sin(2*np.pi*k/16)
    return T.T@N0@T

def unpack(z,N):
    d,b,p,v,c=z[:4],z[4:6],z[6:8],z[8:10],z[10:];x=d-L@p;e=N@x;h=b/1.5
    return x,e,h,p,v,c

def energy(z,N):
    x,e,h,p,v,c=unpack(z,N);return (x@e+1.5*(h@h)+(8/3)*(p@p)+(2/3)*(v@v)+c@W@c)/2

def rhs(z,N,a):
    x,e,h,p,v,c=unpack(z,N);E=L.T@e;jc=beta*rad*K@c
    J=Dloss@e+L@(Y@E-2*root@a+jc)
    return np.r_[Da.T@h-J,-Da@e,v,1.5*E-2/3*v-4*p,Ac@c+beta*rad*K.T@E/2]

def run(amp,on):
    maps=[];T=I.copy();b=np.zeros(19)
    for k in range(16):
        n0=hodge(k,amp);n1=hodge(k+1,amp);nm=(n0+n1)/2;a=np.array([0.,float(on and 8<=k<12)])
        A=np.column_stack([rhs(I[:,j],nm,np.zeros(2)) for j in range(19)]);F=np.linalg.solve(I-dt*A/2,I+dt*A/2);g=np.linalg.solve(I-dt*A/2,dt*rhs(np.zeros(19),nm,a));maps.append((n0,n1,nm,a,F,g));T=F@T;b=F@b+g
    start=np.linalg.solve(I-T,b);z=start.copy();tot=np.zeros(8);maxerr=maxcharge=0.
    for n0,n1,nm,a,F,g in maps:
        zn=F@z+g;mid=(z+zn)/2;x,e,h,p,v,c=unpack(mid,nm);E=L.T@e;out=root@E-a;jc=beta*rad*K@c
        x0=unpack(z,n0)[0];x1=unpack(zn,n1)[0];metric=(x0@(n1-n0)@x0+x1@(n1-n0)@x1)/4
        J=Dloss@e+L@(Y@E-2*root@a+jc);Jfull=np.r_[J,D[:,4:].T@h];d0=np.r_[z[:4],np.zeros(3)];d1=np.r_[zn[:4],np.zeros(3)]
        maxcharge=max(maxcharge,np.max(abs(G.T@(d1-d0+dt*Jfull))))
        useful=.52*c[-1]**2;ml=e@Dloss@e+4/9*(v@v);cl=c@loss@c-useful
        work=np.array([dt*(a@a),dt*(out@out),metric,dt*useful,dt*ml,dt*cl,dt*(E@jc),max(metric,0)])
        err=energy(zn,n1)-energy(z,n0)-(work[0]-work[1]+work[2]-sum(work[3:6]));maxerr=max(maxerr,abs(err));tot+=work;z=zn
    ret=np.max(abs(z-start));delta=energy(z,hodge(16,amp))-energy(start,hodge(0,amp));assert ret<1e-9 and maxerr<1e-9 and maxcharge<1e-9
    return dict(shear=amp,source=on,incident=tot[0],reflected=tot[1],signed_metric_work=tot[2],useful=tot[3],field_heat=tot[4],circuit_heat=tot[5],interface=tot[6],positive_metric_work=tot[7],net_after_signed_metric=tot[3]-tot[2],net_without_recovery=tot[3]-tot[7],storage_change=delta,return_error=ret,max_step_energy_error=maxerr,max_charge_error=maxcharge)
rows=[run(a,on) for a in (0.,.1,.25) for on in (False,True)]
print(json.dumps(dict(status='CONDITIONAL_ORIGINAL_FINITE_METRIC_CHARGE_WELD',dc_clamped_charge_injective=True,dc_neutral_static_polarization_requires_zero=True,unclamped_neutral_e=[str(t) for t in e],rows=rows,scope='Original XCIII/XCIV incidence, XCV linear off-guard circuit transcribed; illustrative SPD inverse Hodge shear and prescribed source; linear periodic midpoint solution only, no original nonlinear guard admission, physical geometry, GR metric, upstream access or solar extraction.'),indent=2))
