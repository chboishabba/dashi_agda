"""MR26-39 reciprocal shared-cavity and half-mode work checks.
Analytic reference only; no calibrated Earth cavity or HF excitation law.
"""
import sympy as s

checks=[]
def eq(name,a,b):
    d=a-b
    assert (all(s.simplify(x)==0 for x in d) if isinstance(d,s.MatrixBase)
            else s.simplify(d)==0), (name,d)
    checks.append(name)

# MR30-32: original shared observation [1,1], with bright/dark input.
k1,k2,r,L,delta=s.symbols('k1 k2 r L delta',positive=True,real=True)
k=s.Matrix([k1,k2]); e=k.dot(k)/2
b=k/s.sqrt(2*e); d=s.Matrix([-k2,k1])/s.sqrt(2*e)
eq('bright normalization',b.T*b,s.eye(1))
eq('dark normalization',d.T*d,s.eye(1))
eq('bright dark orthogonal',b.T*d,s.zeros(1))
eq('BIDI complete source fibre',b*b.T+d*d.T,s.eye(2))
eq('dark source not observed',k.T*d,s.zeros(1))
x,y,u,v,A,B=s.symbols('x y u v A B',real=True)
inc=s.Matrix([x+s.I*y,u+s.I*v]); a=A+s.I*B
out=inc-k*a
norm=lambda z:(z.H*z)[0]
eq('signed cavity boundary',norm(inc)-norm(out),2*s.re(s.conjugate(a)*(k.T*inc)[0])-2*e*s.Abs(a)**2)
# Steady state cavity: adot=-(e+r+L+i delta)a+k^T inc.
# Use independent real quadratures and the equation to identify input work.
F=(k.T*inc)[0]; adot=-(e+r+L+s.I*delta)*a+F
eq('cavity energy derivative',2*s.re(s.conjugate(a)*adot),norm(inc)-norm(out)-2*(r+L)*s.Abs(a)**2)
eta=4*e*L/((e+r+L)**2+delta**2)
eq('reverse load derivative',s.diff(eta,L),4*e*((e+r)**2+delta**2-L**2)/((e+r+L)**2+delta**2)**2)
eq('resonant bright optimum',eta.subs({delta:0,L:e+r}),e/(e+r))
eq('ideal bright/dark transfer', (b*b.T).subs({k1:1,k2:1}),s.ones(2)/2)
# MR34-37: reciprocal half-frequency, slow cavity and fast-control coordinate.
q,z,h,vq,vz,vh,g,c,wq,wz,wh,beta,Rs,Rl,Rq,Rh,Fs,Fl,Fh,Fp=s.symbols('q z h vq vz vh g c wq wz wh beta Rs Rl Rq Rh Fs Fl Fh Fp',real=True)
# Completed square keeps conservative coupling storage bounded below for positive stiffness/beta/c.
U=(vq**2+vz**2+vh**2+wq**2*q**2+wh**2*h**2+wz**2*(z+g*q*q/wz**2)**2)/2+beta*q**4/4+c*q*q*h*h/2
coords=s.Matrix([q,z,h]);vel=s.Matrix([vq,vz,vh]);grad=s.Matrix([s.diff(U,i) for i in coords])
forces=s.Matrix([Fh,Fs+Fl,Fp]);loss=s.diag(Rq,Rs+Rl,Rh)
acc=forces-grad-loss*vel
flow=sum(s.diff(U,i)*j for i,j in zip(coords,vel))+sum(s.diff(U,i)*j for i,j in zip(vel,acc))
eq('reciprocal three-coordinate ledger',flow,forces.dot(vel)-vel.dot(loss*vel))
eq('cavity quadratic drive',grad[1],wz*wz*z+g*q*q)
eq('half-mode backreaction',grad[0],wq*wq*q+2*g*q*z+2*g*g*q**3/wz**2+beta*q**3+c*q*h*h)
eq('no spontaneous half mode from exact zero',acc[0].subs({q:0,vq:0,Fh:0}),0)
# This is an invariant solution, not a proof of stability or absence of subharmonics.
t,amp,phase,omega=s.symbols('t amp phase omega',real=True)
eq('half-mode DC and doubled force',s.expand_trig(s.cos(t+phase)**2),(1+s.cos(2*t+2*phase))/2)
eq('nominal half frequency',2*s.Rational(783,200),s.Rational(783,100))
eq('nominal carrier mismatch',7800-2000*s.Rational(783,200),-30)
# Same fixed source resistance; arbitrary complex independent natural and half-mode RMS force.
f1,f2,p1,p2=s.symbols('f1 f2 p1 p2',real=True)
fn=f1+s.I*f2; fp=p1+s.I*p2; speed=(fn+fp)/2
load=s.Abs(speed)**2; half=s.re(s.conjugate(fp)*speed); natural=s.re(s.conjugate(fn)*speed)
eq('matched two-force ledger',natural+half,2*load)
eq('net paid half-mode cannot improve fixed-port optimum',load-half,(s.Abs(fn)**2-s.Abs(fp)**2)/4)
for name,f,p in [('A',0,0),('B',0,1),('C',1,0),('D',1,1),('D_antiphase',1,-1)]:
    sub={f1:f,f2:0,p1:p,p2:0}
    print(name, 'natural',natural.subs(sub),'half_work',half.subs(sub),'load',load.subs(sub),'net',(load-half).subs(sub))
print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')
