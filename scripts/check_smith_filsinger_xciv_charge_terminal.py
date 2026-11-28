"""XCIV exact charge/port weld and numerical coupled transient. Synthetic only.
J31 equations transcribed at blob 47493fbefba44c20e7cb82e31521627f13611800.
New feedback system, not original prescribed-source J36 or actual apparatus.
"""
import json
import sympy as S
import numpy as np
from scipy.integrate import solve_ivp
Q=S.Rational
EDGES=[(1,4),(2,5),(0,1),(1,2),(3,4),(4,5),(0,3)]
D=S.Matrix([[1,0,1,0,-1,0,-1],[-1,1,0,1,0,-1,0]])
G=S.zeros(7,6)
for i,(a,b) in enumerate(EDGES):G[i,a]=-1;G[i,b]=1
C=D[:,:2].T; L=D[:,2:4]

def exact():
    assert D*G==S.zeros(2,6)
    h=S.Matrix(S.symbols('h:2',real=True)); j=S.Matrix(S.symbols('j:4',real=True))
    # d=(2E+P,Cb eb,0) oriented edge displacement; clamped edges have
    # reaction current D_inactive^T H, zero effort and zero work.
    J=j.col_join(D[:,4:].T*h); ddot=D.T*h-J
    assert ddot[4:,:]==S.zeros(3,1)
    assert G.T*ddot==-G.T*J
    assert S.ones(1,6)*G.T==S.zeros(1,7)
    assert (G.T*D[:,:].T)==S.zeros(6,2)
    assert G[:4,:].rank()==4
    E=S.Matrix(S.symbols('E:2',real=True)); eb=S.Matrix(S.symbols('bE:2',real=True)); pol=S.Matrix(S.symbols('P:2',real=True)); vel=S.Matrix(S.symbols('V:2',real=True))
    i,j,u,v,b,q,r,ih,x=S.symbols('i j u v b q r ih x',real=True)
    z=S.Matrix([i,j,u,v,b,q,r,ih,x]); w=S.Matrix([q,r]); beta=S.symbols('beta',real=True); rad=S.sqrt(Q(3,100)); t=beta*E
    a=(t+rad*w)/2; out=(t-rad*w)/2; current=beta*rad*w
    assert S.expand(a.dot(a)-out.dot(out)-E.dot(current))==0
    assert (a+out)==t and (a-out)==rad*w
    # Source-owner J31 masses, capacitive-return branch, gamma split from J21.
    Mi=S.Matrix([[2,Q(3,5)],[Q(3,5),Q(3,2)]]); Me=S.Matrix([[Q(7,5),-1],[-1,Q(31,20)]])
    W=(S.Matrix([i,j]).T*Mi*S.Matrix([i,j]))[0]/2+(S.Matrix([u,v]).T*Me*S.Matrix([u,v]))[0]/2+Q(13,40)*b*b+q*q+r*r+Q(3,40)*ih*ih+Q(3,25)*(x*x/2+Q(3,8)*x**4)
    rows=[]
    for U,V,chi in [(0,0,1),(0,1,1),(0,1,0),(1,1,1),(1,0,1),(0,0,0),(1,0,0),(1,1,0)]:
        ju=U*(u-b-Q(1,10))/Q(3,25); jv=V*(v-b-Q(1,10))/Q(3,25)
        f=Mi.inv()*S.Matrix([-Q(35,100)*i,u-v-Q(28,100)*j]); f=f.col_join(Me.inv()*S.Matrix([-j-ju+Q(35,100)*q+2*ih,j-jv])); f=f.col_join(S.Matrix([(ju+jv-Q(18,1000)*b-chi*ih)/Q(65,100),Q(11,10)*r-Q(152,10000)*q-Q(35,100)*u/2+rad*a[0],-Q(11,10)*q-Q(152,10000)*r+rad*a[1],(chi*b-x-(Q(5,100)+chi*Q(9,100))*ih-2*u)/Q(15,100),(ih-Q(52,100)*x)/(Q(12,100)*(1+Q(3,2)*x*x))]))
        loss=Q(35,100)*i*i+Q(28,100)*j*j+Q(1,10)*(ju+jv)+Q(3,25)*(ju*ju+jv*jv)+Q(18,1000)*b*b+Q(4,10000)*w.dot(w)+(Q(5,100)+chi*Q(9,100))*ih*ih+Q(52,100)*x*x
        assert S.factor((S.Matrix([W]).jacobian(z)*f)[0]-E.dot(current)+loss)==0
        rows.append([U,V,chi])
    # Maxwell port: incoming power normalised, two retained external wave channels.
    Y=S.diag(Q(1,10),1000); root=S.diag(S.sqrt(Q(1,10)),S.sqrt(1000)); A=S.Matrix(S.symbols('a:2',real=True)); outM=root*E-A
    edot=(C*h-Q(1,5)*E-vel+2*root*A-Y*E-current)/2
    hdot=(-C.T*E-L*eb)/Q(3,2); ebdot=(L.T*h-Q(20,9)*eb)/Q(1,10)
    vdot=Q(3,2)*E-Q(2,3)*vel-4*pol
    wm=2*E.dot(edot)+Q(3,2)*h.dot(hdot)+Q(8,3)*pol.dot(vel)+Q(2,3)*vel.dot(vdot)+Q(1,10)*eb.dot(ebdot)
    assert S.expand(wm-(A.dot(A)-outM.dot(outM)-Q(1,5)*E.dot(E)-Q(4,9)*vel.dot(vel)-Q(20,9)*eb.dot(eb)-E.dot(current)))==0
    # An uncoupled clamped edge current must not disappear from charge ledger.
    assert G[4:,:].T*D[:,4:].T!=S.zeros(6,2)
    return dict(all_8_mode_power_identities=True,mode_rows=rows,exact_charge_continuity=True,clamp_reaction_necessary=True,active_gradient_rank=4,charge_total_zero=True,port_forward_inverse=True,exact_maxwell_power=True,source_owner_blob='47493fbefba44c20e7cb82e31521627f13611800',source_equations_transcribed_not_byte_imported=True)

def run(beta,periods=10,source_on=True,y1=1000.):
    # same XCIII power-normalised rectangular source, forward delay and mixer;
    # no direct Maxwell terminal resistor, no independent J31 incident source.
    Cn=np.array(C,dtype=float); root=np.sqrt([.1,y1]); Y=root**2; rad=np.sqrt(.03)
    Mi=np.linalg.inv([[2,.6],[.6,1.5]]);Me=np.linalg.inv([[1.4,-1],[-1,1.55]])
    def energy(z):
        e,h,p,v,eb=z[:2],z[2:4],z[4:6],z[6:8],z[8:10];i,j,u,vv,b,q,r,ih,x=z[10:19]
        return e@e+.75*(h@h)+4/3*(p@p)+(v@v)/3+.05*(eb@eb)+.5*np.array([i,j])@np.array([[2,.6],[.6,1.5]])@np.array([i,j])+.5*np.array([u,vv])@np.array([[1.4,-1],[-1,1.55]])@np.array([u,vv])+.325*b*b+q*q+r*r+.075*ih*ih+.12*(.5*x*x+.375*x**4)
    y=np.zeros(26); on=False; events=[];time=0.; revstore=0.
    for k in range(4*periods):
        a=np.array([0.,float(source_on and k%4==2)]); stop=(k+1)*.1
        def rhs(t,z):
            e,h,p,vel,eb=z[:2],z[2:4],z[4:6],z[6:8],z[8:10];i,j,u,v,b,q,r,ih,x=z[10:19]
            w=np.array([q,r]); current=beta*rad*w; out=root*e-a; ju=max((u-b-.1)/.12,0);jv=max((v-b-.1)/.12,0)
            m=np.r_[(Cn@h-.2*e-vel+2*root*a-Y*e-current)/2,(-Cn.T@e-eb)/1.5,vel,1.5*e-2/3*vel-4*p,(h-20/9*eb)/.1]
            c=np.r_[Mi@[-.35*i,u-v-.28*j],Me@[-j-ju+.35*q+2*ih,j-jv],(ju+jv-.018*b-on*ih)/.65,1.1*r-.0002*q-.175*u+rad*beta*e[0]/2,-1.1*q-.0002*r+rad*beta*e[1]/2,(on*b-x-(.05+.09*on)*ih-2*u)/.15,(ih-.52*x)/(.12*(1+1.5*x*x))]
            ml=.2*(e@e)+4/9*(vel@vel)+20/9*(eb@eb);cl=.35*i*i+.28*j*j+.1*(ju+jv)+.12*(ju*ju+jv*jv)+.018*b*b+.0004*(w@w)+(.05+.09*on)*ih*ih
            return np.r_[m,c,a@a,out@out,.52*x*x,ml,cl,e@current,((out[0]+out[1])/np.sqrt(2))**2]
        start_reverse=y[25]
        while time<stop-1e-12:
            def event(t,z):return z[14]-(.0018 if on else .006)
            event.terminal=True;event.direction=-1 if on else 1
            sol=solve_ivp(rhs,(time,stop),y,method='Radau',rtol=2e-8,atol=2e-10,events=event)
            assert sol.success; y=sol.y[:,-1];time=sol.t[-1]
            if len(sol.t_events[0]):on=not on;events.append([float(time),bool(on)])
            else:break
            assert len(events)<500
        revstore=y[25]-start_reverse
    inc,ref,load,ml,cl,transfer,_=y[19:];stored=energy(y);external_ref=ref-revstore
    residual=inc-external_ref-load-ml-cl-stored-revstore
    assert abs(residual)<2e-7
    if not source_on:assert np.max(np.abs(y))==0
    return dict(beta=beta,Y1=y1,periods=periods,source_on=source_on,incident=float(inc),external_reflected=float(external_ref),hf_load=float(load),maxwell_losses=float(ml),circuit_losses=float(cl),signed_interface_work=float(transfer),receiver_storage=float(stored),return_delay_storage=float(revstore),residual=float(residual),transient_load_over_incident=float(load/inc) if inc else None,spark_events=events,restored_claim=False)

if __name__=='__main__':
    print(json.dumps(dict(status='PASS_EXACT_CONDITIONAL_WELD_AND_NUMERICAL_TRANSIENT',exact=exact(),runs=[run(b) for b in (1,10,50,100)]+[run(b,y1=y) for y in (1.,10.,100.) for b in (1,10,50)]+[run(10,1,False)],physical_admission=False,J36_periodic_certificate=False,J37_coupled_periodic_certificate=False),indent=2))
