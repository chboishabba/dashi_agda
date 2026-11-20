import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import spsolve
# finite 2D cross-section; two scalar channels, same e1 source/probe
# fixed affine far boundary approximates ambient gradient; not physical GR

def run(n,k,angle):
    x=np.linspace(-3,3,n); h=x[1]-x[0]; N=n*n; rows=[];cols=[];vals=[]; rhs=np.zeros(2*N)
    R=lambda t:np.array([[np.cos(t),-np.sin(t)],[np.sin(t),np.cos(t)]])
    def mat(a,b):
        if abs(a)<1 and abs(b)<.35:
            r=R(angle if a<0 else -angle/2); return r@np.diag([k,1.])@r.T
        return np.eye(2)
    def add(i,j,A):
        for a in range(2):
            for b in range(2): rows.append(2*i+a);cols.append(2*j+b);vals.append(A[a,b])
    for i,z in enumerate(x):
        for j,y in enumerate(x):
            p=i*n+j
            if i in (0,n-1) or j in (0,n-1):
                add(p,p,np.eye(2));rhs[2*p]=z;continue
            for di,dj in ((1,0),(-1,0),(0,1),(0,-1)):
                l,m=i+di,j+dj; q=l*n+m; A=mat((y+x[m])/2,(z+x[l])/2)
                add(p,p,A)
                if l in (0,n-1) or m in (0,n-1):rhs[2*p:2*p+2]+=A@np.array([x[l],0])
                else:add(p,q,-A)
    K=coo_matrix((vals,(rows,cols)),shape=(2*N,2*N)).tocsr(); u=spsolve(K,rhs).reshape(n,n,2)
    assert np.max(abs(K@u.ravel()-rhs))<1e-8
    i=np.argmin(abs(x-1));j=n//2
    return (u[i+1,j]-u[i-1,j])/(2*h)
if __name__=='__main__':
    for n in (61,121):
        for k in (.01,.1,1,10,100):
            g=run(n,k,np.pi/4);print(n,k,*g,'total',.75+.25*g[0],flush=True)

# Exact rank-one Green resolvent: a localized auxiliary mode couples to the
# gradient of a scalar in a disk. Same scalar source/probe, no channel relabel.
# Continuum 2D Dirichlet box, finite difference energy, localized dipole profile.
def collective(n,angle):
    from scipy.sparse import diags,kron,eye
    from scipy.sparse.linalg import splu
    x=np.linspace(-3,3,n); h=x[1]-x[0]; a=x[1:-1]; m=len(a)
    D=diags([-np.ones(m-1),2*np.ones(m),-np.ones(m-1)],[-1,0,1]); L=(kron(D,eye(m))+kron(eye(m),D)).tocsc()
    Y,Z=np.meshgrid(a,a); f=np.exp(-((Y-.45)**2+(Z+.15)**2)/.12)
    # gradient coupling -X integral w n.grad(phi); b=-div(w n)
    b=2/.12*f*(np.cos(angle)*(Y-.45)+np.sin(angle)*(Z+.15))*h*h
    b=b.ravel(); lu=splu(L); v=lu.solve(b); S=b@v; ambient=Z.ravel(); B=b@ambient
    i=np.argmin(abs(a-1));j=np.argmin(abs(a)); probe=(v.reshape(m,m)[i+1,j]-v.reshape(m,m)[i-1,j])/(2*h)
    # x= B/(mu-S) with unit vertex; response=1+probe*x.
    return S,B,probe
if __name__=='__main__':
    for n in (61,121,241):
        for angle in np.linspace(0,np.pi,9):
            S,B,P=collective(n,angle); a=B*P
            if abs(a)<1e-12:continue
            target=5 if a>0 else -3
            mu=S+a/(target-1)
            assert mu>S
            val=1+a/(mu-S)
            assert abs(val-target)<1e-9
            print('collective inverse',n,angle,'S',S,'B',B,'probe',P,'mu',mu,'margin',(mu-S)/S,'response',val)
    for ang,target in [(np.pi/8,5),(5*np.pi/8,-3)]:
        S,B,P=collective(241,ang); mu=S+B*P/(target-1)
        for n in (121,241,481):
            s,b,p=collective(n,ang); assert mu>s
            print('fixed curvature refinement',n,ang,mu,s,1+b*p/(mu-s),(mu-s)/s,flush=True)

# Continuum Dirichlet sine Green expansion on the same square, independent
# of the finite difference inverse. Gauss-Legendre quadrature for projections.
def spectral(m,angle):
    from scipy.special import roots_legendre
    nodes,w=roots_legendre(max(256,4*m)); x=3*nodes; w=3*w
    k=np.pi*np.arange(1,m+1)/6
    basis=np.sin(k[:,None]*(x+3))/np.sqrt(3)
    fy=np.exp(-(x-.45)**2/.12); fz=np.exp(-(x+.15)**2/.12)
    y=basis@(w*fy); z=basis@(w*fz)
    dy=basis@(w*fy*2*(x-.45)/.12); dz=basis@(w*fz*2*(x+.15)/.12)
    b=np.cos(angle)*np.outer(z,dy)+np.sin(angle)*np.outer(dz,y)
    G=b/(k[:,None]**2+k[None,:]**2)
    S=np.sum(b*G)
    B=np.cos(angle)*np.sum(w*fy*2*(x-.45)/.12)*np.sum(w*fz*x)+np.sin(angle)*np.sum(w*fy)*np.sum(w*fz*2*(x+.15)/.12*x)
    P=(k*np.cos(k*4)/np.sqrt(3))@G@(np.sin(k*3)/np.sqrt(3))
    return S,B,P
if __name__=='__main__':
    for ang,target in [(np.pi/8,5),(5*np.pi/8,-3)]:
        S,B,P=collective(241,ang); mu=S+B*P/(target-1)
        for m in (16,32,64,128):
            s,b,p=spectral(m,ang); assert mu>s
            inv=s+b*p/(target-1)
            print('continuum spectral',m,ang,'S B P',s,b,p,'fixed response',1+b*p/(mu-s),'inverse mu',inv,'margin',(inv-s)/s,flush=True)
