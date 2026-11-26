"""AV selected-source controls: full complex Gram, density and UV residuals."""
import sympy as s
import numpy as np


def exact():
    a,b,c,d,e,f,g,h=s.symbols('a b c d e f g h',real=True)
    A=s.Matrix([[a+s.I*b,c+s.I*d],[e+s.I*f,g+s.I*h]])
    psi=s.Matrix([1,1]); v=A*psi
    w=(psi.conjugate().T*A.conjugate().T*A*psi)[0]/2
    assert s.expand(w-sum(s.re(x)**2+s.im(x)**2 for x in v)/2)==0
    X=s.Matrix([[0,1],[1,0]]); Z=s.diag(1,-1)
    assert X*Z!=Z*X and (psi.T*Z*X*Z*psi)[0]==-2
    B=s.Matrix([[1,-1],[0,0]])
    assert B!=s.zeros(2) and B*psi==s.zeros(2,1)
    u=s.Matrix([a+s.I*b,c+s.I*d]); v=s.Matrix([e+s.I*f,g+s.I*h])
    norm=lambda z:s.expand((z.conjugate().T*z)[0])
    inner=(u.conjugate().T*v)[0]
    assert s.expand(norm(u+v)-norm(u-v)-4*s.re(inner))==0
    assert s.expand(norm(u+s.I*v)-norm(u-s.I*v)+4*s.im(inner))==0
    rho,x,y,z,V=s.symbols('rho x y z V',positive=True)
    H=s.diag(-rho,x,y,z); volume=s.sqrt(-H.det()); gi=H/volume
    assert s.simplify(s.sqrt(-gi.inv().det())-volume)==0
    assert s.simplify(volume*gi-H)==s.zeros(4)
    assert s.simplify(volume*(V/volume)-V)==0
    # Layered positive conductivity: flux and average derivative.
    k1,k2,p=s.symbols('k1 k2 p',positive=True)
    ke=1/(p/k1+(1-p)/k2)
    assert s.factor(p*ke/k1+(1-p)*ke/k2-1)==0
    print('PASS complex forward state/quotient, both polarization signs, metric density and layered corrector identities')


def uv():
    # Normalized flat momentum vector = single-site excitation in the
    # chosen normal-mode Fock chart. Distinct from the old local product vacuum.
    c=np.array([1.5,1.,.75]); mu=.7; sin=np.sin(np.linspace(-np.pi,np.pi,64,endpoint=False)/2)**2
    S=sum(4*c[j]**2*sin.reshape(tuple(64 if i==j else 1 for i in range(3))) for j in range(3))
    for a in (1/8,1/16,1/32,1/64):
        omega=np.sqrt(mu**2+S/a**2); E=omega.mean(); lower=4*c[0]/(np.pi*a)
        assert E>=lower
        print('site packet',a,'energy',E,'aE',a*E,'lower',lower)
    # Three independent smooth fixed-scale packet samples. Project to
    # nested momentum windows, orthonormalize by inverse Gram square root.
    p=np.linspace(-10,10,401); dp=p[1]-p[0]
    F=np.stack([np.exp(-p*p/2),p*np.exp(-p*p/2),np.exp(-(p-2)**2/2)],axis=1).astype(complex)
    def whiten(A):
        G=A.conj().T@A*dp; d,U=np.linalg.eigh(G)
        assert min(d)>0
        return A@((U*d**(-.5))@U.conj().T)
    F=whiten(F); omega=np.sqrt(mu**2+c[0]**2*p*p)
    for B in (2,3,4,6):
        Fa=whiten(F*(abs(p)<=B)[:,None]); gram=Fa.conj().T@Fa*dp
        assert np.max(abs(gram-np.eye(3)))<1e-12
        energy=np.real(np.sum(abs(Fa)**2*omega[:,None],axis=0)*dp)
        # Independent original 3/5,4/5 record per orthonormal mode.
        coeff=np.array([.6,.8]); state=np.kron(np.kron(coeff,coeff),coeff)
        assert abs(np.vdot(state,state)-1)<1e-14 and abs(state[0]-.6**3)<1e-14
        err=np.linalg.norm(Fa-F)*np.sqrt(dp)
        print('smeared packet window',B,'gram error',np.max(abs(gram-np.eye(3))),'packet error',err,'branch energy',.64*sum(energy))
    print('PASS selected flat-packet UV scaling and smeared finite Gram/energy controls')


if __name__=='__main__':
    exact(); uv()
