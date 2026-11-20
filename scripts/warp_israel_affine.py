"""Forced Israel receiver offsets; source and trace compatibility stay separate."""
import numpy as np

def radial_source_at_receiver(src, amplitude, rx, eps, dr):
    ir=int(rx/dr); idx=np.arange(ir-1,ir+3)
    if rx<=0 or eps<=0 or dr<=0 or idx[0]<0 or idx[-1]>=src.shape[-1]-1:
        raise ValueError('active receiver stencil')
    V=(idx-rx/dr)[None,:]**np.arange(4)[:,None]
    w=np.linalg.solve(V,[1.,0.,0.,0.])
    return amplitude*(rx/eps)**np.arange(0,6,2)*(src[:,idx]@w)

def offsets(g):
    g=np.asarray(g); out=np.zeros((6,)+g.shape);out[4]=-g
    return out

def forced_identity(values,g,t):
    gamma=1/t+1/(2*t**3);beta=1/(3*t*t)
    terms=np.stack((values[2],-values[3],gamma*values[4],beta*values[5],gamma*g))
    return terms.sum(0),np.abs(terms).sum(0)

def check():
    import sympy as s
    p,m,v,g,dy,D=s.symbols('p m v g dy D')
    A=((1+v)*p+(1-v)*m)/2; Dc=(p-m)/2
    Fc=v*A+(1-v*v)*Dc; target=(2*g-(1+v)*p)/(v-1)
    assert s.simplify(Fc.subs(m,target)-g)==0
    assert s.simplify(2*(1-v)*(target-m)/dy-4*(Fc-g)/dy)==0
    assert s.simplify(v*A+(1-v*v)*D-g-(Fc-g)-(1-v*v)*(D-Dc))==0
    print('PASS exact characteristic target, SAT sign and trace split')
    src=np.zeros((3,13));src[:,2:5]=np.array([[1,-2,3],[2,1,-1],[-1,3,2]])
    t=2.;g=radial_source_at_receiver(src,.013,.025,.04,.008)
    assert np.all(g!=0)
    vals=np.zeros((6,3))+offsets(g)
    err,scale=forced_identity(vals,g,t)
    np.testing.assert_array_equal(err,0)
    wrong=vals[2]-vals[3]+(1/t+1/(2*t**3))*vals[4]+vals[5]/(3*t*t)
    assert np.all(wrong!=0)
    assert not np.any(radial_source_at_receiver(src,.013,.073,.04,.008))
    print('PASS nonzero affine offset, omitted-offset negative control, exterior support',g)
if __name__=='__main__':check()
