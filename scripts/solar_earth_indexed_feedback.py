"""Conditional causal vector cell with indexed time refinement; normalized units."""
import json
import numpy as np
from solar_earth_thermal_vector import sideband


def run(k, source=True, control=True):
    h=2.**(-k); x=np.zeros(7); history=[x.copy()]; ledger=np.zeros(4)
    J=np.array([[0.,-1.,0.],[1.,0.,0.],[0.,0.,0.]])
    for i in range(2**k):
        t=(i+.5)*h; p=(1+np.cos(2*np.pi*t))*.1 if control else 0.
        theta=(x[6]+h*(p-x[6]/2))/(1+h/2)
        nu=1+(theta+x[6])/2
        A=np.block([[-2*np.eye(3),-np.eye(3)],[np.eye(3),-nu*np.eye(3)-3*J]])
        a=np.array([1.,0.,0.]) if source else np.zeros(3)
        f=np.r_[2*a,np.zeros(3)]
        y=np.linalg.solve(np.eye(6)-h*A/2,(np.eye(6)+h*A/2)@x[:6]+h*f)
        E,j=(y+x[:6]).reshape(2,3)/2
        w=h*np.array([a@a,(E-a)@(E-a),nu*(j@j),E@E])
        assert abs((y@y-x[:6]@x[:6])/2-w[0]+sum(w[1:]))<1e-12
        ledger+=w; x=np.r_[y,theta]; history.append(x.copy())
    return np.array(history),ledger


def fixtures():
    rows=[]
    for k in (3,4,5,6):
        coarse,w=run(k); fine,v=run(k+1)
        rho=fine[::2]-coarse
        assert np.array_equal(coarse+rho,fine[::2]) or np.allclose(coarse+rho,fine[::2])
        assert np.linalg.norm(rho)>0
        for source in (False,True):
            for control in (False,True):
                x,L=run(k,source,control)
                assert abs(x[-1,:6]@x[-1,:6]/2-L[0]+sum(L[1:]))<1e-12
                if not source: assert np.all(x[:,:6]==0)
        rows.append(dict(k=k,dt=2.**(-k),signed_endpoint_residual=rho[-1].tolist(),max_residual=float(np.max(np.abs(rho)))))
    assert all(a['max_residual']>b['max_residual'] for a,b in zip(rows,rows[1:]))
    print(json.dumps(dict(rows=rows,worlds=16,physical_admission=False,scope='time refinement only; finite vector cell; thermal input not converted to hardware cost; no restored cycle or spherical transport'),indent=2))
if __name__=='__main__': fixtures()
