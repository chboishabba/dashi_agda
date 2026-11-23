"""Finite prescribed-permittivity Maxwell-ADE midpoint; synthetic only."""
import sympy as S
from smith_filsinger_lorentz_ade_sympy import generator, energy, LorentzMaterial


def transition(n, material, eps1, dt, curl=None, load=0):
    """Endpoint E chart; total D=eps*E+P. Returns state and source maps."""
    eps1, dt = map(S.sympify, (eps1, dt))
    if eps1.is_positive is not True or dt.is_positive is not True:
        raise ValueError('positive endpoint epsilon and timestep required')
    A, B, mass0 = generator(n, material, curl, load)
    M0 = S.diag(*([material.eps]*n+[material.mu]*n+[1]*(2*n)))
    M1 = S.diag(*([eps1]*n+[material.mu]*n+[1]*(2*n)))
    K = M0*A
    L = M1-dt*K/2
    mass1 = mass0.copy()
    mass1[:n,:n] = eps1*S.eye(n)
    return L.inv()*(M0+dt*K/2), L.inv()*dt*M0*B, mass0, mass1


def step(z, jn, jc, material, eps1, dt, curl=None, load=0):
    n = jn.rows
    if jn.shape != (n,1) or jc.shape != (n,1) or z.shape != (4*n,1):
        raise ValueError('state/source dimensions')
    dt, eps1, load = map(S.sympify, (dt, eps1, load))
    A,B,M0,M1 = transition(n,material,eps1,dt,curl,load)
    z1 = A*z+B*(jn+jc)
    e0,e1 = z[:n,:],z1[:n,:]
    mid = (z+z1)/2
    e,v = mid[:n,:],mid[3*n:,:]
    dot = lambda a,b: (a.T*b)[0]
    wmod = -(eps1-material.eps)*dot(e0,e1)/2
    wn,wc = dt*dot(e,jn),dt*dot(e,jc)
    loss = dt*material.sigma*dot(e,e)
    relax = dt*material.gamma/material.alpha*dot(v,v)
    useful = dt*load*dot(e,e)
    delta = energy(z1,M1)-energy(z,M0)
    residual = S.simplify(delta+loss+relax+useful-wn-wc-wmod)
    return dict(z=z1, initial_state=z, displacement=eps1*e1+z1[2*n:3*n,:],
                storage_delta=delta,natural_work=wn,controller_work=wc,
                modulation_work=wmod,ohmic=loss,relaxation=relax,useful_load=useful,
                residual=residual)


def green(maps, i, j):
    """Response at endpoint i to source on interval j; no future sources."""
    if not (0 <= i <= len(maps) and 0 <= j < len(maps)):
        raise IndexError('time index')
    A,B = maps[j]
    if i <= j:
        return S.zeros(*B.shape)
    out = B
    for k in range(j+1,i):
        out = maps[k][0]*out
    return out
