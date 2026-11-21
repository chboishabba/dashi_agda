"""OCT369 P0.32: Bloch basis/accounting adapter, not a new physics formula.

Physical inputs: direct basis B (Cartesian length per integer cell), fractional
orbital positions r_a, integer bond translations R, same-basis hopping T_ab.
For p_cart = 2*pi*B^{-T} k_frac, W_a=exp(i p_cart.dot(B r_a)).
If H_cell=W H_embed W^dagger, the physical Cartesian momentum derivative is
D_i H_cell = partial_{p_i} H_cell - i [X_i,H_cell], X_i=diag((B r_a)_i).
All physical spin/orbital operators must be transported by the same W.
Ordinary k-derivatives are not physical velocities after k-dependent rephasing.
Prior art: Bloch/Wannier geometry; original DASHI crystal and P0.29/P0.31.
"""
import numpy as np


def bracket(a,b):
    return a@b-b@a


def site_position_operators(basis, sites_frac, multiplicity=2):
    positions=np.asarray(sites_frac,float)@np.asarray(basis,float).T
    return np.array([np.diag(np.repeat(positions[:,i],multiplicity)).astype(complex) for i in range(3)])


def embedding_unitary(k_frac, sites_frac, multiplicity=2):
    phases=np.exp(2j*np.pi*(np.asarray(sites_frac,float)@np.asarray(k_frac,float)))
    return np.diag(np.repeat(phases,multiplicity)).astype(complex)


def physical_cell_jets(h, dh, ddh, position_ops):
    """Covariant physical p-derivatives of a cell-gauge Hamiltonian.

    dh,ddh MUST already be derivatives with respect to physical CARTESIAN p,
    not fractional k (multiply derivative by B/(2pi) first). Fixed X gauge.
    """
    x=np.asarray(position_ops)
    out=np.empty_like(dh)
    hess=np.empty_like(ddh)
    for i in range(3):
        out[i]=dh[i]-1j*bracket(x[i],h)
        for j in range(3):
            hess[i,j]=(ddh[i,j]-1j*bracket(x[i],dh[j])
                 -1j*bracket(x[j],dh[i])-bracket(x[i],bracket(x[j],h)))
    return out,hess


def direct_reciprocal_relabel(basis, new_cell_axes, sites_frac, translations, k_frac):
    """Re-express same physical sites/bonds using B'=B U, U in GL(3,Z)."""
    b=np.asarray(basis,float);u=np.asarray(new_cell_axes,float)
    inv=np.linalg.inv(u)
    return b@u, np.asarray(sites_frac)@inv.T, np.asarray(translations)@inv.T, u.T@np.asarray(k_frac)
