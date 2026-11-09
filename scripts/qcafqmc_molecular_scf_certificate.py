#!/usr/bin/env python3
"""Same-source molecular Hartree-Fock / Roothaan admission certificate.

This does NOT invent another HF solver. It checks an existing solver's
converged MO coefficients, AO overlap and Fock matrix and correctly
transformed one- and two-electron integrals.

Reuses DASHI/Physics/Chemistry/AtomicPeriodicTable369HeliumHartreeConvergenceExact
for the pre-existing helium RHF-equivalent evidence. General multi-centre
molecular SCF execution is delegated to source-labelled PySCF.

In a real AO basis the fixed-point equations are C^T S C=I, F C=S C eps,
Tr[D S]=N and h_MO=C^T h_AO C. ERI AO->MO is optional and only tractable
for small full bases (or selected four-index blocks).
"""
import json
import numpy as np

class SCFIdentityError(ValueError):
    pass

def verify_molecular_scf(C,S,F,eigenvalues,density,hcore,nelec,
                         hmo=None,eri_ao=None,eri_mo=None,
                         tolerance=1e-6):
    C=np.asarray(C,dtype=float)
    if C.ndim!=2 or C.shape[0]!=C.shape[1]:
        raise SCFIdentityError("requires a full square molecular-orbital frame")
    n=C.shape[0]
    S=np.asarray(S,dtype=float)
    F=np.asarray(F,dtype=float)
    D=np.asarray(density,dtype=float)
    h=np.asarray(hcore,dtype=float)
    eigenvalues=np.asarray(eigenvalues,dtype=float)
    if any(x.shape!=(n,n) for x in (S,F,D,h)) or eigenvalues.shape!=(n,):
        raise SCFIdentityError("incompatible AO/MO dimensions")
    if not all(np.isfinite(x).all() for x in (C,S,F,D,h,eigenvalues)):
        raise SCFIdentityError("nonfinite SCF data")
    if any(not np.allclose(x,x.T,rtol=0,atol=tolerance) for x in (S,F,D,h)):
        raise SCFIdentityError("non-symmetric AO matrix")
    if np.linalg.eigvalsh(S)[0]<=0:
        raise SCFIdentityError("AO overlap not positive definite")
    norm_orth=np.linalg.norm(C.T@S@C-np.eye(n),ord="fro")
    norm_roothaan=np.linalg.norm(F@C-S@C@np.diag(eigenvalues),ord="fro")
    electron=float(np.trace(D@S))
    if norm_orth>tolerance or norm_roothaan>tolerance:
        raise SCFIdentityError("RHF orthonormality or Roothaan eigenproblem failed")
    if abs(electron-nelec)>tolerance:
        raise SCFIdentityError("molecular electron count differs from source sector")
    result={"nbasis":n,
            "mo_orthonormality_residual":float(norm_orth),
            "roothaan_residual":float(norm_roothaan),
            "electron_trace":electron,
            "requested_electrons":int(nelec),
            "source_existing_atomic_HF":
              "scripts/atomic_helium_hartree_scf.py (one-orbital RHF-equivalent)",
            "fresh_HF_solver_implemented":False}
    if hmo is not None:
        hmo=np.asarray(hmo)
        if hmo.shape!=(n,n):raise SCFIdentityError("hmo shape")
        diff=np.linalg.norm(hmo-C.T@h@C,ord="fro")
        if diff>tolerance:raise SCFIdentityError("one-electron AO/MO mismatch")
        result["one_electron_transform_residual"]=float(diff)
    if (eri_ao is None)!=(eri_mo is None):
        raise SCFIdentityError("both AO and MO two-electron tensors required")
    if eri_ao is not None:
        if n>8:raise SCFIdentityError("full AO ERI cross-check only for <=8 orbitals")
        ao=np.asarray(eri_ao);mo=np.asarray(eri_mo)
        if ao.shape!=(n,)*4 or mo.shape!=(n,)*4:
            raise SCFIdentityError("ERI shape")
        expected=np.einsum("up,vq,wr,xs,uvwx->pqrs",
                           C,C,C,C,ao,optimize=True)
        diff=np.linalg.norm(mo-expected)
        if diff>tolerance:raise SCFIdentityError("two-electron AO/MO mismatch")
        result["two_electron_transform_residual"]=float(diff)
    return result

def from_pyscf_restricted(mol,mf,tolerance=1e-5):
    """Verify the completed, restricted converged SCF, not rerun Hartree-Fock."""
    if not mf.converged:raise SCFIdentityError("RHF not converged")
    if getattr(mol,"spin",None)!=0:raise SCFIdentityError("restricted singlet only")
    C=np.asarray(mf.mo_coeff)
    if C.ndim!=2 or C.shape[0]!=C.shape[1]:
        raise SCFIdentityError("linear-dependence-truncated MO frame needs dedicated handling")
    S=mf.get_ovlp()
    D=mf.make_rdm1()
    F=mf.get_fock(dm=D)
    return verify_molecular_scf(C,S,F,mf.mo_energy,D,mf.get_hcore(),
                                mol.nelectron,tolerance=tolerance)

def self_test():
    rng=np.random.default_rng(1011)
    A=rng.normal(size=(3,3))
    S=A.T@A+np.eye(3)
    w,v=np.linalg.eigh(S)
    inverse_sqrt=(v*(w**-.5))@v.T
    Q,_=np.linalg.qr(rng.normal(size=(3,3)))
    C=inverse_sqrt@Q
    eps=np.array([-1.2,-.4,.7])
    F=S@C@np.diag(eps)@C.T@S
    D=2*np.outer(C[:,0],C[:,0])
    h=F.copy()
    eri=np.zeros((3,3,3,3))
    hmo=C.T@h@C
    moeri=np.einsum("up,vq,wr,xs,uvwx->pqrs",C,C,C,C,eri,optimize=True)
    positive=verify_molecular_scf(C,S,F,eps,D,h,2,hmo,eri,moeri)
    assert positive["mo_orthonormality_residual"]<1e-12
    assert positive["roothaan_residual"]<1e-12
    try:verify_molecular_scf(C[:,::-1],S,F,eps,D,h,2,hmo,eri,moeri)
    except SCFIdentityError:negative=True
    else:raise AssertionError("incorrect orbital frame accepted")
    return {"positive":positive,"wrong_orbital_order_rejected":negative,
            "real_molecular_pyscf_computation_executed":False}

if __name__=="__main__":
    print(json.dumps(self_test(),indent=2))
