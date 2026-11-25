"""Unbounded rational Conway action via certified per-atom CRT limbs.

Source: Martin Seysen mm_crt_space.py and test_mm_crt/test_crt.py.
Conditional on original atom denominator <= 8 and invariant diagonal norm
(weights 1 or 2). No lifting of arbitrary modular target matrices.
"""
from dataclasses import dataclass
from functools import reduce
from math import gcd, prod
from fractions import Fraction
import numpy as np

MODULI = (7, 31, 127, 255)
M = prod(MODULI)
CRT = tuple((M//p)*pow(M//p,-1,p) for p in MODULI)
RADIX = 128
DIM = 196884


def require(ok, message):
    if not ok: raise ValueError(message)


def norm2(a, weights):
    return sum(int(w)*int(x)**2 for w,x in zip(weights,a))


def centered_crt(residues):
    a = sum(c*np.asarray(r,dtype=np.int64) for c,r in zip(CRT,residues))%M
    return np.where(a>M//2,a-M,a)


def integer_atom(a, atom, residue_action, weights):
    """Return 8*rho(atom)a, in the original external coordinates."""
    a=np.asarray(a,dtype=object)
    require(a.ndim==1 and len(a)==len(weights),'wrong vector shape')
    require(all(isinstance(x,(int,np.integer)) for x in a),'noninteger limb input')
    require(all(w in (1,2) for w in weights),'invalid norm weights')
    signs=np.array([1 if x>=0 else -1 for x in a],dtype=np.int64)
    work=np.abs(a); out=np.zeros(len(a),dtype=object); radix_power=1
    # The conservative bound also covers every possible limb of full DIM.
    require(4*64*(RADIX-1)**2*sum(int(w) for w in weights)<M*M,'CRT modulus too small')
    while np.any(work):
        limb=np.asarray(work%RADIX,dtype=np.int64)*signs
        work=work//RADIX
        if np.any(limb):
            residues=[(8*np.asarray(residue_action(limb,atom,p),dtype=np.int64))%p for p in MODULI]
            require(all(r.shape==limb.shape for r in residues),'wrong native residue shape')
            b=centered_crt(residues)
            require(norm2(b,weights)==64*norm2(limb,weights),'native norm discrepancy')
            out+=b.astype(object)*radix_power
        radix_power*=RADIX
    require(norm2(out,weights)==64*norm2(a,weights),'recombined norm discrepancy')
    return out


@dataclass(frozen=True, eq=False)
class Vector:
    """(a + zeta*b)/d, one common positive integer denominator."""
    a: np.ndarray
    b: np.ndarray
    d: int=1

    def __eq__(self, other):
        return isinstance(other,Vector) and np.array_equal(self.a*other.d,other.a*self.d) and np.array_equal(self.b*other.d,other.b*self.d)


def normalize(a,b,d):
    a,b=np.asarray(a,dtype=object),np.asarray(b,dtype=object)
    require(a.shape==b.shape and a.ndim==1 and d!=0,'invalid cyclotomic vector')
    if d<0:a,b,d=-a,-b,-d
    g=reduce(gcd,(int(x) for arr in (a,b) for x in arr),int(d))
    return Vector(a//g,b//g,int(d)//g)


def add(v,w):
    g=gcd(v.d,w.d);m,n=w.d//g,v.d//g
    return normalize(m*v.a+n*w.a,m*v.b+n*w.b,v.d*m)


def scale(c,v):
    # SymPy QQ.cyclotomic_field(3) ANP, descending coefficients.
    coeff=[Fraction(int(x.numerator),int(x.denominator)) for x in c.to_list()]
    require(len(coeff)<=2,'wrong cyclotomic field')
    b,a=([Fraction(0)]*(2-len(coeff))+coeff)
    d=a.denominator*b.denominator//gcd(a.denominator,b.denominator)
    A,B=int(a*d),int(b*d)
    return normalize(A*v.a-B*v.b,B*v.a+(A-B)*v.b,v.d*d)


def action(v,atoms,residue_action,weights):
    for atom in atoms:
        v=normalize(integer_atom(v.a,atom,residue_action,weights),
                    integer_atom(v.b,atom,residue_action,weights),8*v.d)
    return v


def reduce_vector(v,p,zeta):
    return np.asarray((v.a+zeta*v.b)%p,dtype=np.int64)*pow(v.d,-1,p)%p


class ConwayNative:
    """Use the original native mmgroup external-index and atom-action API."""
    def __init__(self):
        from mmgroup import MMV
        from mmgroup.mm_op import mm_op_word, mm_vector
        from mmgroup.structures.mm_space_indices import numeric_index_to_sparse
        self.MMV,self.op,self.work=MMV,mm_op_word,mm_vector
        _,self.indices=numeric_index_to_sparse(255,'E')
        require(self.indices.shape==(DIM,) and not np.any(self.indices&255),'original external index chart')
        self.weights=np.ones(DIM,dtype=np.int64);self.weights[24:300]=2

    def residue(self,limb,atom,p):
        v=self.MMV(p)(); val=np.asarray(limb%p,dtype=np.uint32)
        v.space.setitems_sparse(v,self.indices|val)
        require(np.array_equal(np.asarray(v['E'],dtype=np.int64)%p,val),'original external coordinate write mismatch')
        a=np.array([atom],dtype=np.uint32)
        self.op(p,v.data,a,1,1,self.work(p))
        return np.asarray(v['E'],dtype=np.int64)%p

    def act(self,v,g):
        atoms=tuple(int(a) for a in g.mmdata)
        require(all(1<=((a>>28)&7)<=6 for a in atoms),'unknown native atom tag')
        return action(v,atoms,self.residue,self.weights)

    def unit(self,j):
        require(0<=j<DIM,'invalid original unit coordinate')
        a=np.zeros(DIM,dtype=object);a[j]=1
        return Vector(a,np.zeros(DIM,dtype=object))
