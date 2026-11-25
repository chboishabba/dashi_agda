"""Exact SymPy controls of the CRT proof, not native Monster execution."""
from itertools import product
import numpy as np
from sympy import QQ, Matrix, Rational
from monster3b_conway_exact_crt import *

K=QQ.cyclotomic_field(3);z=K.unit
# Orthogonal Hadamard with denominator 8, and signed permutations.
H=np.array([[(-1)**((i&j).bit_count()) for j in range(64)] for i in range(64)],dtype=np.int64)
J=np.roll(np.eye(64,dtype=np.int64),1,axis=0)*8
ops=[H,J,J.T]; weights=np.ones(64,dtype=np.int64)

def native(limb,atom,p):return (ops[atom]@limb)*pow(8,-1,p)%p

def run():
    count=0
    for k in (0,1,7,31,85,170):
        a=np.array([(-1)**i*((1<<k)+i**3) for i in range(64)],dtype=object)
        b=np.array([(-1)**(i//2)*(i*(1<<k)-3) for i in range(64)],dtype=object)
        v=normalize(a,b,19)
        w=action(v,[0,1,2,0],native,weights)
        require(w==v,'inverse')
        for atom in range(3):
            w=action(v,[atom],native,weights)
            R=Matrix(ops[atom].tolist())/8
            require(all(R*Matrix(u.tolist())/v.d==Matrix(t.tolist())/w.d for u,t in ((v.a,w.a),(v.b,w.b))),'exact SymPy parity')
            require(action(scale(z/3,v),[atom],native,weights)==scale(z/3,w),'K-linearity')
            for p,root in ((31,5),(127,19)):
                require(np.array_equal(reduce_vector(w,p,root),native(reduce_vector(v,p,root),atom,p)),'reduction')
                count+=1
        require(add(scale(z,v),add(scale(z*z,v),v))==scale(K.zero,v),'cyclotomic cancellation')
    # Full-size worst-case limb and weighted norm, with signed permutation
    # within equal metric weights. No dense matrix construction.
    full_weights=np.ones(DIM,dtype=np.int64);full_weights[24:300]=2
    a=np.array([(-1)**i*((1<<100)+127) for i in range(DIM)],dtype=object)
    def flip(limb,atom,p):return -limb%p
    require(np.array_equal(integer_atom(a,0,flip,full_weights),-8*a),'full-size limbs')
    def corrupt(limb,atom,p):
        b=flip(limb,atom,p);b[0]=(b[0]+1)%p;return b
    try:integer_atom(a,0,corrupt,full_weights)
    except ValueError:pass
    else:raise ValueError('corrupted native residue accepted')
    print(dict(sympy_atom_equations=36,exact_cyclotomic_linearity=18,reductions=count,roundtrips=6,full_size_limb_checks=1,corruption_rejected=1))

if __name__=='__main__':run()
