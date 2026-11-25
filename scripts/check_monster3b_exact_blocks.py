"""Exact block/linear combination and normalized outer-coordinate controls."""
from monster3b_conway_exact_crt import *
from monster3b_char0_orbit_weld import K,Z,mat,eye,signed_from_positive
from sympy import Matrix
from random import Random
r=Random(369)
H=np.array([[(-1)**((i&j).bit_count()) for j in range(64)] for i in range(64)],dtype=np.int64)
I=np.eye(64,dtype=np.int64);P=np.roll(I,1,axis=0)
atoms={0x10000001:(P,1),0x50000001:(H,8),0x60000001:(H,8),0x20000001:(P.T,1)}
def residue(v,word,p):
    for a in word:
        M,d=atoms[a];v=M@v%p*pow(d,-1,p)%p
    return v
weights=np.ones(64,dtype=np.int64)
words=[(0x10000001,)*7,(0x50000001,0x10000001,0x60000001),tuple(atoms)*3,()]
checks=0
for k in (0,40,171):
    v=normalize([r.randrange(-2**k,2**k+1) for _ in range(64)],[r.randrange(-2**k,2**k+1) for _ in range(64)],19)
    for word in words:
        blocks=list(atom_blocks(word));require(tuple(a for b,d in blocks for a in b)==word,'word order')
        w=block_action(v,blocks,residue,weights)
        ref=v
        for a in word:ref=action(ref,[a],lambda x,g,p:residue(x,[g],p),weights)
        require(w==ref,'blocked/atom action mismatch');checks+=1
        for p,z in ((31,5),(127,19)):
            require(np.array_equal(reduce_vector(w,p,z),residue(reduce_vector(v,p,z),word,p)),'blocked reduction');checks+=1
    cs=[Z/3, K.convert(2)/7, -Z, K.zero]
    vs=[v,scale(Z,v),scale(K.convert(5)/11,v),v]
    ref=scale(K.zero,v)
    for c,u in zip(cs,vs):ref=add(ref,scale(c,u))
    require(linear_combination(cs,iter(vs),64)==ref,'linear combination');checks+=1
D=mat([[Z,K.zero],[K.zero,K.one]])
E=mat([[K.one,K.zero],[K.zero,Z]])
J=mat([[-K.one,K.zero],[K.zero,K.one]])
A=signed_from_positive(D,E,J)
for s in (1,2):
    t=3-s
    require(A['C'][s].inv()*A['D'][t]*A['C'][s]==A['E'][s],'right E=C D C^-1')
    require(A['C'][t]*A['C'][s]==J,'outer square')
    checks+=2
try:signed_from_positive(D,E,mat([[K.one,K.one],[K.zero,K.one]]))
except ValueError:checks+=1
else:raise ValueError('bad parity accepted')
print({'exact_block_and_signed_checks':checks})
