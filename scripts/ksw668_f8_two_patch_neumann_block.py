#!/usr/bin/env python3
"""KSW F8 noncommutative causal two-patch DN->ND inverse.

On causally ordered source E and receiver R boundary patches, take
A=[[D_e,0],[F_re,D_r]]. Di are elliptic local outgoing DN operators;
F_re is the non-glancing lens DN Fourier-integral operator. The local
diagonal parametrix G0 gives R=I-A G0, R²=0 exactly. Thus
G=G0(I+R) is an exact 2-term Neumann inverse (operator algebra).
ND_{r<-e}=-D_r^-1 F_re D_e^-1. This recycles the DASHI Balaban
finite Neumann telescope, not a spectral contraction argument.

A rigorous original physical FIO composition additionally requires
the microlocal patch restriction, causal wavefront remainder and
specific original TT/Weyl source-observable weld. Not a measurement.
"""
import json
import sympy as s
INVERSE={'De':'Ee','Ee':'De','Dr':'Er','Er':'Dr'}
def red(word):
    stack=[]
    for letter in word:
        if stack and INVERSE.get(stack[-1])==letter:stack.pop()
        else:stack.append(letter)
    return tuple(stack)
class E:
    def __init__(self,terms=None):
        self.terms={w:c for w,c in (terms or {}).items() if c}
    @classmethod
    def atom(cls,*parts):return cls({red(parts):1})
    def __add__(self,other):
        d=self.terms.copy()
        for w,c in other.terms.items():d[w]=d.get(w,0)+c
        return E(d)
    def __neg__(self):return E({w:-c for w,c in self.terms.items()})
    def __sub__(self,other):return self+(-other)
    def __mul__(self,other):
        d={}
        for w,c in self.terms.items():
            for ww,cc in other.terms.items():
                key=red(w+ww)
                d[key]=d.get(key,0)+c*cc
        return E(d)
    def __eq__(self,other):return self.terms==other.terms
I=E.atom();O=E();De=E.atom('De');Dr=E.atom('Dr')
Ee=E.atom('Ee');Er=E.atom('Er');F=E.atom('F')
def mul(A,B):
    return [[A[i][0]*B[0][j]+A[i][1]*B[1][j]
            for j in range(2)] for i in range(2)]
def add(A,B):
    return [[A[i][j]+B[i][j] for j in range(2)] for i in range(2)]
def sub(A,B):
    return [[A[i][j]-B[i][j] for j in range(2)] for i in range(2)]
def equal(A,B):
    return all(A[i][j]==B[i][j] for i in range(2) for j in range(2))
def audit():
    ONE=[[I,O],[O,I]]
    A=[[De,O],[F,Dr]]
    G0=[[Ee,O],[O,Er]]
    R=sub(ONE,mul(A,G0))
    zero=[[O,O],[O,O]]
    assert R[1][0]==-(F*Ee)
    assert equal(mul(R,R),zero)
    G=add(G0,mul(G0,R))
    assert equal(mul(A,G),ONE)
    assert equal(mul(G,A),ONE)
    assert G[1][0]==-(Er*F*Ee)
    assert G[1][0]!=-(Ee*F*Er)  # No commutation is assumed.
    de=s.Matrix([[2,1],[0,1]])
    dr=s.Matrix([[1,0],[1,3]])
    f=s.Matrix([[1,2],[3,4]])
    big=s.BlockMatrix([[de,s.zeros(2)],[f,dr]]).as_explicit()
    g0=s.diag(de.inv(),dr.inv())
    rr=s.eye(4)-big*g0
    gg=g0*(s.eye(4)+rr)
    assert rr**2==s.zeros(4)
    assert big*gg==s.eye(4) and gg*big==s.eye(4)
    assert gg[2:4,0:2]==-dr.inv()*f*de.inv()
    return dict(operator='[[De,0],[F_re,Dr]]',
       causal_late_to_early_block_zero=True,
       diagonal_local_parametrix='diag(Ee,Er)',
       residual='[[0,0],[-F_re Ee,0]]',
       residual_squared_zero=True,
       exact_finite_Neumann_depth=2,
       exact_inverse='[[Ee,0],[-Er F_re Ee,Er]]',
       exact_noncommutative_two_sided_inverse=True,
       rational_nonscalar_matrix_positive_control=True,
       microlocal_ND_offdiagonal='-Er F_re Ee',
       elliptic_source_DN_order=1,lens_FIO_order=1,
       elliptic_receiver_DN_order=1,
       ND_lens_FIO_order=-1,
       two_derivative_Weyl_after_ND_order=1,
       source_TT_fourth_derivative_normalized_by_lambda4=True,
       physically_identified_full_5D_FIO_with_smoothing_error=False,
       measured_early_graviton=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
