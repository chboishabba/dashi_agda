#!/usr/bin/env python3
"""Original source E32/E33/E21 Higgs versus pure YM mass-gap gates.

Source #1106/#1241 SU3c x SU3L x SU3R bifundamentals and orbifold
parities. Tree-level gauge-orbit mass kernels are NOT 4D pure YM OS gaps.
"""
import sympy as s


def e(i,j):
    x=s.zeros(3); x[i,j]=1; return x


def basis():
    out=[]
    for i in range(3):
        for j in range(i+1,3):
            out += [e(i,j)+e(j,i), s.I*(e(i,j)-e(j,i))]
    out += [s.diag(1,-1,0),s.diag(1,1,-2)]
    return out


def realvec(X):
    return s.Matrix([s.re(s.expand_complex(z)) for z in X]+[s.im(s.expand_complex(z)) for z in X])


def main():
    parity=s.diag(-1,-1,1)
    even=[X for X in basis() if parity*X*parity==X]
    assert len(even)==4
    zero=s.zeros(3)
    # Source VEV structure with rational trial amplitudes.
    # The true nonconstant BVP must still be used for a physical operator.
    phi=e(2,1)
    chi=e(2,2)+s.Rational(1,4)*e(1,0)
    def variation(L,R):
        return realvec(L*phi-phi*R).col_join(realvec(L*chi-chi*R))
    C=s.Matrix.hstack(*([variation(t,zero) for t in even]+[variation(zero,t) for t in even]))
    assert C.rows==36 and C.cols==8 and C.rank()==7
    M=C.T*C
    assert M.rank()==7 and len(M.nullspace())==1
    # Source Higgs fields are colour singlets; tree-level colour mass = zero.
    Mfull=s.diag(s.zeros(8),M)
    assert Mfull.rank()==7 and len(Mfull.nullspace())==9
    # Negative control: without E21 only four L/R directions break.
    chi0=e(2,2)
    def variation0(L,R):
        return realvec(L*phi-phi*R).col_join(realvec(L*chi0-chi0*R))
    C0=s.Matrix.hstack(*([variation0(t,zero) for t in even]+[variation0(zero,t) for t in even]))
    assert C0.rank()==4
    # Elementary finite-size kinetic control. This does NOT model
    # interacting YM, nor show that its continuum gap vanishes.
    for n in (8,16,32,64):
        assert 0 < 4*s.sin(s.pi/n)**2 <= 4*s.pi**2/n**2
    print('PASS source orbifold-even SU3L/R gauge basis 4+4; E32/E33/E21 rank 7')
    print('PASS SU3c eight colour generators remain Higgs-null, full gauge nullity 9')
    print('PASS removing E21 restores neutral rank 4 of 8')
    print('PASS no transport from Higgs mass to physical E1/D1/D2/OS YM gap')
    print('OPEN E1 interacting continuum, D1 physical clustering, D2 same-H OS spectrum, N1 and G1')

if __name__=='__main__': main()
