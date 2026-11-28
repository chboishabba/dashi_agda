#!/usr/bin/env python3
"""BR63 exact NONLINEAR Israel trace-reversal back-solve on moving wall.

For any nondegenerate 4D induced Lorentz metric h, its inverse h^-1,
jump K_ab and wall scalar j, define the exact physical Israel tensor
   I_ab = jump K_ab - h_ab tr_h(jump K) + 3 j h_ab.
Then
   jump K_ab = [I_ab-3j h_ab]
       -(1/3) h_ab tr_h[I-3j h].
This bidirectional map needs NO tangential frequency, holds at q=0 and
at null q²=0, and retains all ten symmetric tensor components. It is
the full induced-metric trace-reversal, NOT the flat reference η
approximation or a positivity theorem.

At a stress-free (I=0) pure-tension wall, [K]=j h as required.
The original Codazzi source still constrains four derivatives of I;
this inverse does not by itself give Einstein–Israel evolution.

--part reference|moving|source.
"""
import argparse
import sympy as s

def original_junction(h,k,j):
    hi=h.inv()
    tr=s.trace(hi*k)
    return k-h*tr+3*j*h

def original_inverse(h,I,j):
    hi=h.inv()
    src=I-3*j*h
    return src-s.Rational(1,3)*h*s.trace(hi*src)

def check(h,seed):
    k=s.Matrix(4,4,lambda a,b:
        s.Rational((min(a,b)+2)*(max(a,b)+4)+seed-13,11))
    j=s.Rational(seed-4,7)
    assert h.det()!=0
    I=original_junction(h,k,j)
    reconstructed=original_inverse(h,I,j)
    assert (reconstructed-k).applyfunc(s.cancel)==s.zeros(4)
    back=original_junction(h,reconstructed,j)
    assert (back-I).applyfunc(s.cancel)==s.zeros(4)
    assert I==I.T
    zero=s.zeros(4)
    pure=original_inverse(h,zero,j)
    assert (pure-j*h).applyfunc(s.cancel)==s.zeros(4)
    assert (original_junction(h,j*h,j)).applyfunc(s.cancel)==s.zeros(4)
    return True

def reference():
    h=s.diag(-1,1,1,1)
    for k in range(6):check(h,k)
    print("PASS BR63 original eta 10-dimensional Israel full trace reverse and inverse")

def moving():
    # Actual induced metric from material graph F=n-f(t,x,y,z)
    # in flat 5D, with NONZERO time and tangential graph tilt.
    g=s.diag(-1,1,1,1,1)
    grad=s.Matrix([s.Rational(1,5),s.Rational(-2,7),
                   s.Rational(3,11),s.Rational(1,13)])
    e=s.Matrix(5,4,lambda i,j:
        int(i==j)+(grad[j] if i==4 else 0))
    h=e.T*g*e
    expected=g[:4,:4]+grad*grad.T
    assert h==expected
    z=1+(grad.T*g[:4,:4]*grad)[0]
    assert z>0 and h.det()!=0
    for k in range(6):check(h,k)
    print("PASS BR63 actual moving spacelike graph non-diagonal induced metric, 10 channels")

def source():
    # Reverse solve is not a source-free wall compatibility theorem:
    # a generally prescribed symmetric I has nonzero signed Codazzi
    # divergence, even though its K jump can be reconstructed.
    from check_hopf369_br62_israel_codazzi_rank import pencil,PAIRS
    q=s.Matrix([1,1,0,0]) # characteristic null q²=0
    A=pencil(q)
    assert A.rank()==4
    T=s.Matrix([s.Rational(k+1,13) for k in range(10)])
    assert A*T!=s.zeros(4,1)
    h=s.diag(-1,1,1,1)
    I=s.Matrix(4,4,lambda i,j:s.Rational(min(i,j)+max(i,j)+2,17))
    K=original_inverse(h,I,s.Rational(-6,5))
    assert (original_junction(h,K,s.Rational(-6,5))-I)==s.zeros(4)
    print("PASS BR63 frequency-free Israel inverse; unforced null Codazzi violation retained")

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--part",choices=["reference","moving","source"],default="reference")
    args=p.parse_args()
    {"reference":reference,"moving":moving,"source":source}[args.part]()

if __name__=="__main__":main()
