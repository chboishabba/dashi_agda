from sympy import symbols, Rational as Q, cancel, diff, factorial, prod, expand, Poly
from time import perf_counter

def main():
    start=perf_counter()
    e,a,b=symbols('E2 E4 E6', nonzero=True)
    z=1-b*b/a**3
    def D(f):
        return cancel(diff(f,e)*(e*e-a)/12+diff(f,a)*(e*a-b)/3+diff(f,b)*(e*b-a*a)/2)
    assert cancel(D(z)-z*b/a)==0
    # F=sqrt(E4); operate on rational multipliers of F.
    def T(f):
        return cancel(a/b*(D(f)+f*(e-b/a)/6))
    f=[1]
    for _ in range(3): f.append(T(f[-1]))
    assert cancel(f[3]-z*(f[3]+Q(3,2)*f[2]+Q(23,36)*f[1]+Q(5,72)))==0
    # exact coefficient recurrence for z=1728/j
    for n in range(1,25):
        lhs=Q(factorial(6*n),factorial(3*n)*factorial(n)**3*1728**n)
        prev=Q(factorial(6*(n-1)),factorial(3*(n-1))*factorial(n-1)**3*1728**(n-1))
        assert n**3*lhs==prev*prod(n-1+c for c in (Q(1,6),Q(1,2),Q(5,6)))
    A,B,C=13591409,545140134,640320
    assert Q(1-Q(77265280,90856689),6)==Q(A,B)
    assert 144*B*B==163*(C**3+1728)
    print('PASS: Ramanujan vector field -> hypergeometric ODE, 24 coefficient ratios, CM normalization algebra')
    print('wall_seconds',perf_counter()-start)
if __name__=='__main__':main()
