from sympy import binomial, Integer, __version__
from itertools import product

def count(n,k):
    return 22*sum(binomial(n-1,f)*binomial(n-1-f,m)*Integer(5)**(f+m)*Integer(17)**(n-1-f-m) for f in range(k) for m in range(n-k+1))
for n in range(1,7):
    for k in range(1,n+1):
        direct=0
        for a in product(range(3),repeat=n):
            if a[-1]==1:continue
            f=a[:-1].count(0); m=a[:-1].count(1)
            if f<=k-1<=n-1-m:
                direct+=5**(a.count(0)+a.count(1))*17**a.count(2)
        assert count(n,k)==direct
expected=9167718374353723578296555963574948854256678928778970149906144439312264998339359863246305576651707176606
assert count(72,21)==expected
print('SymPy',__version__,'21 small cases PASS; Shem exact word-count fibre PASS')
