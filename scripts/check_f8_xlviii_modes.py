import sympy as s

def check():
    t=s.symbols('t',positive=True)
    a,b,c,d=[s.symbols(k+'0:3') for k in ('a','b','c','d')]
    e,f=[s.symbols(k+'0:3') for k in ('e','f')]
    E4=lambda A,L: -(A+L)/(4*t*t)
    E5=lambda A,B,L: -(A+2*B-L)/(2*t*t)
    count=0
    for A,B in ((a,b),(e,f)):
        for j in range(3):
            assert s.simplify(E5(A[j],B[j],c[j])-2*E4(A[j],c[j])-(c[j]-B[j])/t**2)==0; count+=1
            assert s.simplify(E4(A[j],c[j])-E4(A[j],d[j])-(d[j]-c[j])/(4*t**2))==0; count+=1
        assert s.simplify(sum(E4(A[j],c[j]) for j in range(3))-E4(sum(A),sum(c)))==0; count+=1
        assert s.simplify(sum(E5(A[j],B[j],c[j]) for j in range(3))-E5(sum(A),sum(B),sum(c)))==0; count+=1
    for j in range(3):
        assert s.simplify(E4(a[j],c[j])-E4(e[j],c[j])+(a[j]-e[j])/(4*t**2))==0; count+=1
        assert s.simplify(E5(a[j],b[j],c[j])-E5(e[j],f[j],c[j])+(a[j]-e[j]+2*(b[j]-f[j]))/(2*t**2))==0; count+=1
    print(f'{count}/{count} exact symbolic assertions PASS')
if __name__=='__main__': check()
