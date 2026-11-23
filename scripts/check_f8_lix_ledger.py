import sympy as s
from itertools import product

def check():
    count=0
    for d in (3,7,11):
        W=s.diag(*[s.Rational((2*j+1)**d-max(0,2*j-1)**d,d*2**d) for j in range(3)])
        A=s.Matrix([[1,2,0],[-1,1,3],[0,2,1]])/7
        B=s.Matrix([[2,0,1],[1,3,0],[0,-1,2]])/5
        z=s.Matrix([2,-3,1]); x=s.Matrix([1,4,-2]); r=s.Matrix([3,-2,5]); q=s.Matrix([-2,4,1])
        adj=lambda M:W.inv()*M.T*W
        pair=lambda a,b:(a.T*W*b)[0]
        assert pair(z,A*x)==pair(adj(A)*z,x);count+=1
        assert adj(B*A)==adj(A)*adj(B);count+=1
        assert pair(z,B*(A*x+r)+q)==pair(adj(A)*adj(B)*z,x)+pair(adj(B)*z,r)+pair(z,q);count+=1
        for mask in product((0,1),repeat=3):
            P=s.diag(*mask); Q=s.eye(3)-P
            assert P*Q==s.zeros(3) and adj(P)==P;count+=1
            assert pair(z,r)==pair(z,P*r)+pair(z,Q*r);count+=1
        # Three independent residual branches; preserve signed and unsigned ledgers.
        a,b,c=[pair(z,v) for v in (r,q,-r-q)]
        assert a+b+c==0 and abs(a)+abs(b)+abs(c)>0;count+=1
    # Trialectic face negative control: linear marginal sums cannot recover a triple product.
    for parity in (0,1):
        rows=[x for x in product((-1,1),repeat=3) if (x[0]*x[1]*x[2]==1)==bool(parity)]
        assert all(sum(x[i] for x in rows)==0 for i in range(3));count+=1
        assert all(sum(x[i]*x[j] for x in rows)==0 for i,j in ((0,1),(1,2),(0,2)));count+=1
        assert sum(x[0]*x[1]*x[2] for x in rows)==(4 if parity else -4);count+=1
    print(count,'exact SymPy checks PASS')
if __name__=='__main__':check()
