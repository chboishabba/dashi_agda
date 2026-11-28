import sympy as s
from itertools import combinations
Q=s.Rational

def run(X,G,A):
    pairs=list(combinations(range(5),2)); left=G.inv()*X.T
    def wedge_gen(K):
        return s.Matrix(10,10,lambda i,j: K[pairs[i][0],pairs[j][0]]*int(pairs[i][1]==pairs[j][1])-K[pairs[i][0],pairs[j][1]]*int(pairs[i][1]==pairs[j][0])-K[pairs[i][1],pairs[j][0]]*int(pairs[i][0]==pairs[j][1])+K[pairs[i][1],pairs[j][1]]*int(pairs[i][0]==pairs[j][0]))
    def projector(B):return (4*B**4-B**2)/3
    def derivative(B,H):return (4*sum((B**j*H*B**(3-j) for j in range(4)),s.zeros(35))-B*H-H*B)/3
    F=projector(A[0]); assert F.rank()==10
    for i,j in combinations(range(1,5),2):
        K=s.zeros(5);K[j,i]=1;K[i,j]=-1
        L=wedge_gen(K); T=s.kronecker_product(L,s.eye(10))+s.kronecker_product(s.eye(10),L)
        O=left*T*X
        assert X*O==T*X and O.T*G+G*O==s.zeros(35)
        for k in range(1,5):
            H=sum((K[l,k]*A[l-1] for l in range(1,5)),s.zeros(35))
            B=A[k-1]; P=projector(B); dP=derivative(B,H)
            assert O*B-B*O==H
            assert dP==O*P-P*O
            assert P*dP+dP*P==dP and P*dP*P==s.zeros(35)
        print('rotation',i,j,'four axes PASS',flush=True)
    B=Q(3,5)*A[0]+Q(4,5)*A[1]; H=-Q(4,5)*A[0]+Q(3,5)*A[1]
    P=projector(B); dP=derivative(B,H)
    assert P*P==P and P.rank()==10 and P.T*G==G*P
    assert P*dP+dP*P==dP and P*dP*P==s.zeros(35)
    assert dP.T*G==G*dP
    print('tilted unit covector tangent PASS',flush=True)
    print('PASS BR203 rotation covariance and normalized covector derivative',s.__version__,flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier
    _,_,X,G,_,_,_,A,_,_,_,_=carrier()
    run(X,G,A)
