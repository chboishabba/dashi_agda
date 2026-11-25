"""Two-square oriented cochain witness and original-curl frequency limit."""
import json
import sympy as S
q=S.Rational
# Vertex numbering: lower row 0,1,2; upper row 3,4,5.
# Active interior electric edges: shared vertical, right vertical.
# Boundary electric edges: lower left, lower right. Other three edges clamped.
edges=[(1,4),(2,5),(0,1),(1,2),(3,4),(4,5),(0,3)]
G=S.zeros(7,6)
for i,(a,b) in enumerate(edges):G[i,a]=-1;G[i,b]=1
D=S.Matrix([[1,0,1,0,-1,0,-1],[-1,1,0,1,0,-1,0]])
assert D*G==S.zeros(2,6)
assert G.rank()==5 and D.rank()==2 and D.nullspace()
assert 7-D.rank()==G.rank()
C=S.Matrix([[1,-1],[0,1]])
assert D[:,:2]==C.T and D[:,2:4]==S.eye(2)
# Reconstruct every static active closed electric cochain as a gradient,
# keeping inactive edges and boundary effort rather than erasing DC.
x,y=S.symbols('x y',real=True)
e=S.Matrix([x,y,-x,x-y,0,0,0]);phi=S.Matrix([0,-x,-y,0,0,0])
assert D*e==S.zeros(2,1) and G*phi==e
# Original-curl direct-resistor matched terminal: each fixed nonzero
# harmonic sees a finite passive Schur impedance z. With Y=G=t,
# terminal amplitude normalized to sqrt(Y)*E is 2t/(2t+z).
t=S.symbols('t',positive=True);a,b=S.symbols('a b',real=True)
ratio=4*t*t/((2*t+a)**2+b*b)
assert S.limit(ratio,t,S.oo)==1
# DC fraction of the unchanged two-channel four-bin rectangular source.
source=S.Matrix([[0,0],[1,0],[0,1],[0,0]])
mean=S.ones(1,4)*source/4
assert (4*(mean*mean.T)[0])/sum(v*v for v in source)==q(1,4)
print(json.dumps(dict(status='PASS_EXACT_ORIENTED_TWO_SQUARE_COMPLEX',edges=edges,curl=D.tolist(),gradient=G.tolist(),rank_gradient=G.rank(),rank_curl=D.rank(),closed_equals_exact=True,active_DC_gradient_witness=True,original_curl_DC_fraction='1/4',nonzero_mode_matched_limit='1',original_curl_supremum_conditional='3/4',actual_apparatus_mesh=False),indent=2,default=str))
