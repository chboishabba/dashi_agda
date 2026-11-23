# YM.REAL exact SymPy six-gate cut — 17 November 2026

## Reproducible verification

Use scripts/check_ym_real_sympy_fullchain_20261117.py. Verified locally with
SymPy 1.14.0: 169/169 exact symbolic assertions.

The existing companion scripts were also rerun locally:
- check_ym_original_wilson_loworder_20261117.py: 44346/44346
- check_ym_wilson_L1_commutator_20261117.py: 1184/1184
- check_ym_dyadic_cyclotomic_full_20261117.py: 1374/1374
- check_ym_bn_cauchy_schedule_20261117.py: 551/551

Three later geometry-forward finite checks were ported to master and
executed with the project venv (`sympy 1.14.0`, exact `Fraction`
arithmetic where applicable):

- check_ym_w0_T_path_geometry_20261123.py: PASS, path coefficients
  (13, 6, 14, 4) with the shared intermediate state retained.
- check_ym_p0_original_wilson_marked_ordered_t_20261123.py: PASS, 1024
  restricted Z2 states, four W-fibre four-column ordered-T identities.
- check_ym_p0_original_gauge_orbit_20261123.py: PASS, 1024 links, 1536
  plaquettes, connected frozen complements, and exact 2^265/2^248 counts.

Total 47624/47624 earlier exact rational and symbolic assertions, plus
the three later PASS controls, without using approximate trigonometric
arithmetic or simulation. These are finite/computational checks, NOT Agda
kernel-accepted universal theorems.

## Six constructive mathematical links

**Finite Fejer and all-degree cubature.** Pick dyadic orders A,M,L with
2(A-1)-1 >= d, M>d, L>d. On S3, use Chebyshev-II nodes
x_a=cos(pi*a/A), weight 2*sin(pi*a/A)^2/A, Fejer-I midpoint nodes
y_b=cos((2b-1)*pi/(2M)) and weights

w_b = [1 - 2 sum_(h=1)^floor((M-1)/2)
        cos(h*(2b-1)*pi/M)/(4*h*h-1)] / M,

and L equally weighted circle nodes. The product has (A-1)*M*L
strictly positive nodes and integrates every sphere polynomial of degree
<=d. Fejer positivity follows from the universal rational telescope
2*sum_(h=1)^J(4h*h-1)^(-1)=1-(2J+1)^(-1), so
w_b >= 1/[M(2J+1)] >0. Chebyshev/Fejer/circle exactness follows from
finite Fourier character orthogonality; even monomial moments factor
into Pochhammer products and odd monomials vanish. The cyclotomic
checker uses exact Q[z]/(z^N+1) for complete degrees 3,5,7,9.
The all-d Fourier induction and positive Bishop square-root embedding
are mathematical arguments, not Agda typechecked producers.

**Effective b_n.** Let b_n(q,v)=((1+q.v)/2)^n and
c_n=(3/2)_n/(3)_n. The exact kernel identities are

H_v((1-q.v)*b_n)/c_n = 3/(n+3),
H_v((q.v)^2*b_n)/c_n = (n^2+n+3)/[(n+3)(n+4)].

For |f|<=B and L_f-Lipschitz with L_f>0,
Q_n(f)(q)=sum_j(w_j*f(v_j)*b_n(q,v_j))/c_n, where the
positive cubature integrates degree n+1, obeys

||Q_n(f)-f|| <= L_f*delta + 12*B/[(n+3)*delta^2].

At eps_k=2^(-k-3), delta_k=eps_k/(2*L_f) and
n_k=ceil(96*B*L_f^2/eps_k^3), the error is <=eps_k.
The constant-function case L_f=0 is exact already. For any bounded
uniformly continuous f, replace L_f*delta by its supplied modulus.

**Bishop completion.** Polynomial positivity and H(1)=1 give
|H(P)|<=||P||_infty. Thus a_k=H(Q_(n_k)f) is Cauchy:
|a_j-a_k|<=eps_j+eps_k (j>=k). The direct Bishop
Sequence.fast-cauchy⇒convergent constructs its real limit. Positivity,
linearity, contractivity, setoid-extensionality and two-sided SU2
invariance then extend by polynomial approximation and O(4) moment
invariance. The actual Agda modulus/Cauchy producer remains open.

**SU2 matrix and original rational source.** U(q)=[[q0+i*q3,q2+i*q1],
[-q2+i*q1,q0-i*q3]]. SymPy proves Tr U/2=q0,
det U=q0^2+q1^2+q2^2+q3^2 and U^dagger U=U U^dagger=norm^2 I.
The branch contains the original reduced-rational to Bishop embedding
and norm-one transport as source-written candidates. Agda acceptance
and a full original SUN group carrier equivalence remain open.

**Finite original Wilson scalar route.** At periodic side L, the
original source has 4L^4 independent positive links, 6L^4 six-plane
plaquettes, and Wilson action
S_L(U)=beta*sum_p(1-ReTr(U_p)/2) >=0, beta>=0.
For all real S>=0, the alternating Taylor polynomials satisfy
T_(2m+1)(S) <= exp(-S) <= T_(2m)(S), and their difference is
S^(2m+1)/(2m+1)!. Since 0<=S_L<=B_L=12*beta*L^4, finite positive
per-link cubatures exact through polynomial degree 2*(2m+1)
(conservative for L>=2 and sufficient for the commutator L=1)
integrate both rational endpoints exactly. Hence their exact
partition bracket width is at most
B_L^(2m+1)/(2m+1)!, which tends constructively to zero. This
constructs a rational endpoint algorithm for the finite Wilson
partition without first defining Haar on arbitrary continuous f.
Source-native 4D link/plaquette enumeration is already available;
the full legacy/SUN/Bishop carrier identification is still open.

## First/second original Wilson coefficient certificates

For L>=2, let P=6L^4. Exact moments of the independent-link
six-plane trace give E[S_L/beta]=P and
E[(S_L/beta)^2]=P^2+P/4.
For L=1, original plaquettes are link commutators, not distinct
link loops: E[S_L/beta]=9/2 and E[(S_L/beta)^2]=187/8.
Consequently 1-beta*E[S/beta] <= Z_L(beta) <=
1-beta*E[S/beta]+beta^2*E[(S/beta)^2]/2.

At beta=1/(16P) the exact enclosures are:

L=1: beta=1/96, Z in [61/64, 140731/147456]
L=2: beta=1/1536, Z in [15/16, 184705/196608]
L=3: beta=1/7776, Z in [15/16, 935065/995328]
L=4: beta=1/24576, Z in [15/16, 2955265/3145728]
L=5: beta=1/60000, Z in [15/16, 7215001/7680000]
L=6: beta=1/124416, Z in [15/16, 14961025/15925248]

The bounds are exact for the mathematical independent-link SU2 Haar
model and for positive cubature models sharing its degree-2 moments,
not a computed Agda-defined original measure.

## Trust ledger

Finite rational/SymPy and symbolic identities: PASS for the checks above.
All-degree cubature mathematical recipe: available, with a proof scheme.
Native universally quantified Agda Fourier producer: OPEN.
Native Bishop uniform-modulus/Cauchy producer and continuous Haar: OPEN.
Original rational-to-Bishop 2x2 unitary: source-written, kernel OPEN.
Original same-source SUN/legacy scalar and all-cutoff Haar cylinder: OPEN.
No continuum interacting Yang–Mills or mass gap is inferred.

Attribution: Fejer, Stroud, Pizzetti/Folland, Wilson, Balaban,
Bishop/Bridges, Murray/Csimma and original DASHI theorem owners.
