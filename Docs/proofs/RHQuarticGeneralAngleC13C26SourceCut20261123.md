# RH P0 × 27/13 antipodal quotient × C13/C26 angular lift — original source cut (23 November 2026)

**Evidence:** Exact local SymPy plus rational inequalities and exhaustive 27-point action, script scripts/check_rh_c13_c26_angle_stencil_20261123.py. Original sources: Lean RiemannProjectiveQuarticFourWindowAtomic / PoleSameObject / SignedPoleTarget / SignedPoleSmooth; Agda BalancedTernaryAntipodalOrbitExact, BalancedTernaryAntipodalResidualCodecExact, HyperfabricPunctured27Projective13OrientationExact; Griess source order13 grade action (Lean PR #52). Original mathematical/representation attribution retained. **No Lean/Agda kernel, CI, or RH proof claimed.**

## 1. Distinguish C3, C2, C13 and C26

A finite group is not a numerical divisor. Literal pi/|C3| is the old pi/3. Original balanced ternary 27 is 1 origin plus 26 signed nonzero points, or 13 strict antipodal axes with recoverable sign: 27=1+2*13. This is **C2 global antipodal** reduction; the full 27/C2 quotient has 14 classes including the centre. The source projective axes are stratified 3+6+4 by support.

The independently owned Griess grade automorphism on the same additive F3^3 grades is M(x,y,z)=(x+y,y+z,x+y+z) mod3. Antipode A=-I commutes with M. Exact 27-state exhaustive check: M has order13, two nonzero 13-cycles; G=A∘M has order26, one 26-cycle on the nonzero points, G^13=A and G^26=I. On the projective 13-axis quotient M/G induces one 13-cycle. Hence assigning one G-step the complex phase exp(i*pi/13) is a valid **abstract C26 character**, with its thirteenth step -1; on the 13 axes the step is 2*pi/13. It does NOT identify this character with the physical 3×3×3 cube path metric: all 54/54 original nearest-neighbour edges are sent to nonedges by the genuine M and G actions (existing Griess/C13 spatial no-go). For the unchanged RH centres (0,pi/13,pi/2,pi), pi/2 is 13/2 character steps, not an integer C26 orbit position. The common angle grid is instead pi/26 (52-step circle). Thus no full native C26 Fourier/Laplacian intertwiner follows.

Do not conflate 13 as quotient axes with **the original independent J2 cofactor** 13=9+4=3²+2². A same-source metric/intertwiner would be needed to identify these two appearances.

## 2. Newly derived exact Pluecker cancellation for ANY fourth angle

For original atomic weights (1,-1,lambda,mu), centres (0,theta,pi/2,pi), pole angular frequency16, put z=cos(theta), b=cos(2theta), u=(theta/pi)^2, p=cos(16theta).

Original on-line pairings:
A1=1-z-mu; A2=1-b-lambda+mu.
M1/pi²=-u*z-mu; M2/pi²=-u*b-lambda/4+mu.
J2=A1*M2-A2*M1 is **linear in mu** for every theta (only the positive-radius smooth J2 is generally quadratic).

The original pole modulates only the theta source site because cos(16c)=1 for c=0,pi/2,pi. Hence B1=A1+(1-p)z and B2=A2+(1-p)b. Their same-source projective pole determinant is

P_theta=B1*A2-B2*A1=(1-p)*(z*A2-b*A1).

The original normalized projective profile mass at the source theta site, where raw weight=-1, is Q_theta=4*(z*A2-b*A1). Thus P_theta=(1-p)*Q_theta/4 for **arbitrary lambda,mu,theta**, and for ANY two selected endpoints

P_two*Q_theta_half - P_half*Q_theta_two = 0.

This is a rank-one projective/Pluecker identity and does NOT use theta=pi/3 or J2=0. Both nonzero endpoint source contributions must remain in the raw provenance; the zero is an OBSERVATION, not a missing source, cyclotomic phase or zeta zero.

Each projective profile has zeroth moment 0. Imposing original J2=0 at each endpoint also makes second moment 0. After theta cancellation, surviving masses x0,xh,x2h at h=pi/2 obey x0+xh+x2h=0 and h²*xh+4h²*x2h=0, so necessarily

(x0,xh,x2h)=C_theta*(-3,+4,-1).

Symmetric unfolding produces (C_theta/2)*(-1,+4,-6,+4,-1), negative centered discrete biharmonic on **unchanged spacing h=pi/2**:

F_theta(q)= -2*C_theta*(1-cos(pi*q/2))²
          = -8*C_theta*sin(pi*q/4)^4.

Therefore every original Fourier q=4n fourth-order notch persists when changing the **discarded original theta source position**, but its magnitude C_theta changes. This is NOT a new 13-spaced biharmonic operator. At theta=pi/3, C_theta=40/351 recovers the original formula exactly.

## 3. Explicit full-corridor negative control for theta=pi/13

The standard rational Archimedes pi interval 157/50<pi<22/7, with alternating cosine Taylor bounds, proves

9708/10000 < cos(pi/13) < 971/1000.

Let lambda range over the exact original full interval [1/2,2/3] and solve the original atomic J2 equation. The exact rational inequalities in the committed script establish -1/10<mu(theta,lambda)<0 throughout this interval; moreover A1=1-z-mu>0 and A2=1-b-lambda+mu<0. Since z,b>0 and p=cos(16*pi/13)<1, it follows rigorously that

P_theta(lambda)=(1-p)*(z*A2-b*A1) < 0
for EVERY lambda in the old corridor.

The original Lean SignedPoleSmooth witness uses positive pole lower bounds, so the old source lemma does NOT survive the substitution. The old mu-neighbourhood about the pi/3 atomic endpoints also moves. The angle-dependent C_theta remains positive for pi/13, by factorization and the same rational cosine interval. But its magnitude and target strength shrink:

theta=pi/3:   P_half=+1.125, P_two=+1, C=40/351≈0.113960114, S≈2.08139.
theta=pi/13:  P_half≈-0.787724, P_two≈-1.059079, C≈0.0021229821, S≈0.03877458.
S_theta=3*pi^4*C_theta/16; the old sufficient witness floor 7*pi^4/1600≈0.426165 is not met. Decimal evaluations are DIAGNOSTICS; pole negativity is certified by rational inequalities over ALL lambda.

For exact sign analysis one may use z,u,p and
D_two=4uz²+2uz-2u-4z²-2z+5,
D_half=16uz²+8uz-8u-16z²-8z+21,
C_theta=4(p-1)(z-1)(2z+1)(4z²+2z-5)(6z²+3z-7)(uz-z+1)/(9 D_two D_half).
The local SymPy identity verifies C_theta=-selected mass at pi. At theta=pi/13 both D factors and (p-1),(z-1) are negative, other numerator factors positive, hence C_theta>0.

## 4. Execution choice and nonpromotion

**Preferred RH P0:** leave original pi/3 witness and its positive pole geometry intact; if a projective 13-axis feature helps, add it as a distinct source-indexed/sign-preserving 13-axis fibre, not by replacing a source angle. Only a typed downstream observer map plus a genuinely signed actual-zero estimate could contribute to RH A2.

**P1 exploratory alternative:** redesign the source **jointly**, with different physical angle sites/pole modulation and fresh J2/W positivity and strength estimates, if a true C26-equivariant angular stencil is desired. A single-site pi/13 substitution is insufficient, and treating C13 as the spatial graph symmetry is refuted by all 54 native edge tests. Reuse existing native 27/13 codec, Griess/Albert actor and H05 cube, rather than writing a duplicate 13-point carrier.

The original RH strict post-sixth condition H_n+E_n+S_W<T_W(rho), actual zeta zeros/multiplicities, real mu, FarExact, local slack and analytic six-face maps remain OPEN. No Lean/Agda kernel acceptance, no RH/GRH completion.
