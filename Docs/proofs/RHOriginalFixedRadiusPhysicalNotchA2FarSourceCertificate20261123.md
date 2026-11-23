# RH P0 — fixed-radius finite-pole and horizontal-uniform Fourier-notch certificate (23 November 2026)

**Original owner:** Lean Synthesis/RiemannProjectiveQuarticFourWindowAtomic.lean, RiemannProjectiveQuarticFourWindowPoleSameObject.lean, RiemannProjectiveQuarticFourWindowSignedPolePair.lean, RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean; prior source regressions check_rh_original_bump_explicit_radius_20261122.py and check_rh_original_bump_q4_sqrtR_boundary_layer_20261123.py. New rational regression scripts/check_rh_original_bump_fixedR_qwindow_20261123.py on RH PR #1533. The full local SymPy script was executed successfully. No Lean/Agda kernel or GitHub CI.

## Fixed-radius result: closes prior q-window obligation

For the SAME original fixed even compact unit-mass normalized bump, original four centres (0,pi/3,pi/2,pi), weights (1,-1,lambda,mu), original J2-null selected endpoints lambda=1/2,2/3, choose R=10^-10, t>=10^14, |a|<=1/2, q near 4. Write alpha=16 a/t. The exact original source combined normalized pair kernel is K(R,t,a,q)=P_two(R,t) Q_half(R,alpha,q)-P_half(R,t) Q_two(R,alpha,q), where P is the original finite-pole determinant with cosh(8v/t)*cos(16v), and Q is the projective original ordinate cosine transform with cosh(alpha v). This is the same original signed two-endpoint coefficient selection, not a new smoothing of q.

The quantitative result, **for ALL t>=10^14 and ALL |a|<=1/2**, is

  K(R,t,a,4 +/- (1/2)*sqrt(R)) > 11 R^2 / 100 > 0;
  K(R,t,a,4 +/- 2*sqrt(R)) < -4 R^2 / 5 < 0.

The four inequalities are strict; by continuity in real q there are AT LEAST TWO distinct real roots of the Fourier RESPONSE, one in each interval (4-2sqrtR,4-sqrtR/2) and (4+sqrtR/2,4+2sqrtR). No uniqueness, actual zeta-zero, RH/GRH or prime-side assertion follows.

## Proof: explicit original source envelopes, no Gaussian and no phase-only descent

Let Y=R Z be the original normalized fixed-shape even bump, with m2=E[Z^2] in [1/24,1] by the original support and plateau. Put e=m2 R^2/2. The prior original J2 source root proof supplies, for each selected endpoint, |mu_exact-(mu0+mu1 e)|<=600 R^4 and |mu1|<1. The original Fourier and centre-moment source expansion, independently recomputed by local SymPy, gives:

  K(R,infinity,0,q) = F(q)+e*K1(q)+E_R(q),
  F(q)=-(320/351)*sin(pi q/4)^4,
  K1(4)=120/13,
  K1'(4)=-200 sqrt(3) pi/117-10/13+764 pi/351.

For |q-4|<=2sqrtR all q-shift arguments in Q satisfy |q +/- 1,2|<7 and pole frequencies <=18. Original absolute source weight mass <3, support |v|<4, and normalized even-bump Fourier error |phi(k)-(1-e k^2)|<= k^4 R^4/24 (including the original first two differentiated moment formulae) imply uniform source-coefficient bounds Acoef<=1300; |P0|<=18, |P1|<=6000, |Q0''|<=1152 and |Q1''|<=60096, hence |K1''|<16,000,000. The exact K1'(4) and pi<22/7, sqrt(3)<2 give |K1'(4)|<20. Therefore throughout the q interval:

  |K1(q)-120/13| <= 20|q-4|+8,000,000|q-4|^2 <=0.0036,
  e*|K1(q)-120/13|<=0.0018 R^2.

The original true-bump vs truncated-jet q-uniform residual (including both selected exact J2 roots) is |E_R(q)|<23,000,000,000,000 R^4. It uses source root correction 600R^4, pole input truncation at |k|<=18, q source at |k|<7 and polynomial-jet coefficient l1 norm 1300. For delta=q-4, |delta|<=2sqrtR, elementary |sin u-u|<=|u|^3/6 gives

  |F(4+delta)+(5 pi^4/1404)*delta^4|<=10R^3.

**NEW q-UNIFORM finite-pole/horizontal payment:** on |v|<4, t>=200 and |a|<=1/2, both |8v/t| and |alpha v| are <=32/t<=0.16. Since cosh y-1<=y^2 on this strip, the ORIGINAL positive normalized bump mass and absolute weight sum <3 give:
  individual pole pairing drift <=3072/t^2,
  |P_j(t)-P_j(infinity)|<=18432/t^2,
  |Q_j(alpha,q)-Q_j(0,q)|<=73728/t^2,
  |P_j(t)|<19 and |Q_j(0,q)|<=72.
Thus for every REAL q, not only q=4,
  |K(R,t,a,q)-K(R,infinity,0,q)|
   <= 2*(18432*72+19*73728)/t^2
   = 5,455,872/t^2.
At t>=10^14 this is <0.055 R^2. This bound uses the real original horizontal normalization alpha=16a/t, not an arbitrary unscaled a.

Writing q=4+x sqrtR at x= +/-1/2 and +/-2, one therefore has

  K(R,t,a,q)/R^2 = (60/13)*m2 -(5 pi^4/1404)*x^4 + error,
  |error| < 0.058.

For |x|=1/2 the lower value at m2=1/24 is 5/26-5 pi^4/22464 > 0.17 by pi<22/7; subtracting 0.058 leaves >0.11. For |x|=2 the upper value at m2=1 is (20/351)(81-pi^4)<-0.9 by pi>157/50; adding 0.058 leaves <-0.8. All these numerical comparisons were checked as exact rational inequalities, not rounded floats.

## Correct RH/GRH mapping and source-frontier

**Critical geometry:** original canonical local physical zero window is |q|<=eta=1/(pi+1)<1/4, where q=(gamma-t)/(t/16). The certified q≈4 frequency roots lie in the FAR source at gamma≈5t/4. They are roots of the signed FOUR-WINDOW FOURIER-RESPONSE, NOT actual zeros of zeta(s). They cannot be moved into the local zero band or into the physical complex zero coordinates by any C3/C4/C26 hyperfabric recharting.

The existing literal original high-side criterion in Lean RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean is STILL conditional on LiteralFarMinusMuUniformHighEstimate: retain the same selected W and prove the signed literal far pair source minus the exact full mu integral and the paid local slack is strictly below the post-sixth residual margin for every target off-line zeta zero. An equivalent original local terminal is H_W+S_W<4 d_W(rho)+I_W. The new signed far q-brackets are a proven possible ingredient but do NOT control the entire far source, nor its sum against the actual zeta-zero multiplicities, smooth mu and compensation target.

The original existing Synthesis/RiemannZetaMuZeroCountOneSided.lean DOES give N(A,B)>=integral_A^B mu-C*(log(A+3)+log(B+4)) for sufficiently large A and some C>=0. These brackets map to original ordinates A=t+(t/16)*(4-2sqrtR) and B=t+(t/16)*(4-sqrtR/2), and similarly on the other side. A lower count is not a signed-weighted sum, and its original C,T0 are existential, so this work DOES NOT claim a numerical count at fixed t=10^14.

**Remaining exact P0 / GRH min-cut:** form the full signed FarExact consumer on ACTUAL zeta zeros and literal mu, split by the proven q-band sets and complement, and prove a strict weighted bound against the SAME W.postSixthTerminalResidualMargin including original V4/6th/8th charges and local slack. No generic carrier theorem or further integer phase quotient substitutes for this estimate. No full RH or GRH theorem, and no Lean/Agda kernel receipt.
