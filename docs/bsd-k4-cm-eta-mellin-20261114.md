# BSD selected-curve K4 → K3 high-alpha cross-programme implementation cut
## 14 November 2026 — Agda PR #1500, Lean PR #107

Selected curve ONLY: E : y² = x³-x, conductor 32, discriminant 64,
j=1728 and CM by Z[i]. No universal BSD claim. All new Agda
modules remain SOURCE-WRITTEN until local Agda 2.9 checking.

### What was actually already in-repo

- DASHI/Wikimedia/IbrahimDedekindEtaQPochhammerPentagonalSnowballExact.agda:
  Dedekind eta / q-Pochhammer attribution and *finite* identity routes;
  its own boundary says the infinite product and zero-free analysis
  are not constructed. It is **not** an analytic Dedekind eta proof.
- DASHI/Mathematics/Automorphic/MellinSplitFunctionalEquationExact.agda:
  algebraic lower/upper Mellin reflection **given** actual
  substitution identities; toy finite rational instance only.
- DASHI/Mathematics/Automorphic/EllipticModularityReceiptExact.agda:
  maps *supplied* modular coefficient equality into finite Euler
  product equality; no selected level-32 normalized newform built.
- DASHI/Mathematics/Automorphic/EllipticDirichletBaselMajorantExact.agda:
  Bishop comparison theorem, not central s=1 original coefficients.
- DASHI/Mathematics/Arithmetic/EllipticCurveSmallPrimeFrobeniusExact.agda:
  seven literal checked E(Fp) point-count traces for p=3,5,7,11,
  13,17,19. These are genuine finite original-curve receipts.
- DASHI/Mathematics/Automorphic/EllipticSelectedHeckePrimePowerExact.agda
  (PR #1500): checked-row prime-power Hecke recurrence.
- Lean Synthesis/MillenniumBSDMathlibLFunctionWeld.lean:
  **actual** cmWeierstrass.LFunction, all-n coefficient
  cmAllNCoefficient and cmLSeries. These were already present
  in the Lean repository and should NOT be recreated as abstract
  new coefficient functions.
- Lean Synthesis/MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact.lean
  (PR #107): consumes mathlib v4.28's genuine analytic Dedekind eta
  to source-write upper-half-plane nonzero and differentiability
  for eta(4z)^2 eta(8z)^2. These declarations have NOT been locally
  kernel-accepted.

### NEW original Agda source owners on PR #1500

1. EllipticCMJacobiThetaCheckedRowsExact.agda:
   actual finite Gaussian/Jacobi q-coefficient computation:
   a_k = sum_{(n,m): (2n+1)^2+4m^2=k}
         (-1)^n(2n+1) * {1 if m=0, 2(-1)^m otherwise}.
   All original seven E(Fp) Frobenius coefficients equal this
   theta candidate, plus q^1=1 and the original a_9=a_3^2-3.
   For indices <=19, only n=0,1 and m=0,1,2 are needed.
   Formal ALL-N Jacobi triple-product identity is NOT supplied.

2. EllipticCMLevel32EtaNewmanArithmeticExact.agda:
   r4=r8=2 at N=32. Checks literally
     4r4+8r8=24; (32/4)r4+(32/8)r8=24;
     (4^r4)(8^r8)=32^2; weight=(r4+r8)/2=2;
     leading q exponent is 1.
   Analytic eta-quotient modularity and cusp holomorphy remain open.

3. EllipticCMLevel32LigozatCuspArithmeticExact.agda:
   all SIX divisor denominators d=1,2,4,8,16,32,
   with actual gcd(d,32/d), gcd(d,4), gcd(d,8).
   The exact Ligozat cross-multiplied cusp order calculation
   gives order 1 in each case; d=4,8 each yield two cusps,
   for eight total cusps. Importing the analytic Ligozat
   theorem is still required.

4. EllipticCMLevel32GenusOneArithmeticExact.agda:
   SL2 index μ=48, e2=e3=0, eight cusps; classical
   genus formula arithmetic gives g(X0(32))=1.
   **Crucial shortcut:** dim S_2(Γ0(32))=1.
   An actual cusp-form theorem for this eta product and
   modularity for the original E gives identity from q1=1;
   no new all-prime coefficient comparison is necessary
   for this same-object equality. Modular curve dimension
   theorem remains an independent source dependency.

5. EllipticCMLevel32FrickeMellinExact.agda:
   square-root-free algebra given actual squared eta inversion:
     eta(i/(8t))² = 8t eta(8it)²,
     eta(i/(4t))² = 4t eta(4it)²
   implies
     f32(i/(32t)) = 32t² f32(it).
   Also consumes the EXISTING MellinSplitData for the
   central-fixed reflection epsilon=+1, obtaining
   completed central transform = 2 * upper tail.
   The ANALYTIC eta inversion, actual Bishop integral
   and original L(E,1) identification are still OPEN.

### Exact numerical assays (NOT Agda theorems)

- scripts/check_bsd_level32_cm_eta_theta_exact.py compares
  q * product(1-q^(4n))²(1-q^(8n))², the Gaussian/Jacobi
  two-factor coefficient formula, and independent
  E(Fp) point counts. Independently run through q^256:
  257/257 integer coefficients match, 53/53 odd primes
  match direct E(Fp) counts, all 7 original Agda rows match.
- scripts/check_bsd_level32_mellin_fricke.py uses mpmath
  to check f32(i/(32t))=32t² f32(it) and evaluate
      L(E,1) = 4π ∫_(1/sqrt(32))^∞ f32(it) dt.
  Independently computed
      0.6555143885730299526162098974727798534206887378579...
  matching external LMFDB data for this ORIGINAL curve.
  All integrand samples positive. Strict positivity is a
  mathematical consequence of the classical eta product and
  Mellin equality, but is NOT yet an Agda formal theorem.

### Mathematical K4 proof chain — minimal original maximum cut

A. Dedekind eta actual upper-half-plane carrier in Agda Bishop
   (or a type-/proof-preserving transport from mathlib);
   Jacobi factor identity for ALL q-coefficients.
B. Apply Newman eta-quotient modularity, Ligozat cusp theorem
   to the concrete arithmetic certificates above.
C. Build actual dim S2 Gamma0(32)=g(X0(32))=1 from standard
   genus/dimension theorem and the proven numeric data.
D. Apply source-backed modularity of E:y²=x³-x. Both
   f_E and eta(4τ)^2 eta(8τ)^2 normalized q1=1;
   conclude exact equality in the SAME modular-form space.
E. Prove eta inversion on the Bishop/complex carrier and
   `f32(it)>0` on ALL t>0, via positive infinite q product
   plus nonvanishing/limit. Compute Fricke in the source.
F. Prove integrability and actual Mellin equality at s=1:
     L(E,1) = 2π∫₀^∞ f32(it)dt
            = 4π∫_(1/sqrt(32))^∞ f32(it)dt > 0.
   This gives analytic rank zero WITHOUT an exact Gamma/Beta
   value; the latter is needed only for stronger coefficient
   normalisation and full BSD formula.

### K3 (shortest existing real theorem route)

- Michael Stoll, EllipticCurves/MordellWeil.lean:
  WeierstrassCurve.Affine.fg_point_of_numberField, genuine
  Mordell–Weil finite generation, not an assumed flag.
  Pin: MichaelStollBayreuth/EllipticCurves commit
  bad38e242a187dea006fc302a0ef0fd53eedd4ba.
- Lean PR #107 already owns actual
  rationalProjectivePointAddEquivMathlib and
  cmEveryRationalPoint_eq_twoTorsion_add_double, plus
  cmSelectedOriginalMordellWeil_ZRank_zero with a genuine
  [AddGroup.FG RationalProjectivePoint] premise.
- Integration/MillenniumBSDStollMordellWeilAdapter.lean
  opts in to the donor; scripts/bsd_stoll_mw_isolated_verify.sh
  stages matching Lean/mathlib 4.35.0 in an isolated worktree.
  Original root currently Lean 4.35.0-rc3 and mathlib v4.28.0,
  so do not import the adapter into Synthesis yet.
- Independent direct Fermat/no-congruent-one route remains
  available from CMUnitAreaTriangleCurveWeldExact, but is
  less immediately reusable than the actual donor theorem.
- Need an actual *local* Lean kernel proof and independent
  Agda same-object transport. Source-written != accepted.

### K1, K2, K5 unaffected walls

K1: actual Q2 and real local continuous E[2]-valued Kummer,
sign and v2 invariants, good-prime unramified support.
K2: E(Qbar)-coefficient global/local LES and classical Sha[2].
K5: odd-primary Sha, actual period/Tamagawa/leading
coefficient and universal BSD; a selected L(E,1)>0 proof does
not prove the universal conjecture or full Sha=0.

### Local acceptance

Agda modules:
  bash scripts/check_bsd_agda_k1_k5_local_maxcut.sh
Numerical checks (not golden proofs):
  python3 scripts/check_bsd_level32_cm_eta_theta_exact.py --cutoff 256
  python3 scripts/check_bsd_level32_mellin_fricke.py --dps 65 --terms 110
Lean real MW donor:
  bash scripts/bsd_stoll_mw_isolated_verify.sh

No Agda/Lean/Lake/Nix executable in this execution session.
No source was upgraded to kernel-accepted; PRs remain DRAFT.

External mathematical attribution:
LMFDB elliptic curve 32.a3 / newform 32.2.a.a;
Huber–Liu–McLaughlin–Ye–Yuan–Zhang (CM eta);
Newman/Gordon–Hughes eta-quotient criterion;
Ligozat cusp orders; Jacobi theta product formulas;
Michael Stoll's Mordell–Weil formalization.


### Extended exact-integer independent assay (14 Nov)

Independently reran the TWO finite q-coefficient algorithms through
degree 1024 (beyond the script's default cutoff of 256):
- 1025/1025 coefficient entries agree for the selected
  eta(4τ)²eta(8τ)² q-product and explicit Jacobi/Gaussian theta sum;
- 171/171 odd-prime coefficients through 1024 agree with
  **independent direct point counting** of y²=x³-x in F_p;
- all indices 0<=n<=1024 with n % 4 != 1 have coefficient 0;
- the good-prime square recurrence a_(p²)=a_p²-p agrees for
  every p with p²<=1024.
- all six selected d|32 Ligozat cusp arithmetic checks
  agree with the exact gcd formula and yield cusp order 1.

This is computational testing, not kernel acceptance or an
all-n q-series proof. Reproduce the expanded test with:
  python3 scripts/check_bsd_level32_cm_eta_theta_exact.py --cutoff 1024

### One-dimensional normalized all-n algebraic compiler

`EllipticCMNormalizedOneDimensionalQSeriesExact.agda` proves
`normalizedScalarIsOne` and
`normalizedOneDimensionalAllNCoefficientsAgree`:
if two rational Fourier coefficient families f,g are PROVED
to lie in the same one-dimensional cusp-form line,
so f_n=c*g_n for ALL n, and f_1=g_1=1, then c=1 and
every coefficient agrees. This avoids a second Hecke-prime
reconstruction, while making the missing modular-space
proportionality theorem explicit rather than inserting a
false/assumed instance.
