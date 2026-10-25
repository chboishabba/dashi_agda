# Pickover / Eisenstein-nine / CRT / RH: source-first max-cut (2026-10-25)

## Scope, attribution, and current status

This is a narrow composition over existing DASHI owners, not a new fibre ontology.

- Classical sources: Eisenstein integers and the relation omega^2+omega+1=0; Smith normal form, the Chinese remainder theorem, cyclotomic polynomials, finite Fourier/character theory, Riemann (1859), Machin's pi formula (1706), and Hardy's real Z function.
- DASHI pre-existing owners: `Core.CoarseFineRelativeFibreExact` (reopening); `Algebra.TriadicFiniteArithmetic` (balanced carry); `Algebra.TriadicFiniteArithmeticLaws`; `Algebra.TriadicDepthTwoDFTGroupBridge` and `TriadicDepthTwoCyclotomicDFT` (true C9 DFT); `Moonshine.C3FourierConjugationExact`; `Moonshine.C3RiemannConjugationBridgeExact`; `Mathematics.NumberTheory.RiemannXiSymmetryExact`; `Mathematics.NumberTheory.RiemannCompletedZetaBoundary`; `Analysis.RiemannQuarticDepthFiveX6Rank4BridgeExact`; `Moonshine.JInvariant369RHAtomicTriadicCoefficientCrossPollinationExact`.
- External Lean Mathlib owns its generic zeta, real/complex analysis and, where available in the pinned revision, Hardy Z infrastructure. Existing Lean RH PR #50 and G21 PR #77 retain their original own analytic obligations.
- This tranche: `Mathematics/NumberTheory/EisensteinNineCRTPhaseMaxCutExact.agda` is SOURCE-WRITTEN, NOT kernel-checked in this session. `scripts/check_pickover_eisenstein9_crt.py` has an independently run materially equivalent local Python replay that passed; it is finite computational verification, not an Agda/Lean kernel receipt.
- No RH result, actual zeta-zero coordinate enumeration, Hardy-to-Pickover phase identification, or sin(99^(9999!)) sign is claimed.

## Max-cut A — one concrete ramified nine-layer carrier

Let omega^2+omega+1=0, lambda=1-omega. Then lambda^2=-3 omega, so (lambda^9)=(81 lambda). A Z-basis for the ideal is (81,-81),(0,243) in the (1,omega) basis; determinant 81*243=19683.

For a+b omega, choose the normal-form coordinates

    x = a (mod 81)
    y = a+b (mod 243).

This explicitly identifies the additive quotient with C81 x C243. Its multiplication is

    (x,y)*(u,v) =
      (x*v+y*u-y*v mod 81,
       3*x*v+3*y*u-2*y*v-3*x*u mod 243).

The formulas use representative coordinates and are independent of the chosen representatives. This is an actual concrete ring model, **not** a group isomorphism with C3^9.

The lambda filtration R ⊃ lambda R ⊃ ... ⊃ lambda^9 R=0 has cardinalities

    [19683,6561,2187,729,243,81,27,9,3,1].

Each graded step is one F3 coordinate. The associated graded algebra is F3[t]/(t^9) with t represented by lambda's principal symbol, even though the full ring has nontrivial carries. This is the proper interpretation of the existing 4+5 trit split and the exact coarse/fine reopening law.

The local ring's only idempotents are 0 and 1. The exact finite executable exhaustively enumerates all 19683 elements, confirms this, and checks its 13122 units.

In this ring the integer 99=3^2*11 has lambda-valuation 4, hence (99)^2!=0 while (99)^3=0. Thus 99^(n!)=0 for any n>=3 on this finite quotient. This is strictly a local-ring statement, not real trigonometry.

## Max-cut B — Fourier degeneracy without discarding information

The old char-0 C3 and C9 DFT, inversion and Parseval are already constructed in merged PRs #241, #250, #610; do not reimplement them. Here 3 is not a unit. The normalised idempotent (1+g+g^2)/3 is consequently not defined over R. However, the unnormalised transfer T=1+g+g^2 in R[C3] obeys

    T^2=3T,  T^6=0.

For U=g-1, U^3=3g-3g^2=-3g(g-1) and U^11=0. Modulo 3, U^3=0: F3[C3] ≅ F3[U]/(U^3). This retains nonsemisimple extension/carry information rather than inventing a division by 3.

The comparison of char-0 Fourier projectors versus char-3 nilpotent transfer is a bona fide characteristic-change bridge, not a claim that they are equal operators on the same coefficient ring.

## Max-cut C — decimal cyclotomy and CRT

9999=10^4-1=9*11*101; 1111=11*101; 101=10^2+1.

For E=9999!, exact modular exponentiation verifies:

    99^E mod 9999 = 4950,  4950 ↦ (0,0,1) mod (9,11,101)
    99^E mod 1111 = 506,  506 ↦ (0,1) mod (11,101)
    99^E mod (3^9*11*101) = 2814669 ↦ (0,0,1).

Both selected CRT residues are idempotents. They retain the 101 component and kill the 3/11 components. This nontrivial idempotent lives in a **product ring**; the Eisenstein lambda-local factor itself has no nontrivial idempotents.

The same finite projection persists for 10000!; the apparent round-number gain is a stronger 10-adic congruence, not an improved real-phase certificate.

## Return to RH — defined but distinct zero consumers

Trivial zeta zeros are s=-2,-4,-6,... from the classical functional equation. Nontrivial zeros are zeros in 0<Re(s)<1. The standard entire xi(s) has precisely the nontrivial zeta zeros, since completion cancels the negative-even trivial zeros (and does not introduce the endpoints as zeros). RH states each nontrivial zero satisfies Re(s)=1/2.

Existing DASHI `RiemannXiSymmetryExact` proves the coordinate equality on the critical line, (1-s)=conj(s), but the actual analytic zeta / xi connection is an independent proof obligation. Existing `RiemannCompletedZetaBoundary` and `RiemannAnalyticSubstrate` type these objects and distinguish zeros.

Hardy's Z function provides a real-valued critical-line zero observer with Z(t)=0 iff zeta(1/2+i*t)=0 and |Z(t)|=|zeta(1/2+i*t)|; locate/pin the actual Mathlib implementation before claiming the specific API names in this repo's Lean version. The inspected RH PRs #22/#50/#77 have no native Hardy-specific file. Riemann-Siegel analytic route and RH A1/A2/B/G21 remain separately open.

**Important:** the value 0 of zeta at a zero is additive zero, not the multiplicative identity; 1+omega+omega^2=0 is cyclotomic cancellation, not a Riemann zero. No theorem here identifies these carriers.

## Return to Pickover — a precise remaining terminal consumer

Let alpha=1/(2*pi), S(x)={99x}, E=9999!, and N=99^E. Then

    sign(sin(N)) = positive  iff S^E(alpha) lies in (0,1/2);
    sign(sin(N)) = negative  iff S^E(alpha) lies in (1/2,1).

The boundary cannot occur: N is a positive integer and pi is irrational. In base 99 the decision is the first digit different from 49 after position E: <49 -> positive, >49 -> negative. The exact 9x11 digit chart d=11a+b and centred signed coordinate d-49=11(a-4)+(b-5) is a valid consumer-specific coarse/fine witness. Earlier independent exact Machin rational intervals certify the base9 and base99 decisions at the first seven factorial positions and 9*n! probes through 6! (see conversation audit).

The direct circle power recurrence is **already well-defined**, z_{n+1}=z_n^(99^(n*n!)), z_n=e^(i*99^(n!)). Hopf U(1) fibre retention is a valid faithful representation of the phase. Neither an unqualified finite CRT projection nor a Fourier nilpotent identifies its imaginary sign; there is not yet a certified sparse real-phase evaluation or a proof of computational impossibility.

**Highest-alpha mathematical leaf:** construct a specified analytic invariant or a certified interval for S^E(alpha) that separates it from 1/2, with an explicit complexity budget materially below naive E-position digit extraction. Source-first candidates are the repo's Machin/Bishop pi and Lean exact-real bridge, or genuinely new source-specific symbolic/analytic phase estimates. Do not spend another round rebuilding generic fibres, CRT, C3, or carry.

## Verification

    python3 scripts/check_pickover_eisenstein9_crt.py

An independent equivalent finite Python run passed the full 19683-state test, nine filtration levels, local idempotents, C3 transfer, and both factorial CRT checks. No Agda or Lean executable/kernel receipt was available during this implementation. For kernel validation, run the pinned project Agda compiler against the new module, then use existing relevant regression roots; do not infer kernel verification from a source-written refl or from a passed Python check.

The concrete Agda normal-form functions are a basis for an additional universal quotient/ring-homomorphism theorem. They do not yet prove, internally to Agda, the complete universal quotient ring construction or all ring laws. This is a deliberately explicit finite source-level frontier, not a hidden postulate or an RH/9999 result.


## 2026-10-25 continued max-cut — signed SSP/FRACTRAN × torque × RH roles

### Source reuse rather than a new ontology

- John H. Conway's FRACTRAN supplies the classical positive-integer fractional computation concept; DASHI's signed-SSP instruction/weave code is repo-specific and has distinct evidence/cost semantics.
- Merged torque PR #1164 owns `Physics.Foundations.OrientedThreeAxisBracket369Exact`: the Levi-Civita sign for ordered (output,left,right) triple, balanced trit, and its conjugate C3 character. The bracket has genuine SO3/Hodge consumers but finite orientation alone supplies no force amplitude.
- `Biology.SignedSSPFRACTRANWeaveExact` owns the fifteen Ogg lanes, signed multiplicity and inverse/mediated/forward orientation. `Moonshine.JInvariant369SignedSSPFRACTRANPhaseFibreExact` ALREADY proves signed negation ↔ spectral conjugation.
- `Analysis.RiemannSSP15ProducerMarkedSignedFRACTRANExact` and `RiemannSSP15FilteredProvenanceCapstoneExact` ALREADY own the conditional RH producer-role to signed/pointed execution codec. Its O/j/s -> negative/zero/positive assignment is a CHOSEN role indexing, not an analytic fact about zeros or an external canonical SSP encoding.
- Draft SSP-climbing-gym PR #1139 owns the p-native radix/inverse-limit machine; draft Goldbach 30→29 PR #1214 retains original Mike Dupont/meta-introspector AGPL authorship and signed/weak-stuttering machine work. Neither is vendored or reattributed here.
- `Analysis.PickoverSignedSSPTorquePhaseBridgeExact` adds the explicit datatype intertwiner `Triadic.KernelTrit → BalancedTernary.Trit → OrientedThreeAxisBracket369Exact.BracketVoxel`. It compiles signed negation to torque input reversal modulo the C3 phase and reuses the existing torque reversal theorem rather than rebuilding its 27-case bracket table.
- `Analysis.PickoverRHSSPTorqueRoleBridgeExact` maps the EXISTING conditionally producer-marked O/j/s instructions to phases ζ²/1/ζ, retains the j-role zero instruction effect and its independent pointed prime, and keeps analytic identity unpromoted.

### Literal 99 FRACTRAN submachine

The original integer FRACTRAN fraction `99/1` advances `99^k→99^(k+1)`; its reciprocal `1/99` is enabled at these states exactly for `k≥1`. The prime valuation is sparse:

    v_3(99^k)=2k
    v_11(99^k)=k
    v_p(99^k)=0 for every other SSP/Ogg lane.

No fictitious prime-99 or prime-101 Ogg lane is introduced. The external 101 CRT lane is genuinely absent from SSP15. The Agda signed valuation is a symbolic carrier for this prime-exponent orbit; the 3-token positive weave word `introducePrime 3; introducePrime 3; introducePrime 11` is a provenance-preserving PRESENTATION and the aggregate effect is *not* silently identified with an integer FRACTRAN interpreter.

The coarse sign observation at both prime-3 and prime-11 lanes is `positive` for all `k≥1`. Our independently exact Machin intervals certify opposite REAL sine signs for `99^1` and `99^6`. Thus coarse signed SSP polarity cannot, by itself, determine even the small-exponent real phase. Full magnitudes or richer data might, if a valid real attachment exists.

### Strong new quantitative torsion / torque correspondence

Let `ζ_m=exp(2πi/m)`. From `99^(9999!)≡4950 mod9999`, the induced circle power map acts exactly on `μ9999`:

    P(ζ_9999^k)=ζ_9999^(4950 k)=ζ_101^(50 k)
    P²=P, kernel μ99, image μ101.

The generator `ζ_9999` maps to `ζ_101^50`. The primitive generator `ζ_101 = ζ_9999^99` is fixed, since `50*99≡1 mod101`.

Define a signed planar **oriented-area** observable on `μ101`:

    sign det((1,0), (cos(2πt/101),sin(2πt/101)))
     = zero if t=0
     = positive if 1≤t≤50
     = negative if 51≤t≤100.

The oriented area is exactly the z-component of the R³ wedge/cross of two coplanar unit vectors, connecting to the selected torque/Hodge right-hand-rule convention. Inversion t→-t reverses the sign, matching the signed-SSP reciprocal and torque-bracket reversal laws. Zero remains a neutral third state; it is not forced into + or −.

The Python audit exhausts all 9999 input torsion phases: **101 outputs**, every output has **99 preimages**, with **4950 positive / 99 neutral / 4950 negative** projected orientations. These are integer-only tests of the actual finite circle-group action, not approximations to `e^i`.

The final same-object statement is still:

    e^i is NOT known to be in μ9999;
    orientation(P(e^i)) cannot be read from P|μ9999.

An analytic attachment to the original phase must supply a signed semicircle separation or a rigorously bounded approximation. Neither the exact R³ torque wedge nor the 101 torsion projector supplies it automatically.

### What returns to RH

The three historical O/j/s source *roles* are exactly encoded as a negative/neutral/positive signed SSP tuple once the selected primitive-row producer certificate is supplied. This is an ACTION/PROVENANCE theorem on the role-code state, NOT the assertion that the analytic Riemann ζ zeros partition into three equal sign roles. The actual RH G2 signed method must attach to the literal determinant taper `q(u)` or the already-reduced scalar target; `RiemannG2C3MonsterEquivarianceAuditExact` warns that another raw three-channel C3 transform cannot discharge the remaining analytic q-level sign.

**True next leaves:** (1) exact-head Agda kernel result for two new adapters plus the finite quotient (pending); (2) if RH, same-zeta Hardy/ξ multiplicity-aware zero consumer or the G21 scalar moment/TP2/determinant estimate; (3) if Pickover, a direct REAL phase-separating witness for `sin(99^(9999!))`. Do not confuse code, chosen role index, finite torsion, executable test and analytic proof authority.

Verification (independently materially equivalent local Python PASS):

    python3 scripts/check_pickover_eisenstein9_crt.py
    python3 scripts/check_pickover_machin_factorial_phase.py
    python3 scripts/check_pickover_ssp_torque_101.py

The dedicated workflow now invokes the three scripts and focused Agda roots on the PR branch. No exact-head CI/kernel receipt has been observed in this session.
