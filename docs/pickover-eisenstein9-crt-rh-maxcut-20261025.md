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
