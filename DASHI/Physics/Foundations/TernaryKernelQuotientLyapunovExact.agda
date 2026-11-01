module DASHI.Physics.Foundations.TernaryKernelQuotientLyapunovExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- A concrete kernel is defined first on the five inversion orbits and then
-- lifted back to a canonical nine-sheet representative.  Quotient descent is
-- therefore an exact theorem rather than the phrase "up to quotient".

quotientKernel : Triadic.NineOrbit → Triadic.NineOrbit
quotientKernel Triadic.zeroOrbit = Triadic.zeroOrbit
quotientKernel Triadic.firstAxisOrbit = Triadic.zeroOrbit
quotientKernel Triadic.secondAxisOrbit = Triadic.zeroOrbit
quotientKernel Triadic.equalSignOrbit = Triadic.firstAxisOrbit
quotientKernel Triadic.oppositeSignOrbit = Triadic.firstAxisOrbit

sheetKernel : Triadic.NineSheet → Triadic.NineSheet
sheetKernel sheet =
  Triadic.canonicalNineRepresentative
    (quotientKernel (Triadic.quotientNine sheet))

sheetKernelDescends :
  (sheet : Triadic.NineSheet) →
  Triadic.quotientNine (sheetKernel sheet)
  ≡
  quotientKernel (Triadic.quotientNine sheet)
sheetKernelDescends sheet =
  Triadic.canonicalRepresentativeReturnsOrbit
    (quotientKernel (Triadic.quotientNine sheet))

sheetKernelRespectsGlobalInversion :
  (sheet : Triadic.NineSheet) →
  sheetKernel (Triadic.negateNine sheet) ≡ sheetKernel sheet
sheetKernelRespectsGlobalInversion sheet =
  cong
    (λ orbit →
      Triadic.canonicalNineRepresentative (quotientKernel orbit))
    (Triadic.quotientNineNegationInvariant sheet)

------------------------------------------------------------------------
-- Finite-state iteration alone permits nontrivial cycles.  This explicit
-- orbit kernel has period two on the two axis orbits.

oscillatingKernel : Triadic.NineOrbit → Triadic.NineOrbit
oscillatingKernel Triadic.zeroOrbit = Triadic.zeroOrbit
oscillatingKernel Triadic.firstAxisOrbit = Triadic.secondAxisOrbit
oscillatingKernel Triadic.secondAxisOrbit = Triadic.firstAxisOrbit
oscillatingKernel Triadic.equalSignOrbit = Triadic.equalSignOrbit
oscillatingKernel Triadic.oppositeSignOrbit = Triadic.oppositeSignOrbit

oscillatingKernelPeriodTwo :
  (orbit : Triadic.NineOrbit) →
  oscillatingKernel (oscillatingKernel orbit) ≡ orbit
oscillatingKernelPeriodTwo Triadic.zeroOrbit = refl
oscillatingKernelPeriodTwo Triadic.firstAxisOrbit = refl
oscillatingKernelPeriodTwo Triadic.secondAxisOrbit = refl
oscillatingKernelPeriodTwo Triadic.equalSignOrbit = refl
oscillatingKernelPeriodTwo Triadic.oppositeSignOrbit = refl

oscillationIsNontrivial :
  oscillatingKernel Triadic.firstAxisOrbit ≡ Triadic.firstAxisOrbit → ⊥
oscillationIsNontrivial ()

------------------------------------------------------------------------
-- A strict finite rank supports the stronger convergence result for the
-- declared quotient kernel.  Every orbit reaches the zero fixed class in at
-- most two steps.

orbitRank : Triadic.NineOrbit → Nat
orbitRank Triadic.zeroOrbit = 0
orbitRank Triadic.firstAxisOrbit = 1
orbitRank Triadic.secondAxisOrbit = 1
orbitRank Triadic.equalSignOrbit = 2
orbitRank Triadic.oppositeSignOrbit = 2

firstAxisRankDropsExactly :
  orbitRank Triadic.firstAxisOrbit
  ≡
  suc (orbitRank (quotientKernel Triadic.firstAxisOrbit))
firstAxisRankDropsExactly = refl

secondAxisRankDropsExactly :
  orbitRank Triadic.secondAxisOrbit
  ≡
  suc (orbitRank (quotientKernel Triadic.secondAxisOrbit))
secondAxisRankDropsExactly = refl

equalSignRankDropsExactly :
  orbitRank Triadic.equalSignOrbit
  ≡
  suc (orbitRank (quotientKernel Triadic.equalSignOrbit))
equalSignRankDropsExactly = refl

oppositeSignRankDropsExactly :
  orbitRank Triadic.oppositeSignOrbit
  ≡
  suc (orbitRank (quotientKernel Triadic.oppositeSignOrbit))
oppositeSignRankDropsExactly = refl

quotientKernelReachesFixedClassInTwo :
  (orbit : Triadic.NineOrbit) →
  quotientKernel (quotientKernel orbit) ≡ Triadic.zeroOrbit
quotientKernelReachesFixedClassInTwo Triadic.zeroOrbit = refl
quotientKernelReachesFixedClassInTwo Triadic.firstAxisOrbit = refl
quotientKernelReachesFixedClassInTwo Triadic.secondAxisOrbit = refl
quotientKernelReachesFixedClassInTwo Triadic.equalSignOrbit = refl
quotientKernelReachesFixedClassInTwo Triadic.oppositeSignOrbit = refl

zeroOrbitIsFixed :
  quotientKernel Triadic.zeroOrbit ≡ Triadic.zeroOrbit
zeroOrbitIsFixed = refl

------------------------------------------------------------------------
-- Code length is a separate functional.  Equality in this finite example is
-- checked explicitly; it is not inferred from fixed-point status.

mdlCodeLength : Triadic.NineOrbit → Nat
mdlCodeLength Triadic.zeroOrbit = 1
mdlCodeLength Triadic.firstAxisOrbit = 3
mdlCodeLength Triadic.secondAxisOrbit = 3
mdlCodeLength Triadic.equalSignOrbit = 5
mdlCodeLength Triadic.oppositeSignOrbit = 5

canonicalKernelReducesDiagonalCodeLength :
  mdlCodeLength (quotientKernel Triadic.equalSignOrbit) ≡ 3
  ×
  mdlCodeLength Triadic.equalSignOrbit ≡ 5
canonicalKernelReducesDiagonalCodeLength = refl , refl

record TernaryKernelQuotientLyapunovBoundary : Set where
  constructor ternaryKernelQuotientLyapunovBoundary
  field
    arbitraryWeightsGuaranteeSpatialEquivariance : Bool
    arbitraryWeightsGuaranteeSpatialEquivarianceIsFalse :
      arbitraryWeightsGuaranteeSpatialEquivariance ≡ false

    finiteStateIterationGuaranteesFixedPointConvergence : Bool
    finiteStateIterationGuaranteesFixedPointConvergenceIsFalse :
      finiteStateIterationGuaranteesFixedPointConvergence ≡ false

    quotientDescentNeedsNoCompatibilityProof : Bool
    quotientDescentNeedsNoCompatibilityProofIsFalse :
      quotientDescentNeedsNoCompatibilityProof ≡ false

    fixedPointAutomaticallyMinimisesDescriptionLength : Bool
    fixedPointAutomaticallyMinimisesDescriptionLengthIsFalse :
      fixedPointAutomaticallyMinimisesDescriptionLength ≡ false

open TernaryKernelQuotientLyapunovBoundary public

canonicalTernaryKernelQuotientLyapunovBoundary :
  TernaryKernelQuotientLyapunovBoundary
canonicalTernaryKernelQuotientLyapunovBoundary =
  ternaryKernelQuotientLyapunovBoundary
    false refl
    false refl
    false refl
    false refl
