module DASHI.Analysis.RiemannReflectionPairBlockExact where

------------------------------------------------------------------------
-- SOURCE / FRONTIER CALIBRATION
--
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026).
-- DOI: 10.48550/arXiv.2608.13637.
--
-- The paper uses a finite compression of Weil's Hermitian form and Sylvester
-- inertia to control off-line reflection pairs.  This module does NOT identify
-- the block below with a block of that Hermitian form.  Instead it proves the
-- minimal algebraic lesson needed for the next source-facing investigation:
-- a swap-symmetric inverse-pair block can have a trace-like observable that
-- forgets the pair completely while a second symmetric observable retains a
-- nonzero reflection defect.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)

import DASHI.Analysis.RiemannReflectionOrbitDefectExact as Orbit

------------------------------------------------------------------------
-- Matrix-shaped carrier [[diagonal, offDiagonal], [offDiagonal, diagonal]].
-- Swap conjugation is definitionally trivial on this canonical symmetric form.
------------------------------------------------------------------------

record SwapSymmetric2x2 : Set where
  constructor symmetric2x2
  field
    diagonal : Nat
    offDiagonal : Nat

open SwapSymmetric2x2 public

swapConjugate : SwapSymmetric2x2 → SwapSymmetric2x2
swapConjugate (symmetric2x2 a b) = symmetric2x2 a b

swapConjugateInvariant :
  (b : SwapSymmetric2x2) → swapConjugate b ≡ b
swapConjugateInvariant (symmetric2x2 a b) = refl

------------------------------------------------------------------------
-- Canonical block attached to a reflection orbit.
--
-- The diagonal is deliberately zero and the off-diagonal stores orbit
-- magnitude.  Thus a trace-like statistic sees zero for every orbit, while
-- the squared off-diagonal retains the orientation-blind defect.
------------------------------------------------------------------------

reflectionDefectBlock : Orbit.CentredReflectionState → SwapSymmetric2x2
reflectionDefectBlock x = symmetric2x2 zero (Orbit.orbitMagnitude x)

reflectionDefectBlockInvariant :
  (x : Orbit.CentredReflectionState) →
  reflectionDefectBlock (Orbit.reflect x) ≡ reflectionDefectBlock x
reflectionDefectBlockInvariant Orbit.criticalCentre = refl
reflectionDefectBlockInvariant (Orbit.offLine Orbit.left n) = refl
reflectionDefectBlockInvariant (Orbit.offLine Orbit.right n) = refl

traceLike : SwapSymmetric2x2 → Nat
traceLike (symmetric2x2 a b) = a + a

determinantMagnitudeLike : SwapSymmetric2x2 → Nat
determinantMagnitudeLike (symmetric2x2 a b) = b * b

reflectionBlockTraceAlwaysZero :
  (x : Orbit.CentredReflectionState) →
  traceLike (reflectionDefectBlock x) ≡ zero
reflectionBlockTraceAlwaysZero Orbit.criticalCentre = refl
reflectionBlockTraceAlwaysZero (Orbit.offLine Orbit.left n) = refl
reflectionBlockTraceAlwaysZero (Orbit.offLine Orbit.right n) = refl

reflectionBlockDeterminantMagnitudeIsSquaredDefect :
  (x : Orbit.CentredReflectionState) →
  determinantMagnitudeLike (reflectionDefectBlock x)
    ≡ Orbit.squaredDefect x
reflectionBlockDeterminantMagnitudeIsSquaredDefect x = refl

reflectionBlockDefectInvariant :
  (x : Orbit.CentredReflectionState) →
  determinantMagnitudeLike (reflectionDefectBlock (Orbit.reflect x))
    ≡ determinantMagnitudeLike (reflectionDefectBlock x)
reflectionBlockDefectInvariant Orbit.criticalCentre = refl
reflectionBlockDefectInvariant (Orbit.offLine Orbit.left n) = refl
reflectionBlockDefectInvariant (Orbit.offLine Orbit.right n) = refl

zeroBlockDefectImpliesCriticalCentre :
  (x : Orbit.CentredReflectionState) →
  determinantMagnitudeLike (reflectionDefectBlock x) ≡ zero →
  x ≡ Orbit.criticalCentre
zeroBlockDefectImpliesCriticalCentre x defectZero =
  Orbit.zeroDefectImpliesCriticalCentre x defectZero

------------------------------------------------------------------------
-- Concrete falsifier for "inverse pairing erases everything".
-- Both examples have the same trace-like value zero, but retain different
-- orientation-blind defect magnitudes.
------------------------------------------------------------------------

nearPair : Orbit.CentredReflectionState
nearPair = Orbit.offLine Orbit.left 0

farPair : Orbit.CentredReflectionState
farPair = Orbit.offLine Orbit.right 2

nearAndFarTraceCollide :
  traceLike (reflectionDefectBlock nearPair)
    ≡ traceLike (reflectionDefectBlock farPair)
nearAndFarTraceCollide = refl

nearPairDefectIsOne :
  determinantMagnitudeLike (reflectionDefectBlock nearPair) ≡ 1
nearPairDefectIsOne = refl

farPairDefectIsNine :
  determinantMagnitudeLike (reflectionDefectBlock farPair) ≡ 9
farPairDefectIsNine = refl

record ReflectionPairBlockBoundary : Set where
  field
    swapSymmetricBlockConstructed : Bool
    traceBlindnessConstructed : Bool
    defectRetentionConstructed : Bool
    actualWeilBlockIdentified : Bool
    SylvesterInertiaDerivedForThisBlock : Bool
    analyticDistanceMomentBoundDerived : Bool

reflectionPairBlockBoundary : ReflectionPairBlockBoundary
reflectionPairBlockBoundary = record
  { swapSymmetricBlockConstructed = true
  ; traceBlindnessConstructed = true
  ; defectRetentionConstructed = true
  ; actualWeilBlockIdentified = false
  ; SylvesterInertiaDerivedForThisBlock = false
  ; analyticDistanceMomentBoundDerived = false
  }
