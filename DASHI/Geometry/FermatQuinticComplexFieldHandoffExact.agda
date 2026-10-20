module DASHI.Geometry.FermatQuinticComplexFieldHandoffExact where

-- Explicit complex carrier specialization of the Fermat gradient theorem.
-- Uses the repository's ConcreteComplex, not a new synthetic complex type.
-- Missing power-integrality and characteristic-zero cancellations are
-- *named witnesses*; no false "concrete complex field is solved" claim.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Analysis.ConcreteComplex as C
import DASHI.Analysis.ConstructiveRealSpine as R
import DASHI.Geometry.FermatQuinticGradientNonvanishingExact as Fermat
import DASHI.Geometry.FermatQuinticJacobianCriterionHandoffExact as Jacobian

fourth : {R0 : R.ConstructedOrderedCompleteReal} →
  C.ComplexPair R0 → C.ComplexPair R0
fourth z = C._*C_ (C._*C_ z z) (C._*C_ z z)

timesFive : {R0 : R.ConstructedOrderedCompleteReal} →
  C.ComplexPair R0 → C.ComplexPair R0
timesFive z =
  C._+C_ z (C._+C_ z (C._+C_ z (C._+C_ z z)))

record ComplexQuinticCancellation
  (R0 : R.ConstructedOrderedCompleteReal) : Set₁ where
  field
    fourthZero :
      (z : C.ComplexPair R0) →
      fourth z ≡ C.zeroC → z ≡ C.zeroC
    fiveZero :
      (z : C.ComplexPair R0) →
      timesFive z ≡ C.zeroC → z ≡ C.zeroC

open ComplexQuinticCancellation public

-- Shared integral-domain cancellation cut: one square-zero elimination
-- proves fourth-power cancellation by iteration. Useful outside CY3,
-- including Hodge/complex-polynomial consumers.
record ComplexReducedAlgebra (R0 : R.ConstructedOrderedCompleteReal) : Set₁ where
  field
    squareZero :
      (z : C.ComplexPair R0) →
      C._*C_ z z ≡ C.zeroC → z ≡ C.zeroC
    fiveTorsionFree :
      (z : C.ComplexPair R0) →
      timesFive z ≡ C.zeroC → z ≡ C.zeroC

open ComplexReducedAlgebra public

cancellationFromReducedAlgebra :
  (R0 : R.ConstructedOrderedCompleteReal) →
  ComplexReducedAlgebra R0 → ComplexQuinticCancellation R0
cancellationFromReducedAlgebra R0 A = record
  { fourthZero = λ z eq →
      squareZero A z
        (squareZero A (C._*C_ z z) eq)
  ; fiveZero = fiveTorsionFree A
  }

complexQuinticField :
  (R0 : R.ConstructedOrderedCompleteReal) →
  ComplexQuinticCancellation R0 → Fermat.QuinticField
complexQuinticField R0 laws = record
  { Scalar = C.ComplexPair R0
  ; zero = C.zeroC
  ; fourthPower = fourth
  ; fiveTimes = timesFive
  ; fourthPowerZero = fourthZero laws
  ; fiveTimesZero = fiveZero laws
  }

-- The actual selected ComplexPair supplies the coordinates and operations.
-- Characteristic-zero cancellation is not silently inferred from its name.
complexFermatGradientNonvanishing :
  (R0 : R.ConstructedOrderedCompleteReal) →
  (laws : ComplexQuinticCancellation R0) →
  (z : Fermat.ProjectiveFiveCoordinates (complexQuinticField R0 laws)) →
  Fermat.QuinticGradientZero (complexQuinticField R0 laws) z → ⊥
complexFermatGradientNonvanishing R0 laws =
  Fermat.fermatQuinticHasNoSimultaneousGradientZero
    (complexQuinticField R0 laws)

complexFermatSmoothConditional :
  (R0 : R.ConstructedOrderedCompleteReal) →
  (laws : ComplexQuinticCancellation R0) →
  (J : Jacobian.ProjectiveJacobianCriterion (complexQuinticField R0 laws)) →
  (z : Fermat.ProjectiveFiveCoordinates (complexQuinticField R0 laws)) →
  Jacobian.SmoothAt J z
complexFermatSmoothConditional R0 laws J =
  Jacobian.fermatSmoothAtEveryProjectivePoint (complexQuinticField R0 laws) J
