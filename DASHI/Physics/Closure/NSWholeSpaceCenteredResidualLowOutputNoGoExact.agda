module DASHI.Physics.Closure.NSWholeSpaceCenteredResidualLowOutputNoGoExact where

------------------------------------------------------------------------
-- A / CENTERED RESIDUAL DOES NOT VANISH WITH LOW OUTPUT
--
-- For a continuous resonant pair write
--
--   p = c + y,
--   q = c - y,
--   xi = p + q = 2 c.
--
-- Then
--
--   p - q = 2 y,
--
-- independently of c.  Therefore the centered residual
--
--   C = |p-q|^2
--
-- can remain nonzero as xi -> 0.  The periodic centered-resolvent residual
-- s=(nu/2)(C_alpha+C_beta) consequently cannot be used, without additional
-- state geometry, as a source of output-frequency vanishing.
--
-- This is the exact continuous no-go that prevents an invalid identification
-- of the resolvent opposite-shift variable h with |xi|.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean

add :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  Euclidean.R3Frequency
add a b =
  Euclidean.r3-frequency
    (BishopReal._+_ (Euclidean.x a) (Euclidean.x b))
    (BishopReal._+_ (Euclidean.y a) (Euclidean.y b))
    (BishopReal._+_ (Euclidean.z a) (Euclidean.z b))

negate :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency
negate a =
  Euclidean.r3-frequency
    (BishopReal.-_ (Euclidean.x a))
    (BishopReal.-_ (Euclidean.y a))
    (BishopReal.-_ (Euclidean.z a))

subtract :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  Euclidean.R3Frequency
subtract a b = add a (negate b)

scaleTwo :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency
scaleTwo a =
  Euclidean.r3-frequency
    (BishopReal._+_ (Euclidean.x a) (Euclidean.x a))
    (BishopReal._+_ (Euclidean.y a) (Euclidean.y a))
    (BishopReal._+_ (Euclidean.z a) (Euclidean.z a))

record R3Equivalent
    (left right : Euclidean.R3Frequency) : Set where
  constructor r3-equivalent
  field
    xEquivalent :
      BishopReal._≃_ (Euclidean.x left) (Euclidean.x right)
    yEquivalent :
      BishopReal._≃_ (Euclidean.y left) (Euclidean.y right)
    zEquivalent :
      BishopReal._≃_ (Euclidean.z left) (Euclidean.z right)

open R3Equivalent public

centeredPlus :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  Euclidean.R3Frequency
centeredPlus center displacement = add center displacement

centeredMinus :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  Euclidean.R3Frequency
centeredMinus center displacement = subtract center displacement

centeredOutputIsDoubleCenter :
  (center displacement : Euclidean.R3Frequency) →
  R3Equivalent
    (add
      (centeredPlus center displacement)
      (centeredMinus center displacement))
    (scaleTwo center)
centeredOutputIsDoubleCenter center displacement =
  let open BishopP.ℝ-Solver
  in
  r3-equivalent
    (solve 2
      (λ c y → (c ⊕ y) ⊕ (c ⊖ y) ⊜ c ⊕ c)
      BishopP.≃-refl
      (Euclidean.x center) (Euclidean.x displacement))
    (solve 2
      (λ c y → (c ⊕ y) ⊕ (c ⊖ y) ⊜ c ⊕ c)
      BishopP.≃-refl
      (Euclidean.y center) (Euclidean.y displacement))
    (solve 2
      (λ c y → (c ⊕ y) ⊕ (c ⊖ y) ⊜ c ⊕ c)
      BishopP.≃-refl
      (Euclidean.z center) (Euclidean.z displacement))

centeredDifferenceIsDoubleDisplacement :
  (center displacement : Euclidean.R3Frequency) →
  R3Equivalent
    (subtract
      (centeredPlus center displacement)
      (centeredMinus center displacement))
    (scaleTwo displacement)
centeredDifferenceIsDoubleDisplacement center displacement =
  let open BishopP.ℝ-Solver
  in
  r3-equivalent
    (solve 2
      (λ c y → (c ⊕ y) ⊖ (c ⊖ y) ⊜ y ⊕ y)
      BishopP.≃-refl
      (Euclidean.x center) (Euclidean.x displacement))
    (solve 2
      (λ c y → (c ⊕ y) ⊖ (c ⊖ y) ⊜ y ⊕ y)
      BishopP.≃-refl
      (Euclidean.y center) (Euclidean.y displacement))
    (solve 2
      (λ c y → (c ⊕ y) ⊖ (c ⊖ y) ⊜ y ⊕ y)
      BishopP.≃-refl
      (Euclidean.z center) (Euclidean.z displacement))

------------------------------------------------------------------------
-- The difference coordinate is independent of the centre.  Hence shrinking
-- the output through center -> 0 does not shrink p-q unless y also shrinks by
-- an additional physical hypothesis.
------------------------------------------------------------------------

centeredResidualAutomaticallyCarriesOutputPower : Bool
centeredResidualAutomaticallyCarriesOutputPower = false

resolventShiftAutomaticallyComparableToOutputRadius : Bool
resolventShiftAutomaticallyComparableToOutputRadius = false

continuousCenteredDifferenceIndependentOfCenter : Bool
continuousCenteredDifferenceIndependentOfCenter = true

clayPromotion : Bool
clayPromotion = false

continuousCenteredDifferenceIndependentOfCenterIsTrue :
  continuousCenteredDifferenceIndependentOfCenter ≡ true
continuousCenteredDifferenceIndependentOfCenterIsTrue = refl

centeredResidualAutomaticallyCarriesOutputPowerIsFalse :
  centeredResidualAutomaticallyCarriesOutputPower ≡ false
centeredResidualAutomaticallyCarriesOutputPowerIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
