module DASHI.Physics.Closure.NSDelta1BoundaryStrainGateReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Sharp delta1 gate at the vortex boundary.
--
-- This is a fail-closed receipt only. It records the exact boundary algebra
-- on {lambda2 = 0}, the reformulation delta1 > 1 <=> |lambda1| > 1 there,
-- and the honest analytic gap: current energy/enstrophy control is upper
-- control and does not provide the needed pointwise lower bound on a
-- codimension-1 level set.

record NSDelta1BoundaryStrainGateReceipt : Set where
  constructor mkNSDelta1BoundaryStrainGateReceipt
  field
    boundaryCarrier :
      String

    tracelessnessStatement :
      String

    boundaryGapIdentity :
      String

    delta1ThresholdStatement :
      String

    currentUpperControlStatement :
      String

    missingPDEIngredientStatement :
      String

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    theoremPromotion :
      Bool

    theoremPromotionIsFalse :
      theoremPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

open NSDelta1BoundaryStrainGateReceipt public

canonicalNSDelta1BoundaryStrainGateReceipt :
  NSDelta1BoundaryStrainGateReceipt
canonicalNSDelta1BoundaryStrainGateReceipt =
  mkNSDelta1BoundaryStrainGateReceipt
    "{lambda2 = 0} vortex-boundary carrier"
    "Tracelessness on the boundary gives lambda3 = -lambda1."
    "On {lambda2 = 0}, g12 = lambda2 - lambda1 = -lambda1 = |lambda1|."
    "Therefore delta1 > 1 is exactly the boundary statement |lambda1| > 1."
    "Current energy/enstrophy control is only upper control and does not force a pointwise lower bound for |lambda1| on the boundary."
    "Missing PDE ingredient: a pointwise strain lower bound on the codimension-1 level set {lambda2 = 0}."
    true
    refl
    false
    refl
    false
    refl

