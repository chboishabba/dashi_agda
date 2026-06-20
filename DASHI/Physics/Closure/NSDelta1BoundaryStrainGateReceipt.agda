module DASHI.Physics.Closure.NSDelta1BoundaryStrainGateReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Sharp delta1 gate at the vortex boundary.
--
-- This is a fail-closed receipt only. It records the exact boundary identity
-- on {lambda2 = 0}, the Sard-based partial closure delta1 > 0 at H^2-a.e.
-- regular boundary point, and the honest analytic gap: the quantitative
-- threshold delta1 >= 1 remains open.

record NSDelta1BoundaryStrainGateReceipt : Set where
  constructor mkNSDelta1BoundaryStrainGateReceipt
  field
    boundaryCarrier :
      String

    tracelessnessStatement :
      String

    boundaryGapIdentity :
      String

    sardPartialClosureStatement :
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
    "On {lambda2 = 0}, tracelessness collapses the boundary eigenframe to lambda3 = -lambda1, so the exact boundary identity is delta1 = |lambda1|."
    "By Sard, at H^2-a.e. regular point of the boundary we recover the partial closure delta1 > 0."
    "The quantitative tranche delta1 >= 1 is still open and is not certified by this receipt."
    "Current energy/enstrophy control remains upper control only and does not force a pointwise lower bound strong enough for the threshold delta1 >= 1."
    "Missing PDE ingredient: a pointwise strain lower bound on the codimension-1 level set {lambda2 = 0}."
    true
    refl
    false
    refl
    false
    refl
