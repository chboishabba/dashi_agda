module DASHI.Physics.Closure.FixedPointCFTBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftFixedPointPerturbationClassification as SFPC

------------------------------------------------------------------------
-- Fail-closed handoff from the earned finite fixed-point classification to a
-- possible later fixed-point CFT / continuum RG theorem.
--
-- The existing shift lane earns an exact finite classification.  A genuine
-- CFT-facing promotion additionally needs tangent/perturbation geometry,
-- derivative or linearized semigroup data, scaling dimensions, operator
-- products, and continuum/correlation control.  Those obligations are named
-- here rather than silently identified with the finite three-point result.

data FixedPointCFTOpenGate : Set where
  tangentPerturbationCarrierRequired : FixedPointCFTOpenGate
  derivativeOrLinearizedSemigroupRequired : FixedPointCFTOpenGate
  scalingDimensionSpectrumRequired : FixedPointCFTOpenGate
  operatorProductOrFusionLawRequired : FixedPointCFTOpenGate
  continuumRGControlRequired : FixedPointCFTOpenGate
  correlationOrConformalWardControlRequired : FixedPointCFTOpenGate

data FixedPointCFTPromotion : Set where

fixedPointCFTPromotionImpossibleHere :
  FixedPointCFTPromotion →
  ⊥
fixedPointCFTPromotionImpossibleHere ()

record FixedPointCFTBoundary : Setω where
  field
    finiteClassification :
      SFPC.ShiftFixedPointPerturbationClassification

    finiteFixedPointClassified : Bool
    finiteFixedPointClassifiedIsTrue :
      finiteFixedPointClassified ≡ true

    irrelevantFiniteStatesStrictlyDescend : Bool
    irrelevantFiniteStatesStrictlyDescendIsTrue :
      irrelevantFiniteStatesStrictlyDescend ≡ true

    marginalFiniteStateStable : Bool
    marginalFiniteStateStableIsTrue :
      marginalFiniteStateStable ≡ true

    relevantFiniteStateInhabited : Bool
    relevantFiniteStateInhabitedIsFalse :
      relevantFiniteStateInhabited ≡ false

    tangentPerturbationCarrierConstructed : Bool
    tangentPerturbationCarrierConstructedIsFalse :
      tangentPerturbationCarrierConstructed ≡ false

    derivativeLinearizationConstructed : Bool
    derivativeLinearizationConstructedIsFalse :
      derivativeLinearizationConstructed ≡ false

    scalingDimensionsConstructed : Bool
    scalingDimensionsConstructedIsFalse :
      scalingDimensionsConstructed ≡ false

    operatorProductLawConstructed : Bool
    operatorProductLawConstructedIsFalse :
      operatorProductLawConstructed ≡ false

    continuumFixedPointCFTPromoted : Bool
    continuumFixedPointCFTPromotedIsFalse :
      continuumFixedPointCFTPromoted ≡ false

    openGates : List FixedPointCFTOpenGate

    promotions : List FixedPointCFTPromotion
    promotionsAreEmpty : promotions ≡ []
    noPromotionPossibleHere : FixedPointCFTPromotion → ⊥

    boundary : List String

open FixedPointCFTBoundary public

canonicalFixedPointCFTOpenGates :
  List FixedPointCFTOpenGate
canonicalFixedPointCFTOpenGates =
  tangentPerturbationCarrierRequired
  ∷ derivativeOrLinearizedSemigroupRequired
  ∷ scalingDimensionSpectrumRequired
  ∷ operatorProductOrFusionLawRequired
  ∷ continuumRGControlRequired
  ∷ correlationOrConformalWardControlRequired
  ∷ []

canonicalFixedPointCFTBoundary : FixedPointCFTBoundary
canonicalFixedPointCFTBoundary =
  record
    { finiteClassification =
        SFPC.canonicalShiftFixedPointPerturbationClassification
    ; finiteFixedPointClassified = true
    ; finiteFixedPointClassifiedIsTrue = refl
    ; irrelevantFiniteStatesStrictlyDescend = true
    ; irrelevantFiniteStatesStrictlyDescendIsTrue = refl
    ; marginalFiniteStateStable = true
    ; marginalFiniteStateStableIsTrue = refl
    ; relevantFiniteStateInhabited = false
    ; relevantFiniteStateInhabitedIsFalse = refl
    ; tangentPerturbationCarrierConstructed = false
    ; tangentPerturbationCarrierConstructedIsFalse = refl
    ; derivativeLinearizationConstructed = false
    ; derivativeLinearizationConstructedIsFalse = refl
    ; scalingDimensionsConstructed = false
    ; scalingDimensionsConstructedIsFalse = refl
    ; operatorProductLawConstructed = false
    ; operatorProductLawConstructedIsFalse = refl
    ; continuumFixedPointCFTPromoted = false
    ; continuumFixedPointCFTPromotedIsFalse = refl
    ; openGates = canonicalFixedPointCFTOpenGates
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = fixedPointCFTPromotionImpossibleHere
    ; boundary =
        "The live shift carrier now has an exact finite fixed-point perturbation classification"
        ∷ "start and next strictly descend and are classified as finite irrelevant states"
        ∷ "held is the unique stable finite marginal class used by this boundary"
        ∷ "the finite classification is attached to the existing quadratic-energy and collapse/MDL receipt chain"
        ∷ "A genuine fixed-point CFT theorem still requires tangent geometry, derivative data, scaling dimensions, operator products, continuum control, and correlation identities"
        ∷ "No continuum RG, conformal symmetry, scaling-spectrum, or CFT promotion is made here"
        ∷ []
    }
