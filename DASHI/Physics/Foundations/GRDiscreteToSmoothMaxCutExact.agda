{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRDiscreteToSmoothMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.DiscreteToSmoothEinsteinLimitReceipt as Smooth
import DASHI.Physics.Foundations.GRHolonomyTaylorRicciEvidenceExact as Evidence

data GRDiscreteToSmoothAnalyticLeaf : Set where
  theoremBearingHolonomyTaylorCurvatureControl :
    GRDiscreteToSmoothAnalyticLeaf
  discreteRicciToSmoothRicciIdentification :
    GRDiscreteToSmoothAnalyticLeaf
  stressEnergyConvergenceOnSameFamily :
    GRDiscreteToSmoothAnalyticLeaf
  smoothEinsteinContinuity :
    GRDiscreteToSmoothAnalyticLeaf

canonicalGRDiscreteToSmoothAnalyticLeaves :
  List GRDiscreteToSmoothAnalyticLeaf
canonicalGRDiscreteToSmoothAnalyticLeaves =
  theoremBearingHolonomyTaylorCurvatureControl
  ∷ discreteRicciToSmoothRicciIdentification
  ∷ stressEnergyConvergenceOnSameFamily
  ∷ smoothEinsteinContinuity
  ∷ []

record GRDiscreteToSmoothMaxCut : Set where
  constructor grDiscreteToSmoothMaxCut
  field
    currentReceipt :
      Smooth.DiscreteToSmoothEinsteinLimitReceipt

    currentFirstMissingIsCurvatureConvergence :
      Smooth.DiscreteToSmoothEinsteinLimitReceipt.firstMissing currentReceipt
      ≡ Smooth.missingDiscreteToSmoothCurvatureConvergence

    requestSurfaceExists : Bool
    requestSurfaceExistsIsTrue :
      requestSurfaceExists ≡ true

    theoremBearingEvidenceConstructed : Bool
    theoremBearingEvidenceConstructedIsFalse :
      theoremBearingEvidenceConstructed ≡ false

    firstEvidenceBundleName : String

    remainingLeaves :
      List GRDiscreteToSmoothAnalyticLeaf

open GRDiscreteToSmoothMaxCut public

canonicalGRDiscreteToSmoothMaxCut : GRDiscreteToSmoothMaxCut
canonicalGRDiscreteToSmoothMaxCut =
  grDiscreteToSmoothMaxCut
    Smooth.canonicalDiscreteToSmoothEinsteinLimitReceipt
    Smooth.discreteToSmoothEinsteinLimitExactFirstMissing
    true refl
    false refl
    "GRDiscreteToSmoothFirstAnalyticBundle"
    canonicalGRDiscreteToSmoothAnalyticLeaves

requestDoesNotEqualProof :
  theoremBearingEvidenceConstructed canonicalGRDiscreteToSmoothMaxCut ≡ false
requestDoesNotEqualProof = refl
