{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.W4IndependentPhysicalPredictionRequestExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

record W4IndependentPhysicalPredictionRequest : Set where
  constructor w4IndependentPhysicalPredictionRequest
  field
    observable : String
    massWindow : String
    binCount : String
    acceptedModelFamilies : List String
    requiredPhysics : List String
    scoringScript : String
    providerGridPresent : Bool
    providerGridPresentIsFalse : providerGridPresent ≡ false
    currentInternalProxyPromoted : Bool
    currentInternalProxyPromotedIsFalse :
      currentInternalProxyPromoted ≡ false

open W4IndependentPhysicalPredictionRequest public

canonicalW4IndependentPhysicalPredictionRequest :
  W4IndependentPhysicalPredictionRequest
canonicalW4IndependentPhysicalPredictionRequest =
  w4IndependentPhysicalPredictionRequest
    "d sigma / d phiStar in pb"
    "76 < m_ll < 106 GeV"
    "18 frozen t21 bins with full t22 covariance"
    ( "MiNNLO_PS"
    ∷ "GENEVA_qT"
    ∷ "ARTEMIDE"
    ∷ "CASCADE_PB"
    ∷ "DYTURBO"
    ∷ "independent TMD/resummed provider"
    ∷ [] )
    ( "soft-gluon/TMD or qT resummation in the low-phiStar region"
    ∷ "nonperturbative recoil/primordial transverse-momentum treatment where applicable"
    ∷ "fiducial leptonic acceptance for the CMS observable"
    ∷ "controlled fixed-order/matrix-element tail"
    ∷ "prediction generated independently of the 18-bin t21 fit"
    ∷ [] )
    "scripts/grqft_w4_score_physical_prediction.py"
    false refl
    false refl
