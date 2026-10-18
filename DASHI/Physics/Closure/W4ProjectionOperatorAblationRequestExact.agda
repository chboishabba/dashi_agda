{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.W4ProjectionOperatorAblationRequestExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

record W4ProjectionOperatorAblationRequest : Set where
  constructor w4ProjectionOperatorAblationRequest
  field
    commonMassWindow : String
    currentAbsoluteOperator : String
    ratioDenominatorOperator : String
    covarianceSource : String
    fittedParametersPerVariant : String
    runner : String
    ablationExecutedOnExactHead : Bool
    ablationExecutedOnExactHeadIsFalse :
      ablationExecutedOnExactHead ≡ false
    promotesW4 : Bool
    promotesW4IsFalse : promotesW4 ≡ false
    interpretationBoundary : List String

open W4ProjectionOperatorAblationRequest public

canonicalW4ProjectionOperatorAblationRequest :
  W4ProjectionOperatorAblationRequest
canonicalW4ProjectionOperatorAblationRequest =
  w4ProjectionOperatorAblationRequest
    "76--106 GeV"
    "predict_dirty_z_peak_shape -> sigma_DASHI -> one covariance-weighted scale"
    "t43 ratio denominator: five-point phi-star quadrature of _window_sigma_density_at_phi"
    "CMS SMP-20-003 t22 Total uncertainty covariance"
    "one overall scale for each compared shape"
    "scripts/grqft_w4_projection_operator_ablation.py"
    false refl
    false refl
    ( "same 76--106 GeV construction, different phi-star projection operator"
    ∷ "if ratio-style denominator improves W4 strongly, projection mismatch is implicated"
    ∷ "if it remains bad, move the defect search upstream into common absolute density/physics"
    ∷ "ratio success can hide common multiplicative error by cancellation"
    ∷ "no result from this ablation alone promotes W4"
    ∷ [] )
