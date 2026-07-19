module DASHI.Promotion.TFLCategoricalAuthorityHomology where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ResidualNaturality as RN
import DASHI.Core.PromotionTransformation as PT
import DASHI.Core.ProjectionHomology as PH

import DASHI.Promotion.TFLEncodingCategoricalLoom as TFL

----------------------------------------------------------------------
-- A first fully discharged categorical AI vertical slice.
--
-- Projection category:
--   the TFL constrained-predictor category.
--
-- Authority category:
--   the same typed pipeline surface, interpreted as calibrated reference
--   morphisms.  This is a structural baseline, not an empirical assay
--   claim.  Domain companions may replace it with an independent assay or
--   proof category later.
--
-- Residual:
--   pointwise equality between the projected morphism and authority
--   reference morphism.
--
-- Promotion:
--   exactly the pair residual × closed, hence fail-closed by construction.
----------------------------------------------------------------------

tflAuthorityCategory : PC.ProjectionCategory
tflAuthorityCategory = TFL.tflProjectionCategory

tflResidualNaturality :
  RN.ResidualNaturality TFL.tflProjectionCategory tflAuthorityCategory
tflResidualNaturality = record
  { FObj            = λ A → A
  ; FHom            = λ f → f
  ; F-id            = refl
  ; F-comp          = λ f g → refl
  ; residual        = λ f α → ∀ x → f x ≡ α x
  ; closed          = λ f α → ∀ x → f x ≡ α x
  ; residualReading =
      "TFL structural authority: pointwise comparison against a calibrated reference morphism"
  }

tflPromotionTransformation :
  PT.PromotionTransformation
    TFL.tflProjectionCategory
    tflAuthorityCategory
    tflResidualNaturality
tflPromotionTransformation = record
  { Promoted = λ f α →
      Σ (RN.residual tflResidualNaturality f α) λ _ →
        RN.closed tflResidualNaturality f α
  ; promote = λ f α r c → r , c
  ; failClosed = λ f α promoted → promoted
  ; promote-id = (λ x → refl) , (λ x → refl)
  ; transformationReading =
      "TFL promotion is admitted exactly when pointwise residual and closure witnesses are supplied"
  }

----------------------------------------------------------------------
-- Grammar-change persistence.
--
-- The current TFL companion keeps the categorical object/morphism shape
-- fixed while grammar values alter admissibility.  Therefore grammar
-- transport is identity on the pipeline category, and pipeline stages
-- persist exactly when identified with their transported stage.
----------------------------------------------------------------------

tflProjectionHomology : PH.ProjectionHomology TFL.tflGrammarCategory
tflProjectionHomology = record
  { GrammarMorphism      = λ Γ Γ' → ⊤
  ; TransportFunctor     = λ φ → TFL.tflProjectionCategory
  ; transportPreservesId = λ φ A → A
  ; transportPreservesHom = λ φ f → f
  ; HomologySet          = λ φ → TFL.TFLObj
  ; persists             = λ φ A H → A ≡ H
  ; homologyReading      =
      "TFL grammar transport preserves the typed pipeline skeleton; stronger prediction-topology invariants remain domain obligations"
  }

rawFeaturePersists :
  PH.persists tflProjectionHomology tt TFL.rawFeature TFL.rawFeature
rawFeaturePersists = refl

outputCalibratedPersists :
  PH.persists tflProjectionHomology tt TFL.outputCalibrated TFL.outputCalibrated
outputCalibratedPersists = refl
