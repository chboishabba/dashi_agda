{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.ColliderLowChiSquareProvenanceLadderExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

data LowChiSquareProvenanceClass : Set where
  posteriorTunedTrainingDiagnostic : LowChiSquareProvenanceClass
  independentHoldoutFailure : LowChiSquareProvenanceClass
  boundedFrozenComparisonLaw : LowChiSquareProvenanceClass
  fixtureBaselineDiagnostic : LowChiSquareProvenanceClass

record LowChiSquareEvidenceRow : Set where
  constructor lowChiSquareEvidenceRow
  field
    label : String
    chi2PerDof : String
    provenance : LowChiSquareProvenanceClass
    promotesEmpiricalAdequacy : Bool
    boundary : String

open LowChiSquareEvidenceRow public

hepR41PosteriorT43 : LowChiSquareEvidenceRow
hepR41PosteriorT43 =
  lowChiSquareEvidenceRow
    "HEP-R41 t43 posterior shape-response diagnostic"
    "1.7408778006026118"
    posteriorTunedTrainingDiagnostic
    false
    "Constants were selected after residual inspection; low chi-square is not an accepted comparison law."

hepR42T45Holdout : LowChiSquareEvidenceRow
hepR42T45Holdout =
  lowChiSquareEvidenceRow
    "HEP-R42 unchanged-model t45 independent holdout"
    "222.54402462995546"
    independentHoldoutFailure
    false
    "The HEP-R41 model fails the independent above-Z mass-window holdout."

canonicalCMSW3T43 : LowChiSquareEvidenceRow
canonicalCMSW3T43 =
  lowChiSquareEvidenceRow
    "canonical frozen CMS t43 bounded comparison law"
    "2.1565191176275618"
    boundedFrozenComparisonLaw
    true
    "Promotion is bounded to the W3 t43 comparison-law scope; it is not W4/W5/GRQFT adequacy."

atlasFixtureMinimum : LowChiSquareEvidenceRow
atlasFixtureMinimum =
  lowChiSquareEvidenceRow
    "ATLAS H->gamma gamma fixture-baseline minimum current reduced chi-square"
    "2.6493994618998236"
    fixtureBaselineDiagnostic
    false
    "The baseline is fixture-not-authority and no accepted holdout/authority token exists."

canonicalLowChiSquareEvidenceRows : List LowChiSquareEvidenceRow
canonicalLowChiSquareEvidenceRows =
  hepR41PosteriorT43
  ∷ hepR42T45Holdout
  ∷ canonicalCMSW3T43
  ∷ atlasFixtureMinimum
  ∷ []

lowChiSquareAlonePromotesEmpiricalAdequacy : Bool
lowChiSquareAlonePromotesEmpiricalAdequacy = false

lowChiSquareAlonePromotesEmpiricalAdequacyIsFalse :
  lowChiSquareAlonePromotesEmpiricalAdequacy ≡ false
lowChiSquareAlonePromotesEmpiricalAdequacyIsFalse = refl

holdoutCanDefeatPosteriorLowChiSquare : Bool
holdoutCanDefeatPosteriorLowChiSquare = true

holdoutCanDefeatPosteriorLowChiSquareIsTrue :
  holdoutCanDefeatPosteriorLowChiSquare ≡ true
holdoutCanDefeatPosteriorLowChiSquareIsTrue = refl
