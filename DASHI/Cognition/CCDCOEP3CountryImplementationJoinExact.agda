{-# OPTIONS --safe #-}
module DASHI.Cognition.CCDCOEP3CountryImplementationJoinExact where

------------------------------------------------------------------------
-- Credit: G20 Research Group and the original Brisbane/Antalya
-- compliance report authors own the observed compliance measurements.
-- This module proves only typed admission and non-fusion boundaries.
-- It does NOT claim to reanalyse the original country observations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

data Study : Set where
  brisbane2014 : Study
  antalya2015 : Study

data Metric : Set where
  selectedCompliance : Metric
  ndcProcedure : Metric
  emissions : Metric
  finance : Metric

data Unit : Metric → Set where
  minusOneToOne : Unit selectedCompliance
  recordedProcedure : Unit ndcProcedure
  tonnesCO2e : Unit emissions
  millionTonnesCO2e : Unit emissions
  nominalUSD : Unit finance
  constant2020USD : Unit finance

data Stage : Set where
  candidate : Stage
  reviewedOriginal : Stage

record Observation (s : Study) (m : Metric) : Set where
  constructor observation
  field
    author : String
    sourceURI : String
    countryISO3 : String
    commitmentID : String
    firstDay : String
    lastDay : String
    unit : Unit m
    reviewStage : Stage

-- Admissibility is a separate witness about the selected source.
-- Concrete digest and span checks must be supplied by the external
-- fail-closed validator rather than invented by this formal model.
record Admission {s : Study} {m : Metric}
                 (o : Observation s m) : Set where
  constructor sourceReviewed
  field
    originalStage : Observation.reviewStage o ≡ reviewedOriginal

admittedSource : {s : Study} {m : Metric}
  (o : Observation s m) → Admission o → Observation s m
admittedSource o _ = o

notSameStudy : brisbane2014 ≡ antalya2015 → ⊥
notSameStudy ()

candidateNotReviewed : candidate ≡ reviewedOriginal → ⊥
candidateNotReviewed ()

-- Distinct indexed metric units prevent silently substituting
-- the published compliance scores for physical emissions outcomes.
originalComplianceUnit : Unit selectedCompliance
originalComplianceUnit = minusOneToOne

originalEmissionsUnit : Unit emissions
originalEmissionsUnit = tonnesCO2e
