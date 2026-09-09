module DASHI.Cognition.PNF.SensibLawBrightonS185Subsection3aCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawBrightonS185ApplicabilityEvidenceExact as Applicability

------------------------------------------------------------------------
-- DIRECT s 185(3)(a) COMPILER
--
-- Historical source owner:
--   Residential Tenancies and Rooming Accommodation Act 2008 (Qld),
--   s 185(3)(a), version applicable to 24 January 2023.
--
-- Source-language obligation:
--   while the tenancy continues, the lessor must maintain the premises in a
--   way that the premises remain fit for the tenant to live in.
--
-- This compiler deliberately does NOT insert a free-standing "reasonable time"
-- element into s 185(3)(a).  The selected statutory proposition is an outcome
-- obligation on the exact historical source language.
--
-- The private Form 18a source receipt already pays the continuing-tenancy and
-- ordinary-general-tenancy applicability inputs.  It does NOT promote an
-- agent's use of the words "non-liveability" into objective legal unfitness.
------------------------------------------------------------------------

data TenancyContinuingAtEvaluation : Set where
  tenancy-continuing-at-evaluation : TenancyContinuingAtEvaluation

data PremisesObjectivelyUnfitAtEvaluation : Set where
  premises-objectively-unfit-at-evaluation : PremisesObjectivelyUnfitAtEvaluation

data HistoricalS185Subsection3aApplies : Set where
  historical-s185-subsection3a-applies : HistoricalS185Subsection3aApplies

data S185Subsection3aNonPerformance : Set where
  s185-subsection3a-non-performance : S185Subsection3aNonPerformance

continuingTenancyFromForm18a :
  Applicability.BrightonTenancyContinuing24Jan2023 →
  TenancyContinuingAtEvaluation
continuingTenancyFromForm18a Applicability.form18a-fixed-term-contains-24jan2023 =
  tenancy-continuing-at-evaluation

s185ApplicabilityFromForm18a :
  Applicability.BrightonS185Applies24Jan2023 →
  HistoricalS185Subsection3aApplies
s185ApplicabilityFromForm18a Applicability.form18a-general-tenancy-s185-applies =
  historical-s185-subsection3a-applies

canonicalBrightonTenancyContinuing : TenancyContinuingAtEvaluation
canonicalBrightonTenancyContinuing =
  continuingTenancyFromForm18a Applicability.brightonTenancyContinuing24Jan2023

canonicalBrightonS185Subsection3aApplies : HistoricalS185Subsection3aApplies
canonicalBrightonS185Subsection3aApplies =
  s185ApplicabilityFromForm18a Applicability.brightonS185Applies24Jan2023

directS185Subsection3aCompiler :
  TenancyContinuingAtEvaluation →
  PremisesObjectivelyUnfitAtEvaluation →
  HistoricalS185Subsection3aApplies →
  S185Subsection3aNonPerformance
directS185Subsection3aCompiler
  tenancy-continuing-at-evaluation
  premises-objectively-unfit-at-evaluation
  historical-s185-subsection3a-applies =
    s185-subsection3a-non-performance

brightonS185Subsection3aFromObjectiveUnfitness :
  PremisesObjectivelyUnfitAtEvaluation →
  S185Subsection3aNonPerformance
brightonS185Subsection3aFromObjectiveUnfitness objectiveUnfitness =
  directS185Subsection3aCompiler
    canonicalBrightonTenancyContinuing
    objectiveUnfitness
    canonicalBrightonS185Subsection3aApplies

------------------------------------------------------------------------
-- Evidence/status firewalls.
------------------------------------------------------------------------

data AgentSaysNonLiveableAutomaticallyObjectiveUnfitness : Set where
data OutstandingRemediationAutomaticallyObjectiveUnfitness : Set where
data PhotosAutomaticallyObjectiveUnfitness : Set where
data S185Subsection3aContainsIndependentReasonableTimeElement : Set where

agentCharacterisationDoesNotAutoCreateObjectiveUnfitness :
  AgentSaysNonLiveableAutomaticallyObjectiveUnfitness → ⊥
agentCharacterisationDoesNotAutoCreateObjectiveUnfitness ()

outstandingRemediationDoesNotAutoCreateObjectiveUnfitness :
  OutstandingRemediationAutomaticallyObjectiveUnfitness → ⊥
outstandingRemediationDoesNotAutoCreateObjectiveUnfitness ()

photosDoNotAutoCreateObjectiveUnfitness :
  PhotosAutomaticallyObjectiveUnfitness → ⊥
photosDoNotAutoCreateObjectiveUnfitness ()

noIndependentReasonableTimeElementInserted :
  S185Subsection3aContainsIndependentReasonableTimeElement → ⊥
noIndependentReasonableTimeElementInserted ()

record BrightonS185Subsection3aCompilerBoundary : Set where
  constructor brighton-s185-subsection3a-compiler-boundary
  field
    exactHistoricalProvisionPinned : Bool
    continuingTenancyRequired : Bool
    continuingTenancyPaid : Bool
    objectiveUnfitnessRequired : Bool
    applicabilityRequired : Bool
    applicabilityPaid : Bool
    reasonableTimeInsertedAsIndependentElement : Bool
    agentCharacterisationAutomaticallyPaysObjectiveUnfitness : Bool
    outstandingRemediationAutomaticallyPaysObjectiveUnfitness : Bool
    photosAutomaticallyPayObjectiveUnfitness : Bool
    compilerReference : String

canonicalBrightonS185Subsection3aCompilerBoundary :
  BrightonS185Subsection3aCompilerBoundary
canonicalBrightonS185Subsection3aCompilerBoundary =
  brighton-s185-subsection3a-compiler-boundary
    true true true true true true
    false false false false
    "direct historical RTRA 2008 (Qld) s185(3)(a) outcome-obligation compiler"
