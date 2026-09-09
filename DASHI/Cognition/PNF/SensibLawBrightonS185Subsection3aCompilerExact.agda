module DASHI.Cognition.PNF.SensibLawBrightonS185Subsection3aCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

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
-- It also does NOT promote an agent's use of the words "non-liveability" into
-- objective legal unfitness.  That remains the live evidence/classification
-- coordinate.
------------------------------------------------------------------------

data TenancyContinuingAtEvaluation : Set where
  tenancy-continuing-at-evaluation : TenancyContinuingAtEvaluation

data PremisesObjectivelyUnfitAtEvaluation : Set where
  premises-objectively-unfit-at-evaluation : PremisesObjectivelyUnfitAtEvaluation

data HistoricalS185Subsection3aApplies : Set where
  historical-s185-subsection3a-applies : HistoricalS185Subsection3aApplies

data S185Subsection3aNonPerformance : Set where
  s185-subsection3a-non-performance : S185Subsection3aNonPerformance

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
    objectiveUnfitnessRequired : Bool
    applicabilityRequired : Bool
    reasonableTimeInsertedAsIndependentElement : Bool
    agentCharacterisationAutomaticallyPaysObjectiveUnfitness : Bool
    outstandingRemediationAutomaticallyPaysObjectiveUnfitness : Bool
    photosAutomaticallyPayObjectiveUnfitness : Bool
    compilerReference : String

canonicalBrightonS185Subsection3aCompilerBoundary :
  BrightonS185Subsection3aCompilerBoundary
canonicalBrightonS185Subsection3aCompilerBoundary =
  brighton-s185-subsection3a-compiler-boundary
    true true true true false false false false
    "direct historical RTRA 2008 (Qld) s185(3)(a) outcome-obligation compiler"
