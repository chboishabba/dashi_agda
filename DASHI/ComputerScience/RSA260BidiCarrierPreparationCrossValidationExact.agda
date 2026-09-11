module DASHI.ComputerScience.RSA260BidiCarrierPreparationCrossValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCandidateExperimentExact as Candidate
import DASHI.ComputerScience.RSA260BidiPreparationFrontierCrossValidationExact as Frontier

------------------------------------------------------------------------
-- CARRIER x PREPARATION BIDI CROSS-VALIDATION
--
-- The prior frontier preference rotate29 is scoped to the canonical step-433
-- shadow carrier.  This owner varies the shadow carrier while preserving the
-- same coarse contract and then re-evaluates rotate29/rotate31.
--
-- Result: preparation preference is carrier-relative.  Coarse carrier shape,
-- degree profile, rank and left-nullity do not determine generator geometry.
------------------------------------------------------------------------

record CarrierPreparationRuntimeSource : Set where
  constructor carrier-preparation-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    runtime : String
    exactScriptBlobExecuted : Bool
    exactDependencyClosureExecuted : Bool
open CarrierPreparationRuntimeSource public

currentCarrierPreparationRuntimeSource : CarrierPreparationRuntimeSource
currentCarrierPreparationRuntimeSource = carrier-preparation-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_carrier_preparation_cross.py"
  "5bb3716e7d389ef4a505c8582161edb28cf50638"
  "3435c1d29646ecd35de0cdbbb85d23a93f19721f"
  "Python 3.13.5 / NumPy 2.3.5"
  true
  false

record CarrierCrossReceipt : Set where
  constructor carrier-cross-receipt
  field
    rowStep : Nat
    rank : Nat
    leftNullity : Nat
    rotate29MeanDegreeTimes1000 : Nat
    rotate31MeanDegreeTimes1000 : Nat
    rotate29MeanRelationDimTimes1000 : Nat
    rotate31MeanRelationDimTimes1000 : Nat
    rotate29MedianMinimumKernelWeight : Nat
    rotate31MedianMinimumKernelWeight : Nat
    bothAdaptersPassedTwoOfTwo : Bool
open CarrierCrossReceipt public

step433Receipt : CarrierCrossReceipt
step433Receipt = carrier-cross-receipt
  433 512 412
  15000 16500
  8000 12000
  24 76
  true

step431Receipt : CarrierCrossReceipt
step431Receipt = carrier-cross-receipt
  431 512 412
  11500 11500
  11500 11000
  26 34
  true

step251Receipt : CarrierCrossReceipt
step251Receipt = carrier-cross-receipt
  251 512 412
  16500 17000
  12000 16000
  382 372
  true

step127Receipt : CarrierCrossReceipt
step127Receipt = carrier-cross-receipt
  127 512 412
  6000 6000
  10000 10000
  60 88
  true

record CarrierPreparationInterpretationBoundary : Set where
  constructor carrier-preparation-interpretation-boundary
  field
    allTestedCarriersPreserveRank512 : Bool
    allTestedCarriersPreserveLeftNullity412 : Bool
    allTestedCarrierAdapterPairsRecoverConsumer : Bool
    rotate29PreferredOnCanonicalStep433Carrier : Bool
    rotate29GloballyPreferredAcrossCarrierFibre : Bool
    preparationPreferenceIsCarrierRelative : Bool
    sameCoarseCarrierContractDeterminesGeneratorGeometry : Bool
    rowStep127ShowsDegreeSixPresentation : Bool
    historicalSameObjectIdentityPaid : Bool
open CarrierPreparationInterpretationBoundary public

canonicalCarrierPreparationInterpretationBoundary : CarrierPreparationInterpretationBoundary
canonicalCarrierPreparationInterpretationBoundary = carrier-preparation-interpretation-boundary
  true true true
  true
  false
  true
  false
  true
  false

candidateBoundary : Candidate.CandidateConsumerSupportBoundary
candidateBoundary = Candidate.canonicalCandidateConsumerSupportBoundary

frontierPreference : Frontier.RobustnessAwarePreparationPreference
frontierPreference = Frontier.currentRobustnessAwarePreparationPreference

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SameCoarseContractImpliesSameGeneratorGeometry : Set where
data CanonicalCarrierPreferenceImpliesGlobalPreference : Set where
data DegreeSixShadowImpliesProductionGeneratorDegree : Set where
data CarrierFamilySuccessImpliesHistoricalIdentity : Set where

coarseContractDoesNotDetermineGeneratorGeometry :
  SameCoarseContractImpliesSameGeneratorGeometry → ⊥
coarseContractDoesNotDetermineGeneratorGeometry ()

canonicalPreferenceDoesNotCreateGlobalPreference :
  CanonicalCarrierPreferenceImpliesGlobalPreference → ⊥
canonicalPreferenceDoesNotCreateGlobalPreference ()

degreeSixShadowDoesNotCreateProductionGeneratorDegree :
  DegreeSixShadowImpliesProductionGeneratorDegree → ⊥
degreeSixShadowDoesNotCreateProductionGeneratorDegree ()

carrierFamilySuccessDoesNotCreateHistoricalIdentity :
  CarrierFamilySuccessImpliesHistoricalIdentity → ⊥
carrierFamilySuccessDoesNotCreateHistoricalIdentity ()
