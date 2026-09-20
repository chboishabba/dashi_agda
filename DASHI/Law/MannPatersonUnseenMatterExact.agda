module DASHI.Law.MannPatersonUnseenMatterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.AustralianContractsLegalFollowExact as Contracts
import DASHI.Law.SensibLawProductionLegalRuntimeABIExact as Runtime
import DASHI.Interop.SLRPortableInteractionCommandWeldExact as Interaction
import DASHI.Interop.PortableInteractiveGpuProjectionExact as Portable

------------------------------------------------------------------------
-- MANN v PATERSON UNSEEN-MATTER REGRESSION
--
-- The specimen is intentionally *not* a fifth calibration constructor.
-- Contract/termination/restitution/statute coordinates are fixture inputs to
-- the existing generic legal runtime and MatterCommand reducer.
------------------------------------------------------------------------

data MannMatterRole : Set where
  contractExistence : MannMatterRole
  repudiationTermination : MannMatterRole
  domesticBuildingSection38 : MannMatterRole
  restitutionQuantumMeruit : MannMatterRole

record MannMatterCoordinate : Set where
  constructor mannMatterCoordinate
  field
    role : MannMatterRole
    semanticReference : String
    sourceReference : String
    jurisdictionReference : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open MannMatterCoordinate public

record MannUnseenMatterFixture : Set₁ where
  constructor mannUnseenMatterFixture
  field
    matterReference : String
    hcaCaseReference : String
    victorianStatuteReference : String
    trace : Contracts.AustralianContractFollowTrace
    coordinates : List MannMatterCoordinate

    reviewedEvidenceReceipt : Set
    wrongTypeProjectionReceipt : Set
    sourceRealisedRuleReceipt : Set
    residualFrontierReceipt : Set
    matterRuntimeProjectionReceipt : Set

    usesAustralianCalibrationEnum : Bool
    usesAustralianCalibrationEnumIsFalse :
      usesAustralianCalibrationEnum ≡ false

    contractSpecificReducerAdded : Bool
    contractSpecificReducerAddedIsFalse :
      contractSpecificReducerAdded ≡ false

    usesSharedMatterCommand : Bool
    usesSharedMatterCommandIsTrue :
      usesSharedMatterCommand ≡ true

    fixtureCreatesSemanticAuthority : Bool
    fixtureCreatesSemanticAuthorityIsFalse :
      fixtureCreatesSemanticAuthority ≡ false

open MannUnseenMatterFixture public

RuntimeBoundary : Set
RuntimeBoundary = Runtime.RuntimeLegalProducerBoundary

runtimeBoundaryPaid : RuntimeBoundary
runtimeBoundaryPaid = Runtime.canonicalRuntimeLegalProducerBoundary

MatterCommandKind : Set
MatterCommandKind = Interaction.MatterCommandKind

PortableInteractionBoundary : Set
PortableInteractionBoundary =
  Portable.PortableInteractiveGpuProjectionBoundary

portableInteractionBoundaryPaid : PortableInteractionBoundary
portableInteractionBoundaryPaid =
  Portable.canonicalPortableInteractiveGpuProjectionBoundary

------------------------------------------------------------------------
-- The doctrinal/statutory intersection is a trace relation, not a forced
-- flattening into one source object.
------------------------------------------------------------------------

mannTrace : Contracts.AustralianContractFollowTrace
mannTrace =
  Contracts.australianContractFollowTrace
    "matter:au:hca:2019:32"
    (Contracts.contractTraceNode
      "matter:au:hca:2019:32"
      "Mann v Paterson Constructions Pty Ltd"
      Contracts.restitution
      "AU"
      "court:HCA"
      "2019-10-09"
      Contracts.primaryCaseLaw
      Contracts.official
      "[2019] HCA 32"
      true refl
      false refl
      ∷
     Contracts.contractTraceNode
      "legislation:vic:domestic-building-contracts-act-1995:s38"
      "Domestic Building Contracts Act 1995 (Vic) s 38"
      Contracts.restitution
      "AU-VIC"
      "legislature:VIC"
      "current"
      Contracts.primaryLegislation
      Contracts.official
      "Domestic Building Contracts Act 1995 (Vic) s 38"
      true refl
      false refl
      ∷ [])
    (Contracts.contractTraceEdge
      "matter:au:hca:2019:32"
      "legislation:vic:domestic-building-contracts-act-1995:s38"
      Contracts.intersects
      true refl
      false refl
      ∷ [])
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data HighCourtCaseAutomaticallySameObjectAsVictorianStatute : Set where
data RepudiationAutomaticallyEntitlesQuantumMeruit : Set where
data StatutoryIntersectionAutomaticallyDeterminesRemedy : Set where
data UnseenMatterRequiresNewReducer : Set where
data RenderingMannGraphCreatesLegalAuthority : Set where

hcaCaseIsNotSameObjectAsVictorianStatute :
  HighCourtCaseAutomaticallySameObjectAsVictorianStatute → ⊥
hcaCaseIsNotSameObjectAsVictorianStatute ()

repudiationDoesNotAutoEntitleQuantumMeruit :
  RepudiationAutomaticallyEntitlesQuantumMeruit → ⊥
repudiationDoesNotAutoEntitleQuantumMeruit ()

statutoryIntersectionDoesNotDetermineRemedy :
  StatutoryIntersectionAutomaticallyDeterminesRemedy → ⊥
statutoryIntersectionDoesNotDetermineRemedy ()

unseenMatterDoesNotRequireNewReducer :
  UnseenMatterRequiresNewReducer → ⊥
unseenMatterDoesNotRequireNewReducer ()

renderingDoesNotCreateAuthority :
  RenderingMannGraphCreatesLegalAuthority → ⊥
renderingDoesNotCreateAuthority ()

record MannUnseenMatterAcceptanceBoundary : Set where
  constructor mannUnseenMatterAcceptanceBoundary
  field
    genericEvidenceSubstrateReused : Bool
    genericEvidenceSubstrateReusedIsTrue :
      genericEvidenceSubstrateReused ≡ true

    genericWrongTypeProjectionReused : Bool
    genericWrongTypeProjectionReusedIsTrue :
      genericWrongTypeProjectionReused ≡ true

    genericMatterRuntimeReused : Bool
    genericMatterRuntimeReusedIsTrue :
      genericMatterRuntimeReused ≡ true

    calibrationEnumExtensionRequired : Bool
    calibrationEnumExtensionRequiredIsFalse :
      calibrationEnumExtensionRequired ≡ false

    contractSpecificReducerRequired : Bool
    contractSpecificReducerRequiredIsFalse :
      contractSpecificReducerRequired ≡ false

canonicalMannUnseenMatterAcceptanceBoundary :
  MannUnseenMatterAcceptanceBoundary
canonicalMannUnseenMatterAcceptanceBoundary =
  mannUnseenMatterAcceptanceBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
