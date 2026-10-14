module DASHI.Cognition.PNF.SensibLawFriendlyjordiesWorldEvidenceExact where

------------------------------------------------------------------------
-- FRIENDLYJORDIES EXTERNAL-WORLD EVIDENCE MAX-CUT
--
-- This owner pays only the narrow historical/operational facts directly
-- supported by primary or near-primary public institutional sources.
-- It deliberately does not promote those facts into causal party attribution,
-- counterfactual governance superiority, or a universal Labor/Greens ranking.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Base

------------------------------------------------------------------------
-- Regression-facing status flags.
------------------------------------------------------------------------

cprsLegislativeOutcomePaid : Bool
cprsLegislativeOutcomePaid = true

cprsPartyCausalAttributionPaid : Bool
cprsPartyCausalAttributionPaid = false

southAustraliaOperationalHighRenewablePaid : Bool
southAustraliaOperationalHighRenewablePaid = true

southAustraliaBatterySecurityRolePaid : Bool
southAustraliaBatterySecurityRolePaid = true

southAustraliaGovernanceCausalInferencePaid : Bool
southAustraliaGovernanceCausalInferencePaid = false

externalFactsCreateTransitionPremise : Bool
externalFactsCreateTransitionPremise = false

------------------------------------------------------------------------
-- Source authority and fact scope remain explicit.
------------------------------------------------------------------------

data SourceAuthority : Set where
  parliamentOfficialRecord : SourceAuthority
  independentSystemOperator : SourceAuthority
  stateGovernmentTechnicalPage : SourceAuthority

data FactScope : Set where
  legislativeOutcome : FactScope
  operationalSystemState : FactScope
  operationalSupportRole : FactScope
  causalAttribution : FactScope
  counterfactualTrajectory : FactScope

record WorldFactReceipt : Set where
  constructor world-fact-receipt
  field
    receiptRef : String
    case : March.MarchCase
    authority : SourceAuthority
    sourceTitle : String
    sourceUrl : String
    accessedDate : String
    scope : FactScope
    proposition : String
    directlySupported : Bool
    directlySupportedIsTrue : directlySupported ≡ true
    createsCausalAttribution : Bool
    createsCausalAttributionIsFalse : createsCausalAttribution ≡ false
    createsCounterfactualRanking : Bool
    createsCounterfactualRankingIsFalse :
      createsCounterfactualRanking ≡ false

open WorldFactReceipt public

------------------------------------------------------------------------
-- CPRS: official parliamentary records pay the legislative outcome.
------------------------------------------------------------------------

cprsAugust2009Negatived : WorldFactReceipt
cprsAugust2009Negatived =
  world-fact-receipt
    "world:cprs:2009-08-13:second-reading-negatived"
    March.cprs2009
    parliamentOfficialRecord
    "Carbon Pollution Reduction Scheme Bill 2009 - Parliament of Australia"
    "https://www.aph.gov.au/Parliamentary_Business/Bills_Legislation/Bills_Search_Results/Result?bId=r4127"
    "2026-10-12"
    legislativeOutcome
    "The Carbon Pollution Reduction Scheme Bill 2009 was negatived at second reading in the Senate on 13 August 2009."
    true refl
    false refl
    false refl

cprsDecember2009Negatived : WorldFactReceipt
cprsDecember2009Negatived =
  world-fact-receipt
    "world:cprs:2009-12-02:third-reading-negatived"
    March.cprs2009
    parliamentOfficialRecord
    "Bills discharged, laid aside or negatived 1991-2011 - Parliament of Australia"
    "https://www.aph.gov.au/Parliamentary_Business/Statistics/Senate_StatsNet_Classic/Consolidations/Bills_discharged_laid_aside_or_negatived_1991-2011"
    "2026-10-12"
    legislativeOutcome
    "The Carbon Pollution Reduction Scheme Bill 2009 [No. 2] was negatived at third reading in the Senate on 2 December 2009."
    true refl
    false refl
    false refl

cprsAustralianGreensAmendmentRecord : WorldFactReceipt
cprsAustralianGreensAmendmentRecord =
  world-fact-receipt
    "world:cprs:2009:greens-second-reading-amendment"
    March.cprs2009
    parliamentOfficialRecord
    "Second reading amendments - 2009 - Parliament of Australia"
    "https://www.aph.gov.au/Parliamentary_Business/Statistics/Senate_StatsNet_Classic/legislation/Amendments/Second_reading/2009"
    "2026-10-12"
    legislativeOutcome
    "Parliament records an Australian Greens second-reading amendment to the Carbon Pollution Reduction Scheme Bill 2009 as negatived."
    true refl
    false refl
    false refl

cprsWorldFacts : List WorldFactReceipt
cprsWorldFacts =
  cprsAugust2009Negatived
  ∷ cprsDecember2009Negatived
  ∷ cprsAustralianGreensAmendmentRecord
  ∷ []

------------------------------------------------------------------------
-- South Australia: AEMO pays a high-renewable operational episode and names
-- batteries as one component of system-security management.
------------------------------------------------------------------------

southAustralia2022Islanding : WorldFactReceipt
southAustralia2022Islanding =
  world-fact-receipt
    "world:sa:2022-islanding:91-percent-renewable"
    March.southAustraliaRenewables
    independentSystemOperator
    "AEMO CEO speech at The Australian Energy Nation Forum 2025"
    "https://www.aemo.com.au/newsroom/speeches-and-presentations/aemo-ceo-speech-at-the-australian-energy-nation-forum-2025"
    "2026-10-12"
    operationalSystemState
    "AEMO reports that during South Australia's November 2022 islanding event the region operated at 91 percent renewable energy."
    true refl
    false refl
    false refl

southAustraliaBatteryFrequencyRole : WorldFactReceipt
southAustraliaBatteryFrequencyRole =
  world-fact-receipt
    "world:sa:2022-islanding:battery-frequency-support"
    March.southAustraliaRenewables
    independentSystemOperator
    "AEMO CEO speech at The Australian Energy Nation Forum 2025"
    "https://www.aemo.com.au/newsroom/speeches-and-presentations/aemo-ceo-speech-at-the-australian-energy-nation-forum-2025"
    "2026-10-12"
    operationalSupportRole
    "AEMO states that frequency during the South Australian islanding episode was managed using batteries and gas generation, alongside four synchronous condensers in the network."
    true refl
    false refl
    false refl

southAustralia2025SystemReport : WorldFactReceipt
southAustralia2025SystemReport =
  world-fact-receipt
    "world:sa:2025-electricity-report:grid-forming-battery-context"
    March.southAustraliaRenewables
    independentSystemOperator
    "2025 South Australian Electricity Report"
    "https://www.aemo.com.au/-/media/files/electricity/nem/planning_and_forecasting/sa_advisory/2025/2025-south-australian-electricity-report.pdf"
    "2026-10-12"
    operationalSupportRole
    "AEMO's 2025 South Australian Electricity Report describes growing grid-forming battery capability while retaining gas-powered generation as a current stabilising and low-renewable-availability resource."
    true refl
    false refl
    false refl

southAustraliaWorldFacts : List WorldFactReceipt
southAustraliaWorldFacts =
  southAustralia2022Islanding
  ∷ southAustraliaBatteryFrequencyRole
  ∷ southAustralia2025SystemReport
  ∷ []

------------------------------------------------------------------------
-- A fact bundle pays observed substrate only.  Causal/counterfactual bridges
-- are separate proof obligations.
------------------------------------------------------------------------

record ExternalWorldFactBundle (case : March.MarchCase) : Set where
  constructor external-world-fact-bundle
  field
    facts : List WorldFactReceipt
    directObservedSubstratePaid : Bool
    directObservedSubstratePaidIsTrue :
      directObservedSubstratePaid ≡ true
    partyCausalAttributionPaid : Bool
    partyCausalAttributionPaidIsFalse :
      partyCausalAttributionPaid ≡ false
    counterfactualTrajectoryPaid : Bool
    counterfactualTrajectoryPaidIsFalse :
      counterfactualTrajectoryPaid ≡ false

open ExternalWorldFactBundle public

cprsExternalWorldBundle : ExternalWorldFactBundle March.cprs2009
cprsExternalWorldBundle =
  external-world-fact-bundle
    cprsWorldFacts
    true refl
    false refl
    false refl

southAustraliaExternalWorldBundle :
  ExternalWorldFactBundle March.southAustraliaRenewables
southAustraliaExternalWorldBundle =
  external-world-fact-bundle
    southAustraliaWorldFacts
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Reviewed causal bridge.
--
-- No canonical inhabitant is supplied.  This is the remaining empirical seam
-- between direct institutional facts and a governance-transition premise.
------------------------------------------------------------------------

record ReviewedCausalBridge (case : March.MarchCase) : Set₁ where
  constructor reviewed-causal-bridge
  field
    sourceRefs : List String
    reviewRef : String
    CausalPremise : Set
    causalPremiseWitness : CausalPremise
    sameCase : March.MarchCase
    sameCaseMatches : sameCase ≡ case
    establishesPartySpecificCause : Bool
    establishesCounterfactualTrajectory : Bool

open ReviewedCausalBridge public

record TransitionAdmission
    (case : March.MarchCase)
    (bundle : ExternalWorldFactBundle case) : Set₁ where
  constructor transition-admission
  field
    causalBridge : ReviewedCausalBridge case
    observedFactsRetained : Bool
    observedFactsRetainedIsTrue : observedFactsRetained ≡ true
    directFactsAloneCreateCausalBridge : Bool
    directFactsAloneCreateCausalBridgeIsFalse :
      directFactsAloneCreateCausalBridge ≡ false

open TransitionAdmission public

------------------------------------------------------------------------
-- Compiler into the existing world-transition evidence carrier.
-- Construction requires the separately reviewed causal bridge.
------------------------------------------------------------------------

cprsWorldTransitionEvidenceFromAdmission :
  TransitionAdmission March.cprs2009 cprsExternalWorldBundle →
  Base.WorldTransitionEvidence Base.cprsSourcePaidCase
cprsWorldTransitionEvidenceFromAdmission admission =
  Base.world-transition-evidence
    "world-transition:cprs:reviewed-causal-bridge"
    (ReviewedCausalBridge.sourceRefs
      (TransitionAdmission.causalBridge admission))
    (ReviewedCausalBridge.reviewRef
      (TransitionAdmission.causalBridge admission))
    true refl
    ⊤
    tt
    false refl

------------------------------------------------------------------------
-- South Australia currently has independent world substrate but still lacks
-- the pinned Friendlyjordies M12 source unit required by the narrative lane.
-- Thus both source payment and any stronger causal bridge remain independent.
------------------------------------------------------------------------

record SouthAustraliaDualGate : Set₁ where
  constructor south-australia-dual-gate
  field
    sourceRecovery : Base.SouthAustraliaTransitionPrerequisite
    causalAdmission :
      TransitionAdmission
        March.southAustraliaRenewables
        southAustraliaExternalWorldBundle

southAustraliaDualGateCurrentlyBlocked : SouthAustraliaDualGate → ⊥
southAustraliaDualGateCurrentlyBlocked gate =
  Base.southAustraliaTransitionPrerequisiteCurrentlyImpossible
    (SouthAustraliaDualGate.sourceRecovery gate)

------------------------------------------------------------------------
-- Hard non-promotion boundaries.
------------------------------------------------------------------------

data LegislativeOutcomeImpliesPartyCause : Set where
data HighRenewableEpisodeImpliesGovernanceSuperiority : Set where
data BatterySupportImpliesBatteryOnlyCausation : Set where
data InstitutionalFactBundleImpliesCounterfactual : Set where

legislativeOutcomeDoesNotImplyPartyCause :
  LegislativeOutcomeImpliesPartyCause → ⊥
legislativeOutcomeDoesNotImplyPartyCause ()

highRenewableEpisodeDoesNotImplyGovernanceSuperiority :
  HighRenewableEpisodeImpliesGovernanceSuperiority → ⊥
highRenewableEpisodeDoesNotImplyGovernanceSuperiority ()

batterySupportDoesNotImplyBatteryOnlyCausation :
  BatterySupportImpliesBatteryOnlyCausation → ⊥
batterySupportDoesNotImplyBatteryOnlyCausation ()

institutionalFactsDoNotCreateCounterfactual :
  InstitutionalFactBundleImpliesCounterfactual → ⊥
institutionalFactsDoNotCreateCounterfactual ()

record FriendlyjordiesWorldEvidenceBoundary : Set where
  constructor friendlyjordies-world-evidence-boundary
  field
    cprsLegislativeFactsPaid : Bool
    cprsLegislativeFactsPaidIsTrue : cprsLegislativeFactsPaid ≡ true
    southAustraliaOperationalFactsPaid : Bool
    southAustraliaOperationalFactsPaidIsTrue :
      southAustraliaOperationalFactsPaid ≡ true
    southAustraliaBatteryRolePaid : Bool
    southAustraliaBatteryRolePaidIsTrue :
      southAustraliaBatteryRolePaid ≡ true
    partyCausalAttributionStillOpen : Bool
    partyCausalAttributionStillOpenIsTrue :
      partyCausalAttributionStillOpen ≡ true
    governanceCounterfactualStillOpen : Bool
    governanceCounterfactualStillOpenIsTrue :
      governanceCounterfactualStillOpen ≡ true
    southAustraliaNarrativeSourceStillOpen : Bool
    southAustraliaNarrativeSourceStillOpenIsTrue :
      southAustraliaNarrativeSourceStillOpen ≡ true

canonicalFriendlyjordiesWorldEvidenceBoundary :
  FriendlyjordiesWorldEvidenceBoundary
canonicalFriendlyjordiesWorldEvidenceBoundary =
  friendlyjordies-world-evidence-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
