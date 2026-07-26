module DASHI.Governance.GeopoliticalDifferentialEvidence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; Set₁)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Governance.TraumaExploitationDifferential as Differential

------------------------------------------------------------------------
-- Claim identity and scope.

record GeopoliticalClaimScope : Set where
  constructor geopoliticalClaimScope
  field
    claimId : String
    jurisdiction : String
    timeStart timeEnd : String
    populationScope : String
    sectorScope : String
    technologyScope : String

open GeopoliticalClaimScope public

------------------------------------------------------------------------
-- Source receipts.

data SourceRole : Set where
  officialStatistic : SourceRole
  companyDisclosure : SourceRole
  courtDocument : SourceRole
  unDocument : SourceRole
  academicStudy : SourceRole
  journalism : SourceRole
  advocacyReport : SourceRole

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    sourceId : String
    sourceURI : String
    publisher : String
    publicationDate : String
    accessDate : String
    contentDigest : String
    quotedSpan : String
    sourceRole : SourceRole

open SourceReceipt public

record IndependentEvidence : Set₁ where
  constructor independentEvidence
  field
    sources : List SourceReceipt
    sourceCompletenessReceipt : String
    sourcesAreIndependentOfModelGain : Bool
    sourcesAreIndependentOfModelGainIsTrue :
      sourcesAreIndependentOfModelGain ≡ true

open IndependentEvidence public

------------------------------------------------------------------------
-- Legal procedural status.

data ProceduralStage : Set where
  applicationFiled : ProceduralStage
  provisionalMeasures : ProceduralStage
  jurisdictionDecision : ProceduralStage
  counterMemorialPending : ProceduralStage
  meritsPending : ProceduralStage
  finalMeritsJudgment : ProceduralStage
  discontinued : ProceduralStage

data FinalMeritsStatus : ProceduralStage → Set where
  finalMeritsStatus : FinalMeritsStatus finalMeritsJudgment

provisionalOrderDoesNotEntailFinalMeritsJudgment :
  FinalMeritsStatus provisionalMeasures → ⊥
provisionalOrderDoesNotEntailFinalMeritsJudgment ()

counterMemorialPendingDoesNotEntailFinalMeritsJudgment :
  FinalMeritsStatus counterMemorialPending → ⊥
counterMemorialPendingDoesNotEntailFinalMeritsJudgment ()

record LegalStatusReceipt : Set where
  constructor legalStatusReceipt
  field
    court : String
    caseName : String
    caseNumber : String
    proceduralStage : ProceduralStage
    orderDate : String
    holdingSummary : String
    pendingMerits : Bool
    legalSource : SourceReceipt

open LegalStatusReceipt public

------------------------------------------------------------------------
-- Economic and cyber-export evidence.

data CurrencyUnit : Set where
  usd : CurrencyUnit
  aud : CurrencyUnit
  ils : CurrencyUnit
  eur : CurrencyUnit
  unspecifiedCurrency : CurrencyUnit

record MeasuredAmount : Set where
  constructor measuredAmount
  field
    wholeUnits : Nat
    unit : CurrencyUnit
    measurementLabel : String

open MeasuredAmount public

record CyberExportEvidence : Set where
  constructor cyberExportEvidence
  field
    exportValue : MeasuredAmount
    investmentValue : MeasuredAmount
    globalShareBasisPoints : Nat
    companyCount : Nat
    referenceYear : Nat
    methodology : String
    economicSource : SourceReceipt
    cyberSpecificityReceipt : String

open CyberExportEvidence public

record GlobalPlayerCriterion : Set₁ where
  constructor globalPlayerCriterion
  field
    minimumExportValue : MeasuredAmount
    minimumGlobalShareBasisPoints : Nat
    minimumCompanyCount : Nat
    criterionMethodology : String
    MeetsCriterion : CyberExportEvidence → Set

open GlobalPlayerCriterion public

record GlobalPlayerSupported
  (criterion : GlobalPlayerCriterion)
  (evidence : CyberExportEvidence)
  : Set₁ where
  constructor globalPlayerSupported
  field
    criterionMet : MeetsCriterion criterion evidence

------------------------------------------------------------------------
-- Deployment and mechanism linkage.

record ProductDeploymentReceipt : Set where
  constructor productDeploymentReceipt
  field
    seller : String
    buyer : String
    product : String
    deploymentContext : String
    documentedCapability : String
    documentedUse : String
    affectedPopulation : String
    deploymentSource : SourceReceipt

open ProductDeploymentReceipt public

record DoctrineTechnologyMechanismReceipt : Set₁ where
  constructor doctrineTechnologyMechanismReceipt
  field
    doctrine : String
    technology : String
    institution : String
    externalisationChannel : String
    doctrineSource : SourceReceipt
    technologySource : SourceReceipt
    deployment : ProductDeploymentReceipt
    doctrineToTechnologyReceipt : String
    technologyToInstitutionReceipt : String
    institutionToExternalisationReceipt : String

open DoctrineTechnologyMechanismReceipt public

------------------------------------------------------------------------
-- PNF/ITIR evidence fibres.  Support, contradiction, alternatives and missing
-- axes remain distinct rather than being collapsed into one confidence score.

record GeopoliticalEvidenceFibre : Set₁ where
  constructor geopoliticalEvidenceFibre
  field
    supportFibre : List PNF.CandidatePNF
    contradictionFibre : List PNF.CandidatePNF
    alternativeExplanationFibre : List PNF.CandidatePNF
    missingAxis : List String
    fibreEnumerationReceipt : String

open GeopoliticalEvidenceFibre public

data AlternativeMechanism : Set where
  civilianInnovation : AlternativeMechanism
  ordinaryDefensiveSecurity : AlternativeMechanism
  commercialPathDependence : AlternativeMechanism
  militarySpillover : AlternativeMechanism
  occupationDerivedTesting : AlternativeMechanism
  otherMechanism : AlternativeMechanism

record AlternativeExplanationReceipt : Set where
  constructor alternativeExplanationReceipt
  field
    mechanism : AlternativeMechanism
    description : String
    supportingSource : SourceReceipt

------------------------------------------------------------------------
-- Full evidence and promotion packets.

record GeopoliticalDifferentialEvidencePacket : Set₁ where
  constructor geopoliticalDifferentialEvidencePacket
  field
    scope : GeopoliticalClaimScope
    independentEvidencePacket : IndependentEvidence
    legalStatus : LegalStatusReceipt
    cyberEconomy : CyberExportEvidence
    mechanism : DoctrineTechnologyMechanismReceipt
    evidenceFibre : GeopoliticalEvidenceFibre
    alternativesConsidered : List AlternativeExplanationReceipt
    timeAlignmentReceipt : String
    scopeCompatibilityReceipt : String

open GeopoliticalDifferentialEvidencePacket public

record GeopoliticalClaimPromotionReceipt
  (packet : GeopoliticalDifferentialEvidencePacket)
  : Set₁ where
  constructor geopoliticalClaimPromotionReceipt
  field
    sourceComplete : Bool
    sourceCompleteIsTrue : sourceComplete ≡ true
    scopeCompatible : Bool
    scopeCompatibleIsTrue : scopeCompatible ≡ true
    timeAligned : Bool
    timeAlignedIsTrue : timeAligned ≡ true
    mechanismSupported : Bool
    mechanismSupportedIsTrue : mechanismSupported ≡ true
    counterevidenceConsidered : Bool
    counterevidenceConsideredIsTrue : counterevidenceConsidered ≡ true
    legalStatusPrecise : Bool
    legalStatusPreciseIsTrue : legalStatusPrecise ≡ true
    noCollectiveEssentialisation : Bool
    noCollectiveEssentialisationIsTrue : noCollectiveEssentialisation ≡ true
    independentEvidenceRetained :
      IndependentEvidence
    independentEvidenceMatchesPacket :
      independentEvidenceRetained
      ≡ independentEvidencePacket packet
    promotionInterpretation : String

open GeopoliticalClaimPromotionReceipt public

------------------------------------------------------------------------
-- Local gain cannot be the sole source of a geopolitical promotion receipt.

record GainOnlyEvidence : Set where
  constructor gainOnlyEvidence
  field
    gainLabel : String

record GainOnlyPromotionAttempt
  (packet : GeopoliticalDifferentialEvidencePacket)
  : Set₁ where
  constructor gainOnlyPromotionAttempt
  field
    gain : GainOnlyEvidence
    noIndependentEvidenceAvailable : IndependentEvidence → ⊥
    claimedPromotion : GeopoliticalClaimPromotionReceipt packet

open GainOnlyPromotionAttempt public

gainEvidenceAloneCannotPromote :
  ∀ {packet} →
  GainOnlyPromotionAttempt packet → ⊥
gainEvidenceAloneCannotPromote attempt =
  noIndependentEvidenceAvailable attempt
    (independentEvidenceRetained (claimedPromotion attempt))

------------------------------------------------------------------------
-- Differential attribution must be evidence-bound before it receives a public
-- geopolitical interpretation.

record EvidenceBoundDifferentialAttribution
  {S : _}
  (D : Differential.TraumaExploitationDifferential S)
  (x : _)
  : Set₁ where
  field
    attribution : Differential.DifferentialAttribution D x
    packet : GeopoliticalDifferentialEvidencePacket
    promotion : GeopoliticalClaimPromotionReceipt packet
