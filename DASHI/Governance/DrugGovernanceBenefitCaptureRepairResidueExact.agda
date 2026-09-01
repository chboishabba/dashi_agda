module DASHI.Governance.DrugGovernanceBenefitCaptureRepairResidueExact where

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.DrugGovernanceHistoricalBurdenExternalisationExact as HistoricalBurden
import DASHI.Governance.DrugGovernanceFiveProbeWorldExact as Five
import DASHI.Governance.DrugGovernanceRepairMandateGateExact as MandateGate

------------------------------------------------------------------------
-- BENEFIT CAPTURE / REPAIR RESIDUE
--
-- A later institution can capture clinical/commercial value without thereby
-- inheriting, discharging, or extinguishing a historical repair obligation.
------------------------------------------------------------------------

data ValueSurface : Set where
  samePositivePsychedelicValue : ValueSurface

data BenefitPosition : Set where
  concentratedInstitutionalCapture
  sharedCommunityBenefit
  : BenefitPosition

data RepairResidue : Set where
  historicalRepairOutstanding
  historicalRepairAcknowledged
  historicalRepairDischarged
  : RepairResidue

record BenefitRepairWorld : Set where
  constructor benefitRepairWorld
  field
    surface : ValueSurface
    benefit : BenefitPosition
    repair : RepairResidue

open BenefitRepairWorld public

capturedOutstandingWorld : BenefitRepairWorld
capturedOutstandingWorld = benefitRepairWorld
  samePositivePsychedelicValue
  concentratedInstitutionalCapture
  historicalRepairOutstanding

sharedAcknowledgedWorld : BenefitRepairWorld
sharedAcknowledgedWorld = benefitRepairWorld
  samePositivePsychedelicValue
  sharedCommunityBenefit
  historicalRepairAcknowledged

capturedDischargedWorld : BenefitRepairWorld
capturedDischargedWorld = benefitRepairWorld
  samePositivePsychedelicValue
  concentratedInstitutionalCapture
  historicalRepairDischarged

sameValueDifferentBenefit :
  surface capturedOutstandingWorld ≡ surface sharedAcknowledgedWorld
sameValueDifferentBenefit = refl

benefitDiffers :
  benefit capturedOutstandingWorld ≡ benefit sharedAcknowledgedWorld → ⊥
benefitDiffers ()

sameValueCannotRecoverBenefit : INF.FactorsThrough surface benefit → ⊥
sameValueCannotRecoverBenefit =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness capturedOutstandingWorld sharedAcknowledgedWorld refl benefitDiffers)

sameBenefitDifferentRepair :
  benefit capturedOutstandingWorld ≡ benefit capturedDischargedWorld
sameBenefitDifferentRepair = refl

repairDiffers :
  repair capturedOutstandingWorld ≡ repair capturedDischargedWorld → ⊥
repairDiffers ()

benefitCannotRecoverRepair : INF.FactorsThrough benefit repair → ⊥
benefitCannotRecoverRepair =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness capturedOutstandingWorld capturedDischargedWorld refl repairDiffers)

------------------------------------------------------------------------
-- BIDI probes.
------------------------------------------------------------------------

benefitBundle : Discriminator.ExperimentBundle BenefitRepairWorld
benefitBundle = Discriminator.experimentBundle
  BenefitPosition benefit 3
  "benefit-routing probe on common positive psychedelic value surface"
  "requires evidence about who captures material/organizational benefit"

repairBundle : Discriminator.ExperimentBundle BenefitRepairWorld
repairBundle = Discriminator.experimentBundle
  RepairResidue repair 2
  "historical-repair-residue probe"
  "requires history/provenance evidence rather than present positive valuation"

benefitSeparates :
  Discriminator.BundleSeparates benefitBundle capturedOutstandingWorld sharedAcknowledgedWorld
benefitSeparates = Discriminator.bundleSeparates (λ ())

repairSeparates :
  Discriminator.BundleSeparates repairBundle capturedOutstandingWorld capturedDischargedWorld
repairSeparates = Discriminator.bundleSeparates (λ ())

------------------------------------------------------------------------
-- Repair remains authority-gated.
------------------------------------------------------------------------

repairAdmissionDemand :
  MandateGate.RepairAdmissionDemand MandateGate.reviseBenefitRouting
repairAdmissionDemand = MandateGate.benefitRevisionNeedsMaterialGovernanceAuthority

data BenefitCapturePromotesRepairDischarge : Set where

data BenefitSharingPromotesHistoricalCausation : Set where

data RepairAcknowledgementPromotesDischarge : Set where

data RepairDischargePromotesOriginatingAuthority : Set where

benefitCaptureDoesNotPromoteRepairDischarge : BenefitCapturePromotesRepairDischarge → ⊥
benefitCaptureDoesNotPromoteRepairDischarge ()

benefitSharingDoesNotPromoteHistoricalCausation : BenefitSharingPromotesHistoricalCausation → ⊥
benefitSharingDoesNotPromoteHistoricalCausation ()

acknowledgementDoesNotPromoteDischarge : RepairAcknowledgementPromotesDischarge → ⊥
acknowledgementDoesNotPromoteDischarge ()

repairDischargeDoesNotPromoteOriginatingAuthority : RepairDischargePromotesOriginatingAuthority → ⊥
repairDischargeDoesNotPromoteOriginatingAuthority ()

historicalBurdenBoundary : HistoricalBurden.HistoricalBurdenExternalisationBoundary
historicalBurdenBoundary = HistoricalBurden.canonicalHistoricalBurdenExternalisationBoundary

fiveProbeMaterialSeparator :
  Discriminator.BundleSeparates
    Five.materialBundle Five.baseExternalWorld Five.sharedBenefitWorld
fiveProbeMaterialSeparator = Five.materialSeparates

record BenefitCaptureRepairResidueBoundary : Set where
  constructor benefitCaptureRepairResidueBoundary
  field
    presentPositiveValueDeterminesBenefitRouting : Bool
    presentPositiveValueDeterminesBenefitRoutingIsFalse : presentPositiveValueDeterminesBenefitRouting ≡ false
    benefitRoutingDeterminesRepairStatus : Bool
    benefitRoutingDeterminesRepairStatusIsFalse : benefitRoutingDeterminesRepairStatus ≡ false
    historicalRepairRequiresIndependentProbe : Bool
    historicalRepairRequiresIndependentProbeIsTrue : historicalRepairRequiresIndependentProbe ≡ true
    benefitRepairStillRequiresMandate : Bool
    benefitRepairStillRequiresMandateIsTrue : benefitRepairStillRequiresMandate ≡ true

canonicalBenefitCaptureRepairResidueBoundary : BenefitCaptureRepairResidueBoundary
canonicalBenefitCaptureRepairResidueBoundary = benefitCaptureRepairResidueBoundary
  false refl false refl true refl true refl
