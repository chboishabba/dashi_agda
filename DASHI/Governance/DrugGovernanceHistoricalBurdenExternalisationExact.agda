module DASHI.Governance.DrugGovernanceHistoricalBurdenExternalisationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.DrugGovernanceClassifierEvolutionPathExact as Evolution
import DASHI.Governance.DrugGovernanceErrorAsymmetryBurdenAllocationExact as Burden
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Power

------------------------------------------------------------------------
-- HISTORICAL BURDEN EXTERNALISATION
--
-- Finite DASHI geometry only.  A classifier path may change who receives value
-- and who bears uncertainty/repair burdens.  A later positive route does not
-- erase earlier burden residue, and benefit transfer is not repair transfer.
------------------------------------------------------------------------

data BurdenEpoch : Set where
  punitiveEpoch
  therapeuticReopeningEpoch
  commercialExpansionEpoch
  : BurdenEpoch

data HistoricalBurdenBearer : Set where
  criminalisedCarrier
  careExcludedCarrier
  affectedCommunity
  indigenousSovereignCommunity
  publicInstitution
  commercialActor
  : HistoricalBurdenBearer

data BenefitRecipient : Set where
  noPositiveBenefitRecipient
  clinicalInstitutionBenefit
  commercialBenefitRecipient
  communityBenefitRecipient
  : BenefitRecipient

data RepairResponsibilityState : Set where
  repairBurdenOutstanding
  repairBurdenAcknowledged
  repairBurdenDischargedByReceipt
  : RepairResponsibilityState

data PublicSurface : Set where
  samePositiveTherapeuticSurface : PublicSurface

record HistoricalBurdenState : Set where
  constructor historicalBurdenState
  field
    epoch : BurdenEpoch
    surface : PublicSurface
    uncertaintyBearer : HistoricalBurdenBearer
    benefitRecipient : BenefitRecipient
    repairState : RepairResponsibilityState
    punitiveResidueRetained : Bool

open HistoricalBurdenState public

therapeuticInstitutionalState : HistoricalBurdenState
therapeuticInstitutionalState = historicalBurdenState
  therapeuticReopeningEpoch
  samePositiveTherapeuticSurface
  affectedCommunity
  clinicalInstitutionBenefit
  repairBurdenOutstanding
  true

commercialExpansionState : HistoricalBurdenState
commercialExpansionState = historicalBurdenState
  commercialExpansionEpoch
  samePositiveTherapeuticSurface
  affectedCommunity
  commercialBenefitRecipient
  repairBurdenOutstanding
  true

communityBenefitRepairState : HistoricalBurdenState
communityBenefitRepairState = historicalBurdenState
  commercialExpansionEpoch
  samePositiveTherapeuticSurface
  affectedCommunity
  communityBenefitRecipient
  repairBurdenAcknowledged
  true

sameSurfaceTherapeuticCommercial :
  surface therapeuticInstitutionalState ≡ surface commercialExpansionState
sameSurfaceTherapeuticCommercial = refl

benefitRecipientDiffers :
  benefitRecipient therapeuticInstitutionalState
  ≡ benefitRecipient commercialExpansionState → ⊥
benefitRecipientDiffers ()

sameSurfaceCannotRecoverBenefitRecipient :
  INF.FactorsThrough surface benefitRecipient → ⊥
sameSurfaceCannotRecoverBenefitRecipient =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      therapeuticInstitutionalState commercialExpansionState
      refl benefitRecipientDiffers)

benefitTransferDoesNotDischargeRepair :
  repairState commercialExpansionState ≡ repairBurdenDischargedByReceipt → ⊥
benefitTransferDoesNotDischargeRepair ()

positiveTherapeuticSurfaceDoesNotErasePunitiveResidue :
  punitiveResidueRetained therapeuticInstitutionalState ≡ false → ⊥
positiveTherapeuticSurfaceDoesNotErasePunitiveResidue ()

------------------------------------------------------------------------
-- Historical externalisation event.
------------------------------------------------------------------------

data BurdenTransferMode : Set where
  burdenRetainedByInstitution
  burdenExternalisedToClassifiedCarrier
  burdenExternalisedToAffectedCommunity
  burdenAcknowledgedForRepair
  burdenDischargedWithIndependentReceipt
  : BurdenTransferMode

record HistoricalBurdenTransfer : Set where
  constructor historicalBurdenTransfer
  field
    errorKind : Burden.ClassificationErrorKind
    beforeBearer : HistoricalBurdenBearer
    afterBearer : HistoricalBurdenBearer
    mode : BurdenTransferMode
    historicalResidueRetained : Bool
    transferIsNotFaultAttribution : Bool

canonicalPunitiveExternalisation : HistoricalBurdenTransfer
canonicalPunitiveExternalisation = historicalBurdenTransfer
  Burden.wrongfulPunitiveClassification
  publicInstitution
  criminalisedCarrier
  burdenExternalisedToClassifiedCarrier
  true true

canonicalCommercialExternalisation : HistoricalBurdenTransfer
canonicalCommercialExternalisation = historicalBurdenTransfer
  Burden.wrongfulCommercialLegitimacy
  commercialActor
  affectedCommunity
  burdenExternalisedToAffectedCommunity
  true true

------------------------------------------------------------------------
-- Cross-pollination boundaries.
------------------------------------------------------------------------

evolutionBoundary : Evolution.DrugGovernanceClassifierEvolutionBoundary
evolutionBoundary = Evolution.canonicalDrugGovernanceClassifierEvolutionBoundary

powerBoundary : Power.SocioTechnicalPowerSelectionBoundary
powerBoundary = Power.canonicalSocioTechnicalPowerSelectionBoundary

data LaterBenefitPromotesHistoricalRepair : Set where

data ExternalisedBurdenPromotesCarrierFault : Set where

data CommercialValuePromotesRepairDischarge : Set where

data ClassifierRevisionPromotesBurdenExtinction : Set where

laterBenefitDoesNotPromoteHistoricalRepair : LaterBenefitPromotesHistoricalRepair → ⊥
laterBenefitDoesNotPromoteHistoricalRepair ()

externalisedBurdenDoesNotPromoteCarrierFault : ExternalisedBurdenPromotesCarrierFault → ⊥
externalisedBurdenDoesNotPromoteCarrierFault ()

commercialValueDoesNotPromoteRepairDischarge : CommercialValuePromotesRepairDischarge → ⊥
commercialValueDoesNotPromoteRepairDischarge ()

classifierRevisionDoesNotPromoteBurdenExtinction : ClassifierRevisionPromotesBurdenExtinction → ⊥
classifierRevisionDoesNotPromoteBurdenExtinction ()

record HistoricalBurdenExternalisationBoundary : Set where
  constructor historicalBurdenExternalisationBoundary
  field
    laterPositiveRouteErasesEarlierBurden : Bool
    laterPositiveRouteErasesEarlierBurdenIsFalse : laterPositiveRouteErasesEarlierBurden ≡ false
    benefitTransferEqualsRepairTransfer : Bool
    benefitTransferEqualsRepairTransferIsFalse : benefitTransferEqualsRepairTransfer ≡ false
    burdenExternalisationEqualsFault : Bool
    burdenExternalisationEqualsFaultIsFalse : burdenExternalisationEqualsFault ≡ false
    samePositiveSurfaceDeterminesBenefitRecipient : Bool
    samePositiveSurfaceDeterminesBenefitRecipientIsFalse : samePositiveSurfaceDeterminesBenefitRecipient ≡ false
    historyIndexedBurdenTransferIsExplicit : Bool
    historyIndexedBurdenTransferIsExplicitIsTrue : historyIndexedBurdenTransferIsExplicit ≡ true

canonicalHistoricalBurdenExternalisationBoundary : HistoricalBurdenExternalisationBoundary
canonicalHistoricalBurdenExternalisationBoundary = historicalBurdenExternalisationBoundary
  false refl false refl false refl false refl true refl
