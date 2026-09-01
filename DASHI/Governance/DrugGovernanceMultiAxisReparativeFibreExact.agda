module DASHI.Governance.DrugGovernanceMultiAxisReparativeFibreExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Planning.NonSubstitutionalReparationExact as Repair
import DASHI.Governance.DrugGovernanceHistoricalBurdenPathExact as BurdenPath
import DASHI.Governance.DrugGovernanceBenefitCaptureRepairResidueExact as BenefitRepair
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Indigenous

------------------------------------------------------------------------
-- DRUG-GOVERNANCE MULTI-AXIS REPARATIVE FIBRE
--
-- Repair is not one Boolean.  This owner specialises the canonical
-- NonSubstitutionalReparationExact pattern to eight drug-governance axes while
-- retaining the ordered historical burden path as an independent coordinate.
------------------------------------------------------------------------

data DrugRepairAxis : Set where
  acknowledgementAxis
  truthHistoryAxis
  materialRestitutionBenefitAxis
  institutionalReformAxis
  categoryAuthorityRestorationAxis
  decisionRightsAxis
  sovereignAuthorityAxis
  nonRepetitionAxis
  : DrugRepairAxis

data DrugRepairStatus : Set where
  openRepair acknowledgedRepair repairedRepair : DrugRepairStatus

record DrugReparativeFibre : Set where
  constructor drugReparativeFibre
  field
    status : DrugRepairAxis → DrugRepairStatus

open DrugReparativeFibre public

------------------------------------------------------------------------
-- Canonical fibres corresponding to progressively richer repair surfaces.
------------------------------------------------------------------------

acknowledgementOnly : DrugReparativeFibre
acknowledgementOnly = drugReparativeFibre statusAt
  where
  statusAt : DrugRepairAxis → DrugRepairStatus
  statusAt acknowledgementAxis = acknowledgedRepair
  statusAt truthHistoryAxis = openRepair
  statusAt materialRestitutionBenefitAxis = openRepair
  statusAt institutionalReformAxis = openRepair
  statusAt categoryAuthorityRestorationAxis = openRepair
  statusAt decisionRightsAxis = openRepair
  statusAt sovereignAuthorityAxis = openRepair
  statusAt nonRepetitionAxis = openRepair

materialBenefitOnly : DrugReparativeFibre
materialBenefitOnly = drugReparativeFibre statusAt
  where
  statusAt : DrugRepairAxis → DrugRepairStatus
  statusAt acknowledgementAxis = openRepair
  statusAt truthHistoryAxis = openRepair
  statusAt materialRestitutionBenefitAxis = repairedRepair
  statusAt institutionalReformAxis = openRepair
  statusAt categoryAuthorityRestorationAxis = openRepair
  statusAt decisionRightsAxis = openRepair
  statusAt sovereignAuthorityAxis = openRepair
  statusAt nonRepetitionAxis = openRepair

authorityReformWithoutSovereignty : DrugReparativeFibre
authorityReformWithoutSovereignty = drugReparativeFibre statusAt
  where
  statusAt : DrugRepairAxis → DrugRepairStatus
  statusAt acknowledgementAxis = acknowledgedRepair
  statusAt truthHistoryAxis = repairedRepair
  statusAt materialRestitutionBenefitAxis = repairedRepair
  statusAt institutionalReformAxis = repairedRepair
  statusAt categoryAuthorityRestorationAxis = repairedRepair
  statusAt decisionRightsAxis = repairedRepair
  statusAt sovereignAuthorityAxis = openRepair
  statusAt nonRepetitionAxis = openRepair

fullSyntheticRepair : DrugReparativeFibre
fullSyntheticRepair = drugReparativeFibre (λ _ → repairedRepair)

acknowledgementDoesNotCloseTruthHistory :
  status acknowledgementOnly truthHistoryAxis ≡ repairedRepair → ⊥
acknowledgementDoesNotCloseTruthHistory ()

materialBenefitDoesNotRestoreCategoryAuthority :
  status materialBenefitOnly categoryAuthorityRestorationAxis ≡ repairedRepair → ⊥
materialBenefitDoesNotRestoreCategoryAuthority ()

materialBenefitDoesNotRestoreSovereignty :
  status materialBenefitOnly sovereignAuthorityAxis ≡ repairedRepair → ⊥
materialBenefitDoesNotRestoreSovereignty ()

authorityReformDoesNotByItselfCloseSovereignty :
  status authorityReformWithoutSovereignty sovereignAuthorityAxis ≡ repairedRepair → ⊥
authorityReformDoesNotByItselfCloseSovereignty ()

authorityReformDoesNotByItselfCloseNonRepetition :
  status authorityReformWithoutSovereignty nonRepetitionAxis ≡ repairedRepair → ⊥
authorityReformDoesNotByItselfCloseNonRepetition ()

------------------------------------------------------------------------
-- Same coarse repair label can hide different fine repair fibres.
------------------------------------------------------------------------

data CoarseRepairSurface : Set where
  samePositiveRepairNarrative : CoarseRepairSurface

data RepairVariant : Set where
  acknowledgedVariant materialVariant : RepairVariant

coarseRepair : RepairVariant → CoarseRepairSurface
coarseRepair _ = samePositiveRepairNarrative

fineRepair : RepairVariant → DrugReparativeFibre
fineRepair acknowledgedVariant = acknowledgementOnly
fineRepair materialVariant = materialBenefitOnly

repairCode : RepairVariant → DrugRepairStatus
repairCode acknowledgedVariant = status acknowledgementOnly truthHistoryAxis
repairCode materialVariant = status materialBenefitOnly truthHistoryAxis

-- A distinct axis gives the actual nonfactorability witness.
materialCode : RepairVariant → DrugRepairStatus
materialCode acknowledgedVariant = status acknowledgementOnly materialRestitutionBenefitAxis
materialCode materialVariant = status materialBenefitOnly materialRestitutionBenefitAxis

sameCoarseRepair : coarseRepair acknowledgedVariant ≡ coarseRepair materialVariant
sameCoarseRepair = refl

materialCodeDiffers : materialCode acknowledgedVariant ≡ materialCode materialVariant → ⊥
materialCodeDiffers ()

coarseRepairCannotRecoverMaterialRepair :
  INF.FactorsThrough coarseRepair materialCode → ⊥
coarseRepairCannotRecoverMaterialRepair =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness acknowledgedVariant materialVariant refl materialCodeDiffers)

------------------------------------------------------------------------
-- Cross-pollination welds: generic multi-axis repair, burden path, benefit
-- residue and sovereignty all remain separately typed.
------------------------------------------------------------------------

nonSubstitutionBoundary : Repair.NonSubstitutionBoundary
nonSubstitutionBoundary = Repair.canonicalNonSubstitutionBoundary

burdenPathBoundary : BurdenPath.HistoricalBurdenPathBoundary
burdenPathBoundary = BurdenPath.canonicalHistoricalBurdenPathBoundary

benefitRepairBoundary : BenefitRepair.BenefitCaptureRepairResidueBoundary
benefitRepairBoundary = BenefitRepair.canonicalBenefitCaptureRepairResidueBoundary

indigenousBoundary : Indigenous.IndigenousAuthorityEnvelopeBoundary
indigenousBoundary = Indigenous.canonicalIndigenousAuthorityEnvelopeBoundary

data OneRepairedAxisPromotesGlobalRepair : Set where

data MaterialRepairPromotesSovereignty : Set where

data HistoricalAcknowledgementPromotesNonRepetition : Set where

data FullSyntheticRepairPromotesEmpiricalHistoricalClaim : Set where

oneAxisDoesNotPromoteGlobalRepair : OneRepairedAxisPromotesGlobalRepair → ⊥
oneAxisDoesNotPromoteGlobalRepair ()

materialRepairDoesNotPromoteSovereignty : MaterialRepairPromotesSovereignty → ⊥
materialRepairDoesNotPromoteSovereignty ()

acknowledgementDoesNotPromoteNonRepetition : HistoricalAcknowledgementPromotesNonRepetition → ⊥
acknowledgementDoesNotPromoteNonRepetition ()

syntheticRepairDoesNotPromoteEmpiricalHistory : FullSyntheticRepairPromotesEmpiricalHistoricalClaim → ⊥
syntheticRepairDoesNotPromoteEmpiricalHistory ()

record DrugGovernanceMultiAxisReparativeBoundary : Set where
  constructor drugGovernanceMultiAxisReparativeBoundary
  field
    repairIsMultiAxis : Bool
    repairIsMultiAxisIsTrue : repairIsMultiAxis ≡ true
    acknowledgementClosesAllRepair : Bool
    acknowledgementClosesAllRepairIsFalse : acknowledgementClosesAllRepair ≡ false
    materialBenefitRestoresAuthority : Bool
    materialBenefitRestoresAuthorityIsFalse : materialBenefitRestoresAuthority ≡ false
    authorityReformAutomaticallyRestoresSovereignty : Bool
    authorityReformAutomaticallyRestoresSovereigntyIsFalse :
      authorityReformAutomaticallyRestoresSovereignty ≡ false
    repairedPresentSurfaceErasesBurdenHistory : Bool
    repairedPresentSurfaceErasesBurdenHistoryIsFalse :
      repairedPresentSurfaceErasesBurdenHistory ≡ false

canonicalDrugGovernanceMultiAxisReparativeBoundary :
  DrugGovernanceMultiAxisReparativeBoundary
canonicalDrugGovernanceMultiAxisReparativeBoundary =
  drugGovernanceMultiAxisReparativeBoundary
    true refl false refl false refl false refl false refl
