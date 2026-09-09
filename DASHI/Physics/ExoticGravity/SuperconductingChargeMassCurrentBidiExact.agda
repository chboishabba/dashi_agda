module DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.LiTorrMicroscopicToBulkGravitomagneticSumBidiExact as Bulk
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGProofSearchExact as NegativeGSearch
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- CHARGE CURRENT != MASS CURRENT
------------------------------------------------------------------------

data SignedCurrent : Set where
  negativeCurrent : SignedCurrent
  zeroCurrent : SignedCurrent
  positiveCurrent : SignedCurrent

data CurrentFixture : Set where
  chargeCancelsMassRemainsFixture : CurrentFixture
  chargeCancelsMassCancelsFixture : CurrentFixture

netChargeCurrent : CurrentFixture → SignedCurrent
netChargeCurrent _ = zeroCurrent

netMassCurrent : CurrentFixture → SignedCurrent
netMassCurrent chargeCancelsMassRemainsFixture = positiveCurrent
netMassCurrent chargeCancelsMassCancelsFixture = zeroCurrent

chargeCurrentCollision :
  netChargeCurrent chargeCancelsMassRemainsFixture
    ≡ netChargeCurrent chargeCancelsMassCancelsFixture
chargeCurrentCollision = refl

netChargeCurrentDoesNotDetermineMassCurrent :
  netMassCurrent chargeCancelsMassRemainsFixture
    ≡ netMassCurrent chargeCancelsMassCancelsFixture → ⊥
netChargeCurrentDoesNotDetermineMassCurrent ()

------------------------------------------------------------------------
-- Source reconstruction needed to pay J_m(x).
-- The final coordinate is only eligibility for downstream T_{mu nu}; it is
-- not itself a full laboratory stress-energy receipt.
------------------------------------------------------------------------

record MassCurrentSourceReconstructionReceipt : Set₁ where
  constructor mass-current-source-reconstruction-receipt
  field
    bulkSource : Bulk.BulkSourceIntegral

    ComponentDensityReceipt : Set
    componentDensityReceipt : ComponentDensityReceipt

    ComponentMassReceipt : Set
    componentMassReceipt : ComponentMassReceipt

    ComponentChargeReceipt : Set
    componentChargeReceipt : ComponentChargeReceipt

    ComponentVelocityReceipt : Set
    componentVelocityReceipt : ComponentVelocityReceipt

    SpatialDistributionReceipt : Set
    spatialDistributionReceipt : SpatialDistributionReceipt

    MassCurrentDerivationReceipt : Set
    massCurrentDerivationReceipt : MassCurrentDerivationReceipt

    StressEnergyEligibilityReceipt : Set
    stressEnergyEligibilityReceipt : StressEnergyEligibilityReceipt

open MassCurrentSourceReconstructionReceipt public

data MassCurrentResidual : Set where
  missingComponentDensity : MassCurrentResidual
  missingComponentMass : MassCurrentResidual
  missingComponentCharge : MassCurrentResidual
  missingComponentVelocity : MassCurrentResidual
  missingSpatialDistribution : MassCurrentResidual
  missingMassCurrentDerivation : MassCurrentResidual
  missingStressEnergyEligibility : MassCurrentResidual
  chargeMassCurrentContradictionOpen : MassCurrentResidual

producerForMassCurrentResidual : MassCurrentResidual → Search.ProducerClass
producerForMassCurrentResidual missingComponentDensity = Search.empiricalEvidenceProducer
producerForMassCurrentResidual missingComponentMass = Search.propositionSourceProducer
producerForMassCurrentResidual missingComponentCharge = Search.propositionSourceProducer
producerForMassCurrentResidual missingComponentVelocity = Search.empiricalEvidenceProducer
producerForMassCurrentResidual missingSpatialDistribution = Search.empiricalEvidenceProducer
producerForMassCurrentResidual missingMassCurrentDerivation = Search.discriminatorProducer
producerForMassCurrentResidual missingStressEnergyEligibility = Search.identityProducer
producerForMassCurrentResidual chargeMassCurrentContradictionOpen = Search.contradictionProducer

existingNegativeGFirstStage : NegativeGSearch.ConstitutiveNegativeGStage
existingNegativeGFirstStage = NegativeGSearch.currentConstitutiveNegativeGStage

existingNegativeGFirstStageIsSourceCurrent :
  existingNegativeGFirstStage ≡ NegativeGSearch.sourceCurrentStage
existingNegativeGFirstStageIsSourceCurrent = NegativeGSearch.currentStageIsSourceCurrent

record ChargeMassCurrentBoundary : Set where
  constructor charge-mass-current-boundary
  field
    netElectricalCurrentDeterminesMassCurrent : Bool
    electricalCurrentCancellationImpliesMassCurrentCancellation : Bool
    measuredSupercurrentAlonePaysSourceCurrentLeaf : Bool
    componentResolvedSourceReconstructionRequired : Bool
    spatialDistributionRequired : Bool
    stressEnergyEligibilityRequired : Bool
    massCurrentReceiptAutomaticallyConstructsFullStressEnergy : Bool
    massCurrentReceiptAutomaticallyProvesConstitutiveNegativeG : Bool

canonicalChargeMassCurrentBoundary : ChargeMassCurrentBoundary
canonicalChargeMassCurrentBoundary =
  charge-mass-current-boundary false false false true true true false false
