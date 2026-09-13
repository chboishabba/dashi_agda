module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGMassCurrentAcquisitionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallBidiExact as Wall

------------------------------------------------------------------------
-- MATERIAL-EFFECTIVE NEGATIVE-G: FIRST EMPIRICAL BIDI LEAF
--
-- The current scientific wall begins at an observational collision: net
-- electrical current does not determine net mass current.  Therefore the
-- shortest reverse-search target is the component-resolved source carrier,
-- not a stronger anomalous-force claim.
------------------------------------------------------------------------

data MassCurrentAcquisitionLeaf : Set where
  componentDensityLeaf : MassCurrentAcquisitionLeaf
  componentMassLeaf : MassCurrentAcquisitionLeaf
  componentChargeLeaf : MassCurrentAcquisitionLeaf
  componentVelocityLeaf : MassCurrentAcquisitionLeaf
  spatialDistributionLeaf : MassCurrentAcquisitionLeaf
  massCurrentDerivationLeaf : MassCurrentAcquisitionLeaf
  stressEnergyEligibilityLeaf : MassCurrentAcquisitionLeaf

producerForLeaf : MassCurrentAcquisitionLeaf → Search.ProducerClass
producerForLeaf componentDensityLeaf = Search.empiricalEvidenceProducer
producerForLeaf componentMassLeaf = Search.propositionSourceProducer
producerForLeaf componentChargeLeaf = Search.propositionSourceProducer
producerForLeaf componentVelocityLeaf = Search.empiricalEvidenceProducer
producerForLeaf spatialDistributionLeaf = Search.empiricalEvidenceProducer
producerForLeaf massCurrentDerivationLeaf = Search.discriminatorProducer
producerForLeaf stressEnergyEligibilityLeaf = Search.identityProducer

currentWallReallyStartsAtComponentResolvedMassCurrent :
  Wall.currentScientificWallDiscriminator ≡ Wall.componentResolvedMassCurrent
currentWallReallyStartsAtComponentResolvedMassCurrent =
  Wall.currentScientificWallStartsAtMassCurrent

chargeObservationCannotPayMassCurrent :
  Current.netMassCurrent Current.chargeCancelsMassRemainsFixture
    ≡ Current.netMassCurrent Current.chargeCancelsMassCancelsFixture → ⊥
chargeObservationCannotPayMassCurrent =
  Current.netChargeCurrentDoesNotDetermineMassCurrent

record MassCurrentAcquisitionBundle : Set where
  constructor mass-current-acquisition-bundle
  field
    densityLeaf : MassCurrentAcquisitionLeaf
    densityLeafIsExact : densityLeaf ≡ componentDensityLeaf
    massLeaf : MassCurrentAcquisitionLeaf
    massLeafIsExact : massLeaf ≡ componentMassLeaf
    chargeLeaf : MassCurrentAcquisitionLeaf
    chargeLeafIsExact : chargeLeaf ≡ componentChargeLeaf
    velocityLeaf : MassCurrentAcquisitionLeaf
    velocityLeafIsExact : velocityLeaf ≡ componentVelocityLeaf
    distributionLeaf : MassCurrentAcquisitionLeaf
    distributionLeafIsExact : distributionLeaf ≡ spatialDistributionLeaf
    derivationLeaf : MassCurrentAcquisitionLeaf
    derivationLeafIsExact : derivationLeaf ≡ massCurrentDerivationLeaf
    eligibilityLeaf : MassCurrentAcquisitionLeaf
    eligibilityLeafIsExact : eligibilityLeaf ≡ stressEnergyEligibilityLeaf

canonicalMassCurrentAcquisitionBundle : MassCurrentAcquisitionBundle
canonicalMassCurrentAcquisitionBundle =
  mass-current-acquisition-bundle
    componentDensityLeaf refl
    componentMassLeaf refl
    componentChargeLeaf refl
    componentVelocityLeaf refl
    spatialDistributionLeaf refl
    massCurrentDerivationLeaf refl
    stressEnergyEligibilityLeaf refl

record MassCurrentAcquisitionBoundary : Set where
  constructor mass-current-acquisition-boundary
  field
    strongerAnomalySearchIsCurrentFirstLeaf : Bool
    electricalCurrentAloneDeterminesMassCurrent : Bool
    componentResolvedCarrierIsCurrentFirstLeaf : Bool
    massCurrentAloneConstructsFullStressEnergy : Bool
    stressEnergyAloneProvesNegativeEffectiveG : Bool
    eachEmpiricalPaymentNeedsSameObjectProvenance : Bool

canonicalMassCurrentAcquisitionBoundary : MassCurrentAcquisitionBoundary
canonicalMassCurrentAcquisitionBoundary =
  mass-current-acquisition-boundary false false true false false true
