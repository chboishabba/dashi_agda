module DASHI.Physics.GR.ControlledEMGWEinsteinCouplingDegeneracyExact where

open import DASHI.Core.Prelude

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.SchutzholdEMGWSourceLawExact as Source

------------------------------------------------------------------------
-- EINSTEIN SOURCE COUPLING != LOCAL METRIC-STRESS INTERACTION LABEL
--
-- For the standard Schuetzhold coupling h^{mu nu} T_{mu nu}, once the same
-- physical metric perturbation h and the same EM stress-energy are held fixed,
-- merely relabelling the Einstein source coupling sign does not create a new
-- local interaction Hamiltonian.  A signed-G model must either:
--   (a) re-solve source generation and hence change the physical h; or
--   (b) provide an explicit non-standard local photon-graviton coupling law.
------------------------------------------------------------------------

data LocalInteractionModel : Set where
  standardMetricStressCoupling : LocalInteractionModel
  modifiedLocalPhotonGravitonCoupling : LocalInteractionModel

data EinsteinSourceFixture : Set where
  positiveEinsteinSourceFixture : EinsteinSourceFixture
  negativeEinsteinSourceFixture : EinsteinSourceFixture

fixtureEinsteinSign : EinsteinSourceFixture → Signed.CouplingSign
fixtureEinsteinSign positiveEinsteinSourceFixture = Signed.positiveCoupling
fixtureEinsteinSign negativeEinsteinSourceFixture = Signed.negativeCoupling

data FixedPhysicalInteractionObservation : Set where
  sameStandardMetricStressInteraction : FixedPhysicalInteractionObservation

fixedPhysicalInteractionObserver :
  EinsteinSourceFixture → FixedPhysicalInteractionObservation
fixedPhysicalInteractionObserver _ = sameStandardMetricStressInteraction

fixedHStandardCouplingCollision :
  fixedPhysicalInteractionObserver positiveEinsteinSourceFixture
  ≡ fixedPhysicalInteractionObserver negativeEinsteinSourceFixture
fixedHStandardCouplingCollision = refl

record LocalExchangeModelReceipt : Set₁ where
  constructor local-exchange-model-receipt
  field
    interaction : Exchange.EMGWInteractionCarrier
    model : LocalInteractionModel
    einsteinSourceSign : Signed.CouplingSign

    SamePhysicalMetricPerturbation : Set
    samePhysicalMetricPerturbation : SamePhysicalMetricPerturbation

    SamePhysicalEMStressEnergy : Set
    samePhysicalEMStressEnergy : SamePhysicalEMStressEnergy

    SourceDynamicsReSolved : Set
    sourceDynamicsReSolved : SourceDynamicsReSolved

    LocalCouplingModificationReceipt : Set
    localCouplingModificationReceipt : LocalCouplingModificationReceipt

open LocalExchangeModelReceipt public

record ControlledExchangeSignedGBoundary : Set where
  constructor controlled-exchange-signed-g-boundary
  field
    standardLocalLawIsMetricStressCoupling : Bool
    fixedPhysicalHAloneIdentifiesEinsteinSourceSign : Bool
    fixedPhysicalHAndTNaiveGSignFlipChangesLocalExchange : Bool
    negativeEinsteinCouplingRequiresSourceDynamicsResolved : Bool
    alternativeLocalCouplingRequiresExplicitLaw : Bool
    controlledExchangeCanTestExplicitAlternativeLocalCoupling : Bool
    controlledExchangeCanTestReSolvedSignedGPrediction : Bool
    naiveSignedGRelabellingCountsAsModelDiscriminator : Bool

canonicalControlledExchangeSignedGBoundary : ControlledExchangeSignedGBoundary
canonicalControlledExchangeSignedGBoundary =
  controlled-exchange-signed-g-boundary
    true false false true true true true false
