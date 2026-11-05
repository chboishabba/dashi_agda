{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.Zhang2025EMGravitySourceClaimExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)


import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti

data Contradiction : Set where

------------------------------------------------------------------------
-- SOURCE FIRST: ONE PATENT FAMILY IS NOT THREE INDEPENDENT EXPERIMENTS.
-- Zhang / Xiao / Li: CN119943525A, US12417870B1, WO2026157422A1.
-- These identifiers record documentary origin, NOT validated operation.
------------------------------------------------------------------------

data Publication : Set where
  chineseApplication : Publication
  unitedStatesGrant : Publication
  internationalApplication : Publication

publicationNumber : Publication → String
publicationNumber chineseApplication = "CN119943525A"
publicationNumber unitedStatesGrant = "US12417870B1"
publicationNumber internationalApplication = "WO2026157422A1"

data PatentFamily : Set where
  zhang2025Family : PatentFamily

family : Publication → PatentFamily
family _ = zhang2025Family

familyIdentity : (p q : Publication) → family p ≡ family q
familyIdentity _ _ = refl

------------------------------------------------------------------------
-- A source *claims* controlled motion, not observed gravitational geometry.
-- The three unsupported stronger propositions are deliberately separate.
------------------------------------------------------------------------

data CandidateClaim : Set where
  controlledTargetMotion : CandidateClaim
  massReduction : CandidateClaim
  remoteRepulsiveField : CandidateClaim
  propagatingGravityWave : CandidateClaim
  engineeredMetricShift : CandidateClaim

data PatentClaimEntitlement : CandidateClaim → Set where
  claimedTargetMotion : PatentClaimEntitlement controlledTargetMotion

patentDoesNotClaimMeasuredMassReduction :
  PatentClaimEntitlement massReduction → Contradiction
patentDoesNotClaimMeasuredMassReduction ()

patentDoesNotClaimMeasuredGW :
  PatentClaimEntitlement propagatingGravityWave → Contradiction
patentDoesNotClaimMeasuredGW ()

patentDoesNotClaimMeasuredMetric :
  PatentClaimEntitlement engineeredMetricShift → Contradiction
patentDoesNotClaimMeasuredMetric ()

data DocumentaryAuthority : Set where
  originalPatent : DocumentaryAuthority
  socialTranscript : DocumentaryAuthority

record DocumentaryClaimReceipt : Set where
  constructor documentary-claim-receipt
  field
    publication : Publication
    entitlement : PatentClaimEntitlement controlledTargetMotion
    authority : DocumentaryAuthority
    originalLocator : String

canonicalPatentClaim : DocumentaryClaimReceipt
canonicalPatentClaim =
  documentary-claim-receipt unitedStatesGrant claimedTargetMotion originalPatent
    "https://patents.google.com/patent/US12417870B1/en"

------------------------------------------------------------------------
-- BIDI: a nonconducting / nominally nonmagnetic target can be polarizable.
-- This is an ENUMERATED classical countermodel, not an apparatus prediction.
------------------------------------------------------------------------

data TargetClass : Set where
  nonconductingNonmagnetic : TargetClass
  magneticConducting : TargetClass

data ClassicalMechanism : Set where
  dielectricPolarisation : ClassicalMechanism
  chargeElectricForce : ClassicalMechanism
  magneticGradientForce : ClassicalMechanism
  suspensionTorque : ClassicalMechanism
  mechanicalVibration : ClassicalMechanism
  radiativeMomentum : ClassicalMechanism

data PossibleClassicalRoute : TargetClass → ClassicalMechanism → Set where
  dielectricInsulator :
    PossibleClassicalRoute nonconductingNonmagnetic dielectricPolarisation
  chargedInsulator :
    PossibleClassicalRoute nonconductingNonmagnetic chargeElectricForce
  magneticTarget :
    PossibleClassicalRoute magneticConducting magneticGradientForce

nonconductorDoesNotExcludePolarisation :
  PossibleClassicalRoute nonconductingNonmagnetic dielectricPolarisation
nonconductorDoesNotExcludePolarisation = dielectricInsulator

------------------------------------------------------------------------
-- "The device moves a suspended ball" is NOT an existing DASHI antigravity
-- claim. An optional gravitational interpretation must name its consumer.
------------------------------------------------------------------------

data ScientificConsumer : Set where
  apparatusMotion : ScientificConsumer
  externalTestMass : ScientificConsumer
  freeFall : ScientificConsumer
  metricClock : ScientificConsumer
  farFieldTTStrain : ScientificConsumer

data GravitationalRoute : ScientificConsumer → Set where
  remoteProbe :
    (claim : Anti.AntigravityClaim) →
    claim ≡ Anti.remoteRepulsiveField →
    GravitationalRoute externalTestMass
  freeFallProbe :
    (claim : Anti.AntigravityClaim) →
    claim ≡ Anti.changedFreeFallResponse →
    GravitationalRoute freeFall
  metricProbe :
    (claim : Anti.AntigravityClaim) →
    claim ≡ Anti.engineeredMetricResponse →
    GravitationalRoute metricClock

canonicalExternalRoute : GravitationalRoute externalTestMass
canonicalExternalRoute =
  remoteProbe Anti.remoteRepulsiveField refl

canonicalFreeFallRoute : GravitationalRoute freeFall
canonicalFreeFallRoute =
  freeFallProbe Anti.changedFreeFallResponse refl

canonicalMetricRoute : GravitationalRoute metricClock
canonicalMetricRoute =
  metricProbe Anti.engineeredMetricResponse refl

data SameClaimConsumer : ScientificConsumer → ScientificConsumer → Set where
  sameConsumer : {c : ScientificConsumer} → SameClaimConsumer c c

motionIsNotMetricConsumer :
  SameClaimConsumer apparatusMotion metricClock → Contradiction
motionIsNotMetricConsumer ()

motionIsNotGWConsumer :
  SameClaimConsumer apparatusMotion farFieldTTStrain → Contradiction
motionIsNotGWConsumer ()

------------------------------------------------------------------------
-- Enumerated documentary boundary; no experiment or physical law follows.
------------------------------------------------------------------------

record PatentClaimBoundary : Set where
  constructor patent-claim-boundary
  field
    patentIsExperimentalReplication : Bool
    threePublicationsAreThreeExperiments : Bool
    nonconductorExcludesClassicalPolarisation : Bool
    targetMotionAutomaticallyEstablishesMetric : Bool
    targetMotionAutomaticallyEstablishesGW : Bool
    strongGravityClaimNeedsIndependentConsumer : Bool

canonicalPatentClaimBoundary : PatentClaimBoundary
canonicalPatentClaimBoundary =
  patent-claim-boundary false false false false false true
