module DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as SignedGR
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact as Gravity
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- NEGATIVE-G -> EXISTING ANTIGRAVITY CLAIM ROUTER
--
-- A sign-reversed gravitational coupling is one candidate theory coordinate.
-- It is not allowed to become a generic explanation for every phenomenon that
-- may be colloquially labelled antigravity.
------------------------------------------------------------------------

data NegativeGClaimRelevance : Set where
  directFrozenSignProbe : NegativeGClaimRelevance
  metricSignProbe : NegativeGClaimRelevance
  notImpliedByCouplingSignAlone : NegativeGClaimRelevance

negativeGRelevance : Anti.AntigravityClaim → NegativeGClaimRelevance
negativeGRelevance Anti.reducedPassiveWeight = directFrozenSignProbe
negativeGRelevance Anti.changedFreeFallResponse = directFrozenSignProbe
negativeGRelevance Anti.remoteRepulsiveField = directFrozenSignProbe
negativeGRelevance Anti.alteredInertialResponse = notImpliedByCouplingSignAlone
negativeGRelevance Anti.persistentPropulsiveImpulse = notImpliedByCouplingSignAlone
negativeGRelevance Anti.engineeredMetricResponse = metricSignProbe

record NegativeGClaimProbe (claim : Anti.AntigravityClaim) : Set where
  constructor negative-g-claim-probe
  field
    signedProbe : SignedGR.FrozenSignedCouplingProbe
    couplingIsNegative :
      SignedGR.sign signedProbe ≡ SignedGR.negativeCoupling

    relevance : NegativeGClaimRelevance
    relevanceMatches : relevance ≡ negativeGRelevance claim

    discriminator : Anti.RequiredDiscriminator
    discriminatorMatches :
      Anti.requiredDiscriminator claim ≡ discriminator

open NegativeGClaimProbe public

freeFallNegativeGProbe : NegativeGClaimProbe Anti.changedFreeFallResponse
freeFallNegativeGProbe = negative-g-claim-probe
  SignedGR.canonicalNegativeGFrozenProbe
  refl
  directFrozenSignProbe
  refl
  Anti.freeFallDiscriminator
  refl

remoteFieldNegativeGProbe : NegativeGClaimProbe Anti.remoteRepulsiveField
remoteFieldNegativeGProbe = negative-g-claim-probe
  SignedGR.canonicalNegativeGFrozenProbe
  refl
  directFrozenSignProbe
  refl
  Anti.externalTestMassDiscriminator
  refl

metricNegativeGProbe : NegativeGClaimProbe Anti.engineeredMetricResponse
metricNegativeGProbe = negative-g-claim-probe
  SignedGR.canonicalNegativeGFrozenProbe
  refl
  metricSignProbe
  refl
  Anti.metricClockDiscriminator
  refl

------------------------------------------------------------------------
-- NEGATIVE G IS NOT NEGATIVE MASS
--
-- The existing negative-mass BIDI separates inertial mass, passive response,
-- active gravitational source, Higgs mass parameter and pressure/source terms.
-- Negative G instead changes the source-to-geometry coupling coordinate while
-- keeping the source sign fixed in the frozen probe.
------------------------------------------------------------------------

data NegativeGTheoryCoordinate : Set where
  sourceToGeometryCouplingSign : NegativeGTheoryCoordinate

data NegativeMassTheoryCoordinate : Set where
  sourceOrResponseMassCoordinate : Gravity.NegativeMassTarget → NegativeMassTheoryCoordinate

record NegativeGNegativeMassBoundary : Set where
  constructor negative-g-negative-mass-boundary
  field
    negativeGEqualsNegativeInertialMass : Bool
    negativeGEqualsNegativePassiveMass : Bool
    negativeGEqualsNegativeActiveSource : Bool
    negativeGEqualsHiggsMassSignChange : Bool
    negativeGRequiresSourceStressEnergySignFlip : Bool
    negativeGChangesCouplingOrientationWithFrozenSource : Bool

canonicalNegativeGNegativeMassBoundary : NegativeGNegativeMassBoundary
canonicalNegativeGNegativeMassBoundary =
  negative-g-negative-mass-boundary false false false false false true

------------------------------------------------------------------------
-- REVERSE PROOF SEARCH
------------------------------------------------------------------------

data NegativeGResidual : Set where
  missingSignedEinsteinLawRealisation : NegativeGResidual
  missingSelfConsistentNegativeGSolution : NegativeGResidual
  missingClaimSpecificNegativeGPrediction : NegativeGResidual
  missingClaimBoundObservation : NegativeGResidual
  missingOrdinaryPositiveGComparator : NegativeGResidual
  missingNegativeGAlternativeComparator : NegativeGResidual
  missingSameSourceGeometryWeld : NegativeGResidual

producerForNegativeGResidual : NegativeGResidual → Search.ProducerClass
producerForNegativeGResidual missingSignedEinsteinLawRealisation = Search.propositionSourceProducer
producerForNegativeGResidual missingSelfConsistentNegativeGSolution = Search.contradictionProducer
producerForNegativeGResidual missingClaimSpecificNegativeGPrediction = Search.discriminatorProducer
producerForNegativeGResidual missingClaimBoundObservation = Search.empiricalEvidenceProducer
producerForNegativeGResidual missingOrdinaryPositiveGComparator = Search.propositionSourceProducer
producerForNegativeGResidual missingNegativeGAlternativeComparator = Search.propositionSourceProducer
producerForNegativeGResidual missingSameSourceGeometryWeld = Search.identityProducer

record NegativeGAntigravityBoundary : Set where
  constructor negative-g-antigravity-boundary
  field
    negativeGIsAdmittedAsCounterfactualTheoryCoordinate : Bool
    negativeGIsEstablishedPhysicalConstantSign : Bool
    negativeGDirectlyTargetsFreeFallAndRemoteFieldClaims : Bool
    negativeGAloneImpliesAlteredInertialMass : Bool
    negativeGAloneImpliesReactionlessPropulsion : Bool
    frozenNegativeGProbeEqualsSolvedNegativeGGR : Bool
    negativeGPredictionAutomaticallyMatchesObservation : Bool
    negativeGAutomaticallyProvesAntigravity : Bool

canonicalNegativeGAntigravityBoundary : NegativeGAntigravityBoundary
canonicalNegativeGAntigravityBoundary =
  negative-g-antigravity-boundary true false true false false false false false
