module DASHI.Interop.ObservationTransportSpine where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Cross-domain observation / transport spine.
--
-- This module records the common DASHI pattern shared by ITIR/PNF, Nashi,
-- SeaMeInIt, the brain lane, and the avian-compass discussion:
--
--   latent carrier -> lossy observation quotient -> admissibility gate
--     -> transport -> promotion boundary
--
-- It is only a vocabulary and receipt-boundary surface.  It does not
-- validate any empirical lane and does not turn a quotient into an
-- invertible reconstruction.

data ObservationDomain : Set where
  itirPNFDomain :
    ObservationDomain

  nashiDomain :
    ObservationDomain

  seaMeInItDomain :
    ObservationDomain

  brainDomain :
    ObservationDomain

  avianCompassDomain :
    ObservationDomain

  wikidataDomain :
    ObservationDomain

  wikidataWikipediaJoinDomain :
    ObservationDomain

  lightTransportDomain :
    ObservationDomain

  lesGlesWorldTransportDomain :
    ObservationDomain

  quantumPathFibreDomain :
    ObservationDomain

  stationaryPhaseToyReceiptDomain :
    ObservationDomain

  videoCodecDomain :
    ObservationDomain

  chemistryRightLimitsDomain :
    ObservationDomain

  proteinHormoneChemistryCellDomain :
    ObservationDomain

  developmentalGenomicInverseDomain :
    ObservationDomain

  genomeSensorimotorConstraintDomain :
    ObservationDomain

  bioAnimalexicDomain :
    ObservationDomain

  physicsChemistryBiologyDNAAggregateDomain :
    ObservationDomain

  persistentComputationDomain :
    ObservationDomain

  aggregateBidiTranslationDomain :
    ObservationDomain

  evolutionaryMDLTransportDomain :
    ObservationDomain

  multiObserverScienceDomain :
    ObservationDomain

  freeWillPNFBranchDomain :
    ObservationDomain

  inverseCultureOperatorDomain :
    ObservationDomain

  observerCultureEvolutionAggregateDomain :
    ObservationDomain

  operatorInvariantEquivalenceDomain :
    ObservationDomain

  metaphorAlignmentDomain :
    ObservationDomain

  succinctCommunicationDomain :
    ObservationDomain

  misunderstandingQuotientDomain :
    ObservationDomain

  semanticOperatorAlignmentAggregateDomain :
    ObservationDomain

  fibrePressureMetricDomain :
    ObservationDomain

  knotWeaveTopologyCultureDomain :
    ObservationDomain

data PromotionBoundary : Set where
  diagnosticOnly :
    PromotionBoundary

  candidateSurfaceOnly :
    PromotionBoundary

  promotedArtifact :
    PromotionBoundary

  nonPromotingObservation :
    PromotionBoundary

data NonClaimBoundary : Set where
  quotientIsNotInjective :
    NonClaimBoundary

  correlationIsNotCausation :
    NonClaimBoundary

  behaviorIsNotQualia :
    NonClaimBoundary

  reportIsNotGroundTruth :
    NonClaimBoundary

  localReceiptIsNotGlobalOntology :
    NonClaimBoundary

record ObservationTransportSurface : Set₁ where
  field
    domain :
      ObservationDomain

    LatentCarrier :
      Set

    ObservationQuotient :
      Set

    AdmissibilityGate :
      Set

    TransportOperator :
      Set

    Artifact :
      Set

    observe :
      LatentCarrier →
      ObservationQuotient

    gate :
      ObservationQuotient →
      AdmissibilityGate

    transport :
      LatentCarrier →
      AdmissibilityGate →
      TransportOperator →
      Artifact

    promotionBoundary :
      PromotionBoundary

    nonClaims :
      List NonClaimBoundary

    plainReading :
      String

open ObservationTransportSurface public

record LossyQuotientBoundary
    (surface : ObservationTransportSurface) : Set₁ where
  field
    ObservationalEquivalenceClass :
      Set

    classOfCarrier :
      ObservationTransportSurface.LatentCarrier surface →
      ObservationalEquivalenceClass

    quotientManyToOne :
      Set

    noStateRecoveryClaim :
      Bool

    noStateRecoveryClaimIsTrue :
      noStateRecoveryClaim ≡ true

    boundaryNote :
      String

open LossyQuotientBoundary public

record JointObservationNarrowing
    (left right : ObservationTransportSurface) : Set₁ where
  field
    JointQuotient :
      Set

    JointEquivalenceClass :
      Set

    jointObserve :
      ObservationTransportSurface.LatentCarrier left →
      JointQuotient

    leftKernel :
      Set

    rightKernel :
      Set

    complementaryKernelAssumption :
      Set

    narrowsResidualClass :
      Set

    stillNonInvertible :
      Bool

    stillNonInvertibleIsTrue :
      stillNonInvertible ≡ true

open JointObservationNarrowing public

data BoundaryAcknowledgement : Set where
  acknowledged :
    BoundaryAcknowledgement

record ObservationTransportGovernance
    (surface : ObservationTransportSurface) : Set where
  field
    quotientAwareness :
      BoundaryAcknowledgement

    noQualiaPromotion :
      BoundaryAcknowledgement

    noCausalPromotionFromCorrelation :
      BoundaryAcknowledgement

    boundaryStatement :
      String

open ObservationTransportGovernance public

canonicalObservationNonClaims : List NonClaimBoundary
canonicalObservationNonClaims =
  quotientIsNotInjective
  ∷ correlationIsNotCausation
  ∷ behaviorIsNotQualia
  ∷ reportIsNotGroundTruth
  ∷ localReceiptIsNotGlobalOntology
  ∷ []

canonicalNonPromotingBoundary : PromotionBoundary
canonicalNonPromotingBoundary = nonPromotingObservation

canonicalNoRecoveryFlag : Bool
canonicalNoRecoveryFlag = true

canonicalNoRecoveryFlagIsTrue : canonicalNoRecoveryFlag ≡ true
canonicalNoRecoveryFlagIsTrue = refl
