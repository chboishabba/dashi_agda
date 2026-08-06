module DASHI.Visualisation.EventFilamentPersistenceExact where

open import DASHI.Core.Prelude

import DASHI.Visualisation.EventFilamentFieldExact as Event

------------------------------------------------------------------------
-- Finite exact completion of sections 687--708: path occupancy, probabilistic
-- linkage, threshold persistence, normalised coherence, perturbation budgets,
-- and an explicit end-to-end derived-thread object.

data EventId : Set where
  event0 : EventId
  event1 : EventId
  event2 : EventId

data ThreadId : Set where
  threadA : ThreadId
  threadB : ThreadId

data OccupancyPolicy : Set where
  disjointOccupancy : OccupancyPolicy
  overlappingOccupancy : OccupancyPolicy
  branchingOccupancy : OccupancyPolicy

record ThreadMembership : Set where
  constructor threadMembership
  field
    membershipEvent : EventId
    membershipThread : ThreadId

open ThreadMembership public

canonicalMemberships : List ThreadMembership
canonicalMemberships =
  threadMembership event0 threadA
  ∷ threadMembership event1 threadA
  ∷ threadMembership event2 threadB
  ∷ []

membershipCount : List ThreadMembership → Nat
membershipCount [] = 0
membershipCount (_ ∷ rest) = suc (membershipCount rest)

canonicalMembershipCountIsThree :
  membershipCount canonicalMemberships ≡ 3
canonicalMembershipCountIsThree = refl

------------------------------------------------------------------------
-- A scaled transition row.  The denominator is carried explicitly so a hard
-- optimiser is not silently substituted for uncertain path assignment.

record TransitionRow : Set where
  constructor transitionRow
  field
    sourceEvent : EventId
    toEventOneMass : Nat
    toEventTwoMass : Nat
    rowDenominator : Nat
    rowCloses :
      toEventOneMass + toEventTwoMass ≡ rowDenominator

open TransitionRow public

canonicalTransitionRow : TransitionRow
canonicalTransitionRow = transitionRow event0 2 1 3 refl

canonicalTransitionRowCloses :
  toEventOneMass canonicalTransitionRow
  + toEventTwoMass canonicalTransitionRow
  ≡ rowDenominator canonicalTransitionRow
canonicalTransitionRowCloses = rowCloses canonicalTransitionRow

data LinkageRepresentation : Set where
  maximumScorePath : LinkageRepresentation
  directedForest : LinkageRepresentation
  stochasticPathLaw : LinkageRepresentation

------------------------------------------------------------------------
-- Superlevel persistence.  Membership at a higher threshold implies
-- membership at the lower threshold in the declared finite filtration.

data Threshold : Set where
  highThreshold : Threshold
  mediumThreshold : Threshold
  lowThreshold : Threshold

data SuperlevelMember : Threshold → EventId → Set where
  event0AtHigh : SuperlevelMember highThreshold event0
  event0AtMedium : SuperlevelMember mediumThreshold event0
  event1AtMedium : SuperlevelMember mediumThreshold event1
  event0AtLow : SuperlevelMember lowThreshold event0
  event1AtLow : SuperlevelMember lowThreshold event1
  event2AtLow : SuperlevelMember lowThreshold event2

highIncludedInMedium :
  {event : EventId} →
  SuperlevelMember highThreshold event →
  SuperlevelMember mediumThreshold event
highIncludedInMedium event0AtHigh = event0AtMedium

mediumIncludedInLow :
  {event : EventId} →
  SuperlevelMember mediumThreshold event →
  SuperlevelMember lowThreshold event
mediumIncludedInLow event0AtMedium = event0AtLow
mediumIncludedInLow event1AtMedium = event1AtLow

highIncludedInLow :
  {event : EventId} →
  SuperlevelMember highThreshold event →
  SuperlevelMember lowThreshold event
highIncludedInLow membership =
  mediumIncludedInLow (highIncludedInMedium membership)

data PersistentFeature : Set where
  stableThreadFeature : PersistentFeature
  transientBridgeFeature : PersistentFeature
  persistentVoidFeature : PersistentFeature

record FeatureInterval : Set where
  constructor featureInterval
  field
    feature : PersistentFeature
    birthLevel : Nat
    deathLevel : Nat

open FeatureInterval public

canonicalStableThread : FeatureInterval
canonicalStableThread = featureInterval stableThreadFeature 9 2

canonicalThreadBirth : birthLevel canonicalStableThread ≡ 9
canonicalThreadBirth = refl

------------------------------------------------------------------------
-- Length-normalised support avoids rewarding a longer path merely for having
-- more integration domain.  Fractions are stored without hidden division.

record SupportRatio : Set where
  constructor supportRatio
  field
    integratedSupport : Nat
    pathLength : Nat

open SupportRatio public

coherentPath : SupportRatio
coherentPath = supportRatio 8 4

transversePerturbation : SupportRatio
transversePerturbation = supportRatio 6 4

coherentCrossProduct :
  integratedSupport coherentPath * pathLength transversePerturbation
  ≡
  32
coherentCrossProduct = refl

perturbedCrossProduct :
  integratedSupport transversePerturbation * pathLength coherentPath
  ≡
  24
perturbedCrossProduct = refl

coherentAndPerturbedRatiosDiffer : coherentPath ≡ transversePerturbation → ⊥
coherentAndPerturbedRatiosDiffer ()

record VariationalThreadScore : Set where
  constructor variationalThreadScore
  field
    supportReward : Nat
    speedPenalty : Nat
    curvaturePenalty : Nat

open VariationalThreadScore public

netThreadScore : VariationalThreadScore → Nat
netThreadScore score =
  supportReward score ∸
  (speedPenalty score + curvaturePenalty score)

canonicalVariationalScore : VariationalThreadScore
canonicalVariationalScore = variationalThreadScore 20 3 2

canonicalNetThreadScoreIsFifteen :
  netThreadScore canonicalVariationalScore ≡ 15
canonicalNetThreadScoreIsFifteen = refl

------------------------------------------------------------------------
-- Field-perturbation decomposition mirrors
-- |rhoHat-rho| <= weight error + parameter-induced kernel error.

record KernelParameterError : Set where
  constructor kernelParameterError
  field
    centreContribution : Nat
    covarianceContribution : Nat
    sharpnessContribution : Nat

open KernelParameterError public

kernelParameterBound : KernelParameterError → Nat
kernelParameterBound error =
  centreContribution error
  + covarianceContribution error
  + sharpnessContribution error

record FieldErrorCertificate : Set where
  constructor fieldErrorCertificate
  field
    coefficientError : Nat
    kernelError : KernelParameterError
    certifiedFieldError : Nat
    certificateCloses :
      coefficientError + kernelParameterBound kernelError
      ≡ certifiedFieldError

open FieldErrorCertificate public

canonicalFieldErrorCertificate : FieldErrorCertificate
canonicalFieldErrorCertificate =
  fieldErrorCertificate
    2
    (kernelParameterError 1 3 1)
    7
    refl

canonicalFieldErrorIsSeven :
  certifiedFieldError canonicalFieldErrorCertificate ≡ 7
canonicalFieldErrorIsSeven = refl

------------------------------------------------------------------------
-- The typed construction keeps observed events, inferred graph edges, thread
-- hypotheses, positive fields, slices, and final views distinct.

data FilamentPipelineStage : Set where
  observedEventSetStage : FilamentPipelineStage
  temporalGraphStage : FilamentPipelineStage
  threadHypothesisStage : FilamentPipelineStage
  positiveFieldStage : FilamentPipelineStage
  sliceFieldStage : FilamentPipelineStage
  inverseViewStage : FilamentPipelineStage

nextFilamentStage : FilamentPipelineStage → FilamentPipelineStage
nextFilamentStage observedEventSetStage = temporalGraphStage
nextFilamentStage temporalGraphStage = threadHypothesisStage
nextFilamentStage threadHypothesisStage = positiveFieldStage
nextFilamentStage positiveFieldStage = sliceFieldStage
nextFilamentStage sliceFieldStage = inverseViewStage
nextFilamentStage inverseViewStage = inverseViewStage

pipelineReachesViewInFiveSteps :
  nextFilamentStage
    (nextFilamentStage
      (nextFilamentStage
        (nextFilamentStage
          (nextFilamentStage observedEventSetStage))))
  ≡
  inverseViewStage
pipelineReachesViewInFiveSteps = refl

record DerivedThreadArtefact : Set where
  constructor derivedThreadArtefact
  field
    observedKnotCount : Nat
    inferredSegmentCount : Nat
    assignmentRepresentation : LinkageRepresentation
    provenanceRetained : Bool
    uncertaintyRetained : Bool
    positiveFieldMass : Nat
    ridgeNormalCount : Nat

open DerivedThreadArtefact public

canonicalDerivedThreadArtefact : DerivedThreadArtefact
canonicalDerivedThreadArtefact =
  derivedThreadArtefact
    3 2 stochasticPathLaw true true
    Event.scalarFieldSample
    (Event.ridgeNormalDirections 4 1)

canonicalArtefactRetainsProvenance :
  provenanceRetained canonicalDerivedThreadArtefact ≡ true
canonicalArtefactRetainsProvenance = refl

canonicalArtefactHasThreeRidgeNormals :
  ridgeNormalCount canonicalDerivedThreadArtefact ≡ 3
canonicalArtefactHasThreeRidgeNormals = refl

record EventFilamentPersistenceBoundary : Set where
  constructor eventFilamentPersistenceBoundary
  field
    maximumScorePathIsUniqueThreadDecomposition : Bool
    maximumScorePathIsUniqueThreadDecompositionIsFalse :
      maximumScorePathIsUniqueThreadDecomposition ≡ false

    oneIsovalueDeterminesPersistentTopology : Bool
    oneIsovalueDeterminesPersistentTopologyIsFalse :
      oneIsovalueDeterminesPersistentTopology ≡ false

    longerRawIntegralAlwaysMeansMoreCoherentRidge : Bool
    longerRawIntegralAlwaysMeansMoreCoherentRidgeIsFalse :
      longerRawIntegralAlwaysMeansMoreCoherentRidge ≡ false

    inferredSegmentIsObservedContinuum : Bool
    inferredSegmentIsObservedContinuumIsFalse :
      inferredSegmentIsObservedContinuum ≡ false

open EventFilamentPersistenceBoundary public

canonicalEventFilamentPersistenceBoundary :
  EventFilamentPersistenceBoundary
canonicalEventFilamentPersistenceBoundary =
  eventFilamentPersistenceBoundary false refl false refl false refl false refl
