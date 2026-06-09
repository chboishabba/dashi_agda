module DASHI.Reasoning.MultiObserverScienceQuotient where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Multi-observer science as quotient fusion.
--
-- This module records the thread delta:
--
--   deterministic latent universe
--     -> many-to-one observation quotient
--     -> apparent randomness at the observation surface
--     -> multi-observer quotient fusion
--     -> residual / admissibility checks
--
-- It is intentionally a typed boundary surface, not a hidden-variable
-- theorem, not a universal determinism proof, and not a proof that peer
-- review closes scientific truth.

data ObservationRole : Set where
  instrumentRole :
    ObservationRole

  humanObserverRole :
    ObservationRole

  modelRole :
    ObservationRole

  reviewerRole :
    ObservationRole

data ScienceQuotientGuard : Set where
  noUniversalDeterminismProof :
    ScienceQuotientGuard

  noHiddenVariableProof :
    ScienceQuotientGuard

  noScienceTruthClosure :
    ScienceQuotientGuard

  noPeerReviewInfallibility :
    ScienceQuotientGuard

  noFullLatentStateRecovery :
    ScienceQuotientGuard

  noObserverNeutralCompleteSlice :
    ScienceQuotientGuard

canonicalScienceQuotientGuards :
  List ScienceQuotientGuard
canonicalScienceQuotientGuards =
  noUniversalDeterminismProof
  ∷ noHiddenVariableProof
  ∷ noScienceTruthClosure
  ∷ noPeerReviewInfallibility
  ∷ noFullLatentStateRecovery
  ∷ noObserverNeutralCompleteSlice
  ∷ []

data ScienceFirstMissing : Set where
  missingLatentDynamicsReceipt :
    ScienceFirstMissing

  missingObservationKernelReceipt :
    ScienceFirstMissing

  missingManyToOneWitness :
    ScienceFirstMissing

  missingObserverCalibrationReceipt :
    ScienceFirstMissing

  missingFusionResidualMetric :
    ScienceFirstMissing

  missingAdmissibilityPolicy :
    ScienceFirstMissing

  missingIndependentReviewTrace :
    ScienceFirstMissing

  missingExternalReplicationReceipt :
    ScienceFirstMissing

record DeterministicLatentUniverse : Set₁ where
  field
    Time :
      Set

    LatentState :
      Set

    next :
      LatentState →
      LatentState

    stateAt :
      Time →
      LatentState

    deterministicStepReceipt :
      (sigma : LatentState) →
      next sigma ≡ next sigma

    carrierMeaning :
      String

    determinismBoundary :
      String

open DeterministicLatentUniverse public

record ObservationQuotient
    (U : DeterministicLatentUniverse) : Set₁ where
  field
    Observer :
      Set

    Observation :
      Set

    observe :
      Observer →
      DeterministicLatentUniverse.LatentState U →
      Observation

    observationallyEquivalent :
      Observer →
      DeterministicLatentUniverse.LatentState U →
      DeterministicLatentUniverse.LatentState U →
      Set

    sameObservationImpliesEquivalent :
      (observer : Observer) →
      (left right : DeterministicLatentUniverse.LatentState U) →
      observe observer left ≡ observe observer right →
      observationallyEquivalent observer left right

    quotientManyToOne :
      Set

    kernelMeaning :
      String

    observationBoundary :
      String

open ObservationQuotient public

record ApparentRandomnessQuotient
    (U : DeterministicLatentUniverse)
    (Q : ObservationQuotient U) : Set₁ where
  field
    ApparentOutcome :
      Set

    outcomeFromObservation :
      ObservationQuotient.Observation Q →
      ApparentOutcome

    distinctLatentStatesCanShareOutcome :
      ObservationQuotient.quotientManyToOne Q

    apparentRandomnessReading :
      String

    noRandomnessFromOntologyClaim :
      Bool

    noRandomnessFromOntologyClaimIsTrue :
      noRandomnessFromOntologyClaim ≡ true

open ApparentRandomnessQuotient public

record ObserverSlice
    (U : DeterministicLatentUniverse)
    (Q : ObservationQuotient U) : Set where
  field
    observer :
      ObservationQuotient.Observer Q

    sample :
      DeterministicLatentUniverse.LatentState U

    observation :
      ObservationQuotient.Observation Q

    observation-v :
      observation ≡ ObservationQuotient.observe Q observer sample

    role :
      ObservationRole

    sliceBoundary :
      String

open ObserverSlice public

record QuotientFusion
    (U : DeterministicLatentUniverse)
    (Q : ObservationQuotient U) : Set₁ where
  field
    FusedQuotient :
      Set

    Residual :
      Set

    Admissibility :
      Set

    fuse :
      List (ObserverSlice U Q) →
      FusedQuotient

    residual :
      List (ObserverSlice U Q) →
      FusedQuotient →
      Residual

    admissibility :
      Residual →
      Admissibility

    residualAccepted :
      Residual →
      Set

    admissibilityAccepted :
      Admissibility →
      Set

    fusionNarrowsQuotient :
      String

    fusedQuotientStillManyToOne :
      Bool

    fusedQuotientStillManyToOneIsTrue :
      fusedQuotientStillManyToOne ≡ true

open QuotientFusion public

record PeerReviewAsQuotientFusion
    (U : DeterministicLatentUniverse)
    (Q : ObservationQuotient U)
    (F : QuotientFusion U Q) : Set₁ where
  field
    ReviewTrace :
      Set

    reviewTrace :
      List (ObserverSlice U Q) →
      QuotientFusion.FusedQuotient F →
      QuotientFusion.Residual F →
      QuotientFusion.Admissibility F →
      ReviewTrace

    reviewersAreObservers :
      List (ObservationQuotient.Observer Q)

    reviewIsFusionPlusChecks :
      String

    peerReviewInfallible :
      Bool

    peerReviewInfallibleIsFalse :
      peerReviewInfallible ≡ false

    scienceTruthClosed :
      Bool

    scienceTruthClosedIsFalse :
      scienceTruthClosed ≡ false

open PeerReviewAsQuotientFusion public

record MultiObserverScienceBoundary : Set where
  field
    status :
      String

    pipeline :
      List String

    guards :
      List ScienceQuotientGuard

    exactFirstMissing :
      List ScienceFirstMissing

    universalDeterminismProof :
      Bool

    universalDeterminismProofIsFalse :
      universalDeterminismProof ≡ false

    hiddenVariableProof :
      Bool

    hiddenVariableProofIsFalse :
      hiddenVariableProof ≡ false

    scienceTruthClosure :
      Bool

    scienceTruthClosureIsFalse :
      scienceTruthClosure ≡ false

    peerReviewInfallibility :
      Bool

    peerReviewInfallibilityIsFalse :
      peerReviewInfallibility ≡ false

    fullLatentStateRecovery :
      Bool

    fullLatentStateRecoveryIsFalse :
      fullLatentStateRecovery ≡ false

    observerNeutralCompleteSlice :
      Bool

    observerNeutralCompleteSliceIsFalse :
      observerNeutralCompleteSlice ≡ false

    allowedClaim :
      List String

    forbiddenClaim :
      List String

open MultiObserverScienceBoundary public

canonicalMultiObserverScienceBoundary :
  MultiObserverScienceBoundary
canonicalMultiObserverScienceBoundary =
  record
    { status =
        "multi-observer science quotient surface only; non-promoting"
    ; pipeline =
        "deterministic latent carrier, when supplied"
        ∷ "many-to-one observer-dependent observation quotient"
        ∷ "apparent randomness as quotient-level outcome ambiguity"
        ∷ "observer slices fused into a joint quotient"
        ∷ "residual and admissibility checks gate review claims"
        ∷ "no latent recovery, truth closure, or peer-review infallibility"
        ∷ []
    ; guards =
        canonicalScienceQuotientGuards
    ; exactFirstMissing =
        missingLatentDynamicsReceipt
        ∷ missingObservationKernelReceipt
        ∷ missingManyToOneWitness
        ∷ missingObserverCalibrationReceipt
        ∷ missingFusionResidualMetric
        ∷ missingAdmissibilityPolicy
        ∷ missingIndependentReviewTrace
        ∷ missingExternalReplicationReceipt
        ∷ []
    ; universalDeterminismProof =
        false
    ; universalDeterminismProofIsFalse =
        refl
    ; hiddenVariableProof =
        false
    ; hiddenVariableProofIsFalse =
        refl
    ; scienceTruthClosure =
        false
    ; scienceTruthClosureIsFalse =
        refl
    ; peerReviewInfallibility =
        false
    ; peerReviewInfallibilityIsFalse =
        refl
    ; fullLatentStateRecovery =
        false
    ; fullLatentStateRecoveryIsFalse =
        refl
    ; observerNeutralCompleteSlice =
        false
    ; observerNeutralCompleteSliceIsFalse =
        refl
    ; allowedClaim =
        "a supplied deterministic latent carrier may be observed through many-to-one quotient maps"
        ∷ "apparent randomness can be represented as ambiguity induced by the observation quotient"
        ∷ "multi-observer science can be modeled as quotient fusion checked by residual and admissibility gates"
        ∷ []
    ; forbiddenClaim =
        "this module proves no universal determinism"
        ∷ "this module proves no hidden-variable ontology"
        ∷ "science is not closed truth by construction"
        ∷ "peer review is not infallible"
        ∷ "fused observations do not recover the full latent state"
        ∷ "no observer owns an observer-neutral complete slice"
        ∷ []
    }

------------------------------------------------------------------------
-- Canonical proof-light toy inhabitants.

data ToyTime : Set where
  toyT0 :
    ToyTime

  toyT1 :
    ToyTime

data ToyLatent : Set where
  latentA0 :
    ToyLatent

  latentA1 :
    ToyLatent

  latentB :
    ToyLatent

data ToyObserver : Set where
  observerAlpha :
    ToyObserver

  observerBeta :
    ToyObserver

  reviewerGamma :
    ToyObserver

data ToyObservation : Set where
  observedA :
    ToyObservation

  observedB :
    ToyObservation

data ToyFusedQuotient : Set where
  fusedA :
    ToyFusedQuotient

  fusedB :
    ToyFusedQuotient

data ToyResidual : Set where
  residualZero :
    ToyResidual

  residualOpen :
    ToyResidual

data ToyAdmissibility : Set where
  admissible :
    ToyAdmissibility

  needsMoreReceipt :
    ToyAdmissibility

data ToyReviewTrace : Set where
  toyReviewTrace :
    ToyReviewTrace

toyNext :
  ToyLatent →
  ToyLatent
toyNext latentA0 =
  latentA1
toyNext latentA1 =
  latentB
toyNext latentB =
  latentA0

toyStateAt :
  ToyTime →
  ToyLatent
toyStateAt toyT0 =
  latentA0
toyStateAt toyT1 =
  latentA1

canonicalToyLatentUniverse :
  DeterministicLatentUniverse
canonicalToyLatentUniverse =
  record
    { Time =
        ToyTime
    ; LatentState =
        ToyLatent
    ; next =
        toyNext
    ; stateAt =
        toyStateAt
    ; deterministicStepReceipt =
        λ _ → refl
    ; carrierMeaning =
        "finite deterministic toy carrier with three latent states"
    ; determinismBoundary =
        "toy determinism is local structure, not a universal determinism proof"
    }

toyObserve :
  ToyObserver →
  ToyLatent →
  ToyObservation
toyObserve observerAlpha latentA0 =
  observedA
toyObserve observerAlpha latentA1 =
  observedA
toyObserve observerAlpha latentB =
  observedB
toyObserve observerBeta latentA0 =
  observedA
toyObserve observerBeta latentA1 =
  observedB
toyObserve observerBeta latentB =
  observedB
toyObserve reviewerGamma latentA0 =
  observedA
toyObserve reviewerGamma latentA1 =
  observedA
toyObserve reviewerGamma latentB =
  observedB

toyEquivalent :
  ToyObserver →
  ToyLatent →
  ToyLatent →
  Set
toyEquivalent observer left right =
  toyObserve observer left ≡ toyObserve observer right

toySameObservationImpliesEquivalent :
  (observer : ToyObserver) →
  (left right : ToyLatent) →
  toyObserve observer left ≡ toyObserve observer right →
  toyEquivalent observer left right
toySameObservationImpliesEquivalent _ _ _ same =
  same

record ToyManyToOneWitness : Set where
  field
    observer :
      ToyObserver

    left :
      ToyLatent

    right :
      ToyLatent

    sameObservation :
      toyObserve observer left ≡ toyObserve observer right

    distinctLatent :
      left ≡ right →
      ⊥

open ToyManyToOneWitness public

latentA0NotLatentA1 :
  latentA0 ≡ latentA1 →
  ⊥
latentA0NotLatentA1 ()

canonicalToyManyToOneWitness :
  ToyManyToOneWitness
canonicalToyManyToOneWitness =
  record
    { observer =
        observerAlpha
    ; left =
        latentA0
    ; right =
        latentA1
    ; sameObservation =
        refl
    ; distinctLatent =
        latentA0NotLatentA1
    }

canonicalToyObservationQuotient :
  ObservationQuotient canonicalToyLatentUniverse
canonicalToyObservationQuotient =
  record
    { Observer =
        ToyObserver
    ; Observation =
        ToyObservation
    ; observe =
        toyObserve
    ; observationallyEquivalent =
        toyEquivalent
    ; sameObservationImpliesEquivalent =
        toySameObservationImpliesEquivalent
    ; quotientManyToOne =
        ToyManyToOneWitness
    ; kernelMeaning =
        "observerAlpha identifies latentA0 and latentA1 at observedA"
    ; observationBoundary =
        "the quotient exposes observation classes, not latent identity"
    }

canonicalToyApparentRandomness :
  ApparentRandomnessQuotient
    canonicalToyLatentUniverse
    canonicalToyObservationQuotient
canonicalToyApparentRandomness =
  record
    { ApparentOutcome =
        ToyObservation
    ; outcomeFromObservation =
        λ observation → observation
    ; distinctLatentStatesCanShareOutcome =
        canonicalToyManyToOneWitness
    ; apparentRandomnessReading =
        "observedA has multiple latent preimages for observerAlpha, so the observation surface is ambiguous"
    ; noRandomnessFromOntologyClaim =
        true
    ; noRandomnessFromOntologyClaimIsTrue =
        refl
    }

toySliceAlpha :
  ObserverSlice
    canonicalToyLatentUniverse
    canonicalToyObservationQuotient
toySliceAlpha =
  record
    { observer =
        observerAlpha
    ; sample =
        latentA0
    ; observation =
        observedA
    ; observation-v =
        refl
    ; role =
        instrumentRole
    ; sliceBoundary =
        "alpha slice is a quotient observation, not full latent recovery"
    }

toySliceBeta :
  ObserverSlice
    canonicalToyLatentUniverse
    canonicalToyObservationQuotient
toySliceBeta =
  record
    { observer =
        observerBeta
    ; sample =
        latentA0
    ; observation =
        observedA
    ; observation-v =
        refl
    ; role =
        humanObserverRole
    ; sliceBoundary =
        "beta slice contributes a second quotient, not observer-neutral completion"
    }

toySlices :
  List
    (ObserverSlice
      canonicalToyLatentUniverse
      canonicalToyObservationQuotient)
toySlices =
  toySliceAlpha ∷ toySliceBeta ∷ []

toyFuse :
  List
    (ObserverSlice
      canonicalToyLatentUniverse
      canonicalToyObservationQuotient) →
  ToyFusedQuotient
toyFuse [] =
  fusedB
toyFuse (_ ∷ _) =
  fusedA

toyResidual :
  List
    (ObserverSlice
      canonicalToyLatentUniverse
      canonicalToyObservationQuotient) →
  ToyFusedQuotient →
  ToyResidual
toyResidual [] _ =
  residualOpen
toyResidual (_ ∷ _) fusedA =
  residualZero
toyResidual (_ ∷ _) fusedB =
  residualOpen

toyAdmissibility :
  ToyResidual →
  ToyAdmissibility
toyAdmissibility residualZero =
  admissible
toyAdmissibility residualOpen =
  needsMoreReceipt

toyResidualAccepted :
  ToyResidual →
  Set
toyResidualAccepted residualZero =
  ⊤
toyResidualAccepted residualOpen =
  ⊥

toyAdmissibilityAccepted :
  ToyAdmissibility →
  Set
toyAdmissibilityAccepted admissible =
  ⊤
toyAdmissibilityAccepted needsMoreReceipt =
  ⊥

canonicalToyQuotientFusion :
  QuotientFusion
    canonicalToyLatentUniverse
    canonicalToyObservationQuotient
canonicalToyQuotientFusion =
  record
    { FusedQuotient =
        ToyFusedQuotient
    ; Residual =
        ToyResidual
    ; Admissibility =
        ToyAdmissibility
    ; fuse =
        toyFuse
    ; residual =
        toyResidual
    ; admissibility =
        toyAdmissibility
    ; residualAccepted =
        toyResidualAccepted
    ; admissibilityAccepted =
        toyAdmissibilityAccepted
    ; fusionNarrowsQuotient =
        "toy fusion combines alpha and beta slices, then checks the residual before admissibility"
    ; fusedQuotientStillManyToOne =
        true
    ; fusedQuotientStillManyToOneIsTrue =
        refl
    }

toyFused :
  ToyFusedQuotient
toyFused =
  toyFuse toySlices

toyFusedResidual :
  ToyResidual
toyFusedResidual =
  toyResidual toySlices toyFused

toyFusedAdmissibility :
  ToyAdmissibility
toyFusedAdmissibility =
  toyAdmissibility toyFusedResidual

toyFusedResidualAccepted :
  toyResidualAccepted toyFusedResidual
toyFusedResidualAccepted =
  tt

toyFusedAdmissibilityAccepted :
  toyAdmissibilityAccepted toyFusedAdmissibility
toyFusedAdmissibilityAccepted =
  tt

canonicalToyPeerReviewAsQuotientFusion :
  PeerReviewAsQuotientFusion
    canonicalToyLatentUniverse
    canonicalToyObservationQuotient
    canonicalToyQuotientFusion
canonicalToyPeerReviewAsQuotientFusion =
  record
    { ReviewTrace =
        ToyReviewTrace
    ; reviewTrace =
        λ _ _ _ _ → toyReviewTrace
    ; reviewersAreObservers =
        reviewerGamma ∷ []
    ; reviewIsFusionPlusChecks =
        "peer review is represented as reviewer-observer participation plus quotient fusion, residual acceptance, and admissibility acceptance"
    ; peerReviewInfallible =
        false
    ; peerReviewInfallibleIsFalse =
        refl
    ; scienceTruthClosed =
        false
    ; scienceTruthClosedIsFalse =
        refl
    }
