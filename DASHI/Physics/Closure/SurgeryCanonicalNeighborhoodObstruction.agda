module DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObstruction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.ShellNeighborhoodClass
  using
    ( ShellNeighborhoodClass
    ; definiteShellNeighborhood
    ; oneMinusShellNeighborhood
    ; mixed21ShellNeighborhood
    ; split22ShellNeighborhood
    ; unknownShellNeighborhood
    ; classifyShell1Neighborhood
    )

------------------------------------------------------------------------
-- Canonical-neighborhood and surgery boundary.
--
-- This module deliberately records only a discrete taxonomy connected to the
-- existing shell-neighbourhood classifier.  It does not construct smooth
-- Ricci-flow canonical neighbourhoods, caps, neck continuation, or surgery.

data ⊥ : Set where

NotTrue : Bool → Set
NotTrue b =
  b ≡ true → ⊥

falseNotTrue : NotTrue false
falseNotTrue ()

data SmoothCanonicalNeighborhoodKind : Set where
  smoothEpsilonNeck :
    SmoothCanonicalNeighborhoodKind

  smoothCap :
    SmoothCanonicalNeighborhoodKind

  smoothCompactPositive :
    SmoothCanonicalNeighborhoodKind

data SmoothCanonicalNeighborhoodAvailability : Set where
  smoothCanonicalNeighborhoodUnavailable :
    SmoothCanonicalNeighborhoodKind →
    List String →
    SmoothCanonicalNeighborhoodAvailability

smoothCanonicalNeighborhoodAvailability :
  SmoothCanonicalNeighborhoodKind →
  SmoothCanonicalNeighborhoodAvailability
smoothCanonicalNeighborhoodAvailability smoothEpsilonNeck =
  smoothCanonicalNeighborhoodUnavailable
    smoothEpsilonNeck
    ( "No smooth epsilon-neck chart, C^k control, or S2 cross-section is constructed by the shell classifier"
      ∷ "The shell classifier supplies a finite discrete label only"
      ∷ [] )
smoothCanonicalNeighborhoodAvailability smoothCap =
  smoothCanonicalNeighborhoodUnavailable
    smoothCap
    ( "No smooth cap model, curvature positivity estimate, or cap gluing map is constructed here"
      ∷ "Cap language is only an obstruction target for future analytic evidence"
      ∷ [] )
smoothCanonicalNeighborhoodAvailability smoothCompactPositive =
  smoothCanonicalNeighborhoodUnavailable
    smoothCompactPositive
    ( "No compact positive-curvature canonical-neighborhood theorem is proved here"
      ∷ "The discrete definite shell label is not a smooth compact positive component"
      ∷ [] )

data DiscreteNeighborhoodCandidate : Set where
  discreteCompactPositiveCandidate :
    DiscreteNeighborhoodCandidate

  discreteEpsilonNeckCandidate :
    DiscreteNeighborhoodCandidate

  discreteCapCandidate :
    DiscreteNeighborhoodCandidate

  discreteSplitCandidate :
    DiscreteNeighborhoodCandidate

  discreteUnknownCandidate :
    DiscreteNeighborhoodCandidate

candidateSmoothTarget :
  DiscreteNeighborhoodCandidate →
  SmoothCanonicalNeighborhoodKind
candidateSmoothTarget discreteCompactPositiveCandidate =
  smoothCompactPositive
candidateSmoothTarget discreteEpsilonNeckCandidate =
  smoothEpsilonNeck
candidateSmoothTarget discreteCapCandidate =
  smoothCap
candidateSmoothTarget discreteSplitCandidate =
  smoothEpsilonNeck
candidateSmoothTarget discreteUnknownCandidate =
  smoothEpsilonNeck

candidateSmoothAvailability :
  DiscreteNeighborhoodCandidate →
  SmoothCanonicalNeighborhoodAvailability
candidateSmoothAvailability candidate =
  smoothCanonicalNeighborhoodAvailability (candidateSmoothTarget candidate)

candidateFromShellNeighborhoodClass :
  ShellNeighborhoodClass →
  DiscreteNeighborhoodCandidate
candidateFromShellNeighborhoodClass definiteShellNeighborhood =
  discreteCompactPositiveCandidate
candidateFromShellNeighborhoodClass oneMinusShellNeighborhood =
  discreteEpsilonNeckCandidate
candidateFromShellNeighborhoodClass mixed21ShellNeighborhood =
  discreteCapCandidate
candidateFromShellNeighborhoodClass split22ShellNeighborhood =
  discreteSplitCandidate
candidateFromShellNeighborhoodClass unknownShellNeighborhood =
  discreteUnknownCandidate

classifyDiscreteShellNeighborhood :
  List Nat →
  DiscreteNeighborhoodCandidate
classifyDiscreteShellNeighborhood shell =
  candidateFromShellNeighborhoodClass (classifyShell1Neighborhood shell)

data SurgeryObligation : Set where
  requireSmoothEpsilonNeckModel :
    SurgeryObligation

  requireSmoothCapModel :
    SurgeryObligation

  requireCompactPositiveCanonicalNeighborhoodTheorem :
    SurgeryObligation

  requireSurgeryContinuationLaw :
    SurgeryObligation

  retainDiscreteShellOnlyStatus :
    SurgeryObligation

candidateObligations :
  DiscreteNeighborhoodCandidate →
  List SurgeryObligation
candidateObligations discreteCompactPositiveCandidate =
  requireCompactPositiveCanonicalNeighborhoodTheorem
    ∷ requireSurgeryContinuationLaw
    ∷ retainDiscreteShellOnlyStatus
    ∷ []
candidateObligations discreteEpsilonNeckCandidate =
  requireSmoothEpsilonNeckModel
    ∷ requireSurgeryContinuationLaw
    ∷ retainDiscreteShellOnlyStatus
    ∷ []
candidateObligations discreteCapCandidate =
  requireSmoothCapModel
    ∷ requireSurgeryContinuationLaw
    ∷ retainDiscreteShellOnlyStatus
    ∷ []
candidateObligations discreteSplitCandidate =
  requireSmoothEpsilonNeckModel
    ∷ requireSmoothCapModel
    ∷ requireSurgeryContinuationLaw
    ∷ retainDiscreteShellOnlyStatus
    ∷ []
candidateObligations discreteUnknownCandidate =
  retainDiscreteShellOnlyStatus
    ∷ requireSurgeryContinuationLaw
    ∷ []

record SurgeryCanonicalNeighborhoodObstruction : Set where
  field
    sourceShellClass :
      ShellNeighborhoodClass

    discreteCandidate :
      DiscreteNeighborhoodCandidate

    candidateMatchesShellClass :
      discreteCandidate ≡ candidateFromShellNeighborhoodClass sourceShellClass

    smoothTarget :
      SmoothCanonicalNeighborhoodKind

    smoothTargetMatchesCandidate :
      smoothTarget ≡ candidateSmoothTarget discreteCandidate

    smoothCanonicalNeighborhoodAvailable :
      Bool

    smoothCanonicalNeighborhoodAvailableIsFalse :
      smoothCanonicalNeighborhoodAvailable ≡ false

    smoothCanonicalNeighborhoodBlocked :
      NotTrue smoothCanonicalNeighborhoodAvailable

    surgeryContinuationAvailable :
      Bool

    surgeryContinuationAvailableIsFalse :
      surgeryContinuationAvailable ≡ false

    surgeryContinuationBlocked :
      NotTrue surgeryContinuationAvailable

    smoothAvailability :
      SmoothCanonicalNeighborhoodAvailability

    smoothAvailabilityIsCandidateAvailability :
      smoothAvailability ≡ candidateSmoothAvailability discreteCandidate

    obligations :
      List SurgeryObligation

    obligationsMatchCandidate :
      obligations ≡ candidateObligations discreteCandidate

    obstructionBoundary :
      List String

open SurgeryCanonicalNeighborhoodObstruction public

obstructionFromShellClass :
  ShellNeighborhoodClass →
  SurgeryCanonicalNeighborhoodObstruction
obstructionFromShellClass shellClass =
  record
    { sourceShellClass =
        shellClass
    ; discreteCandidate =
        candidateFromShellNeighborhoodClass shellClass
    ; candidateMatchesShellClass =
        refl
    ; smoothTarget =
        candidateSmoothTarget (candidateFromShellNeighborhoodClass shellClass)
    ; smoothTargetMatchesCandidate =
        refl
    ; smoothCanonicalNeighborhoodAvailable =
        false
    ; smoothCanonicalNeighborhoodAvailableIsFalse =
        refl
    ; smoothCanonicalNeighborhoodBlocked =
        falseNotTrue
    ; surgeryContinuationAvailable =
        false
    ; surgeryContinuationAvailableIsFalse =
        refl
    ; surgeryContinuationBlocked =
        falseNotTrue
    ; smoothAvailability =
        candidateSmoothAvailability (candidateFromShellNeighborhoodClass shellClass)
    ; smoothAvailabilityIsCandidateAvailability =
        refl
    ; obligations =
        candidateObligations (candidateFromShellNeighborhoodClass shellClass)
    ; obligationsMatchCandidate =
        refl
    ; obstructionBoundary =
        "ShellNeighborhoodClass is consumed as a finite discrete classifier"
        ∷ "Smooth epsilon-neck, cap, compact-positive, and surgery-continuation witnesses are all unavailable in this module"
        ∷ "Downstream consumers must treat these values as obstruction taxonomy, not smooth surgery"
        ∷ []
    }

obstructionFromShell :
  List Nat →
  SurgeryCanonicalNeighborhoodObstruction
obstructionFromShell shell =
  obstructionFromShellClass (classifyShell1Neighborhood shell)

------------------------------------------------------------------------
-- Concrete examples and refl-checked classifier wiring.

definiteShellCandidateExample :
  classifyDiscreteShellNeighborhood (8 ∷ []) ≡ discreteCompactPositiveCandidate
definiteShellCandidateExample =
  refl

oneMinusShellCandidateExample :
  classifyDiscreteShellNeighborhood (2 ∷ 2 ∷ []) ≡ discreteEpsilonNeckCandidate
oneMinusShellCandidateExample =
  refl

tripleOneMinusShellCandidateExample :
  classifyDiscreteShellNeighborhood (3 ∷ 3 ∷ 2 ∷ []) ≡ discreteEpsilonNeckCandidate
tripleOneMinusShellCandidateExample =
  refl

split22ShellCandidateExample :
  classifyDiscreteShellNeighborhood (16 ∷ 16 ∷ 4 ∷ 4 ∷ []) ≡ discreteSplitCandidate
split22ShellCandidateExample =
  refl

unknownShellCandidateExample :
  classifyDiscreteShellNeighborhood [] ≡ discreteUnknownCandidate
unknownShellCandidateExample =
  refl

mixed21ClassCandidateExample :
  candidateFromShellNeighborhoodClass mixed21ShellNeighborhood ≡ discreteCapCandidate
mixed21ClassCandidateExample =
  refl

oneMinusObstructionExample :
  SurgeryCanonicalNeighborhoodObstruction
oneMinusObstructionExample =
  obstructionFromShell (2 ∷ 2 ∷ [])

oneMinusObstructionSmoothUnavailable :
  smoothCanonicalNeighborhoodAvailable oneMinusObstructionExample ≡ false
oneMinusObstructionSmoothUnavailable =
  refl

oneMinusObstructionSurgeryContinuationUnavailable :
  surgeryContinuationAvailable oneMinusObstructionExample ≡ false
oneMinusObstructionSurgeryContinuationUnavailable =
  refl

oneMinusObstructionCandidate :
  discreteCandidate oneMinusObstructionExample ≡ discreteEpsilonNeckCandidate
oneMinusObstructionCandidate =
  refl

oneMinusObstructionSmoothTarget :
  smoothTarget oneMinusObstructionExample ≡ smoothEpsilonNeck
oneMinusObstructionSmoothTarget =
  refl

definiteObstructionCompactPositiveTarget :
  smoothTarget (obstructionFromShell (8 ∷ [])) ≡ smoothCompactPositive
definiteObstructionCompactPositiveTarget =
  refl

split22ObstructionStillSurgeryBlocked :
  surgeryContinuationAvailable
    (obstructionFromShell (16 ∷ 16 ∷ 4 ∷ 4 ∷ []))
  ≡
  false
split22ObstructionStillSurgeryBlocked =
  refl
