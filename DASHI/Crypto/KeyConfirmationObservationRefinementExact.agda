module DASHI.Crypto.KeyConfirmationObservationRefinementExact where

------------------------------------------------------------------------
-- KEY CONFIRMATION AS A CONDITIONAL OBSERVATION SURFACE
--
-- Primary reference:
-- Gorjan Alagic, Elaine Barker, Lily Chen, Dustin Moody, Angela Robinson,
-- Hamilton Silberg, Noah Waller,
-- "Recommendations for Key-Encapsulation Mechanisms", NIST SP 800-227,
-- 2025. DOI: 10.6028/NIST.SP.800-227.
--
-- Key confirmation is not itself a weakness.  The blue-team question is
-- narrower: if a confirmation/accept-reject result is externally visible, does
-- it distinguish hidden states that had the same prior public projection?
-- This module makes that split witness exact and supplies a finite regression.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Crypto.BlueTeamAdversaryObservationExact as Observation
import DASHI.Crypto.FiniteCandidateFibreCardinalityExact as Fibre

record ConfirmationObservationSystem : Set₁ where
  constructor confirmationObservationSystem
  field
    Hidden Public PresentedTag : Set
    project : Hidden → Public
    confirmationOutcome : Hidden → PresentedTag → Bool

open ConfirmationObservationSystem public

asAdversarySystem : ConfirmationObservationSystem → Observation.BlueTeamAdversarySystem
asAdversarySystem system =
  Observation.blueTeamAdversarySystem
    (Hidden system)
    (Public system)
    (PresentedTag system)
    Bool
    (project system)
    (confirmationOutcome system)

record ConfirmationSplitWitness
    (system : ConfirmationObservationSystem) : Set where
  constructor confirmationSplitWitness
  field
    left right : Hidden system
    samePublic : project system left ≡ project system right
    presentedTag : PresentedTag system
    outcomesDiffer :
      confirmationOutcome system left presentedTag
      ≡ confirmationOutcome system right presentedTag → ⊥

open ConfirmationSplitWitness public

confirmationSplitGivesHiddenDependentObservation :
  ∀ {system : ConfirmationObservationSystem} →
  ConfirmationSplitWitness system →
  Observation.HiddenDependentSplit (asAdversarySystem system)
confirmationSplitGivesHiddenDependentObservation split =
  Observation.hiddenDependentSplit
    (left split)
    (right split)
    (samePublic split)
    (presentedTag split)
    (outcomesDiffer split)

------------------------------------------------------------------------
-- Finite exact harness.
--
-- Two candidate hidden keys share the same public surface.  A visible Boolean
-- confirmation outcome for presented tag false distinguishes them and shrinks
-- the finite candidate mask 2 -> 1.  This demonstrates the theorem shape only;
-- it is not a claim about a conforming ML-KEM deployment.
------------------------------------------------------------------------

boolEq : Bool → Bool → Bool
boolEq false false = true
boolEq false true = false
boolEq true false = false
boolEq true true = true

boolConfirmationSystem : ConfirmationObservationSystem
boolConfirmationSystem =
  confirmationObservationSystem
    Bool
    ⊤
    Bool
    (λ hidden → tt)
    boolEq

boolConfirmationSplit : ConfirmationSplitWitness boolConfirmationSystem
boolConfirmationSplit =
  confirmationSplitWitness false true refl false different
  where
  different : true ≡ false → ⊥
  different ()

boolConfirmationHiddenDependent :
  Observation.HiddenDependentSplit (asAdversarySystem boolConfirmationSystem)
boolConfirmationHiddenDependent =
  confirmationSplitGivesHiddenDependentObservation boolConfirmationSplit

beforeConfirmationMask : List Bool
beforeConfirmationMask = true ∷ true ∷ []

afterConfirmationMask : List Bool
afterConfirmationMask = true ∷ false ∷ []

confirmationMaskRefines : Fibre.Refines beforeConfirmationMask afterConfirmationMask
confirmationMaskRefines = Fibre.keepLive (Fibre.dropLive Fibre.empty)

beforeConfirmationCount : Fibre.liveCount beforeConfirmationMask ≡ 2
beforeConfirmationCount = refl

afterConfirmationCount : Fibre.liveCount afterConfirmationMask ≡ 1
afterConfirmationCount = refl

------------------------------------------------------------------------
-- Boundary: a protocol must expose the outcome for this refinement to belong
-- to the adversary observation surface.  The existence of key confirmation as
-- a protocol feature alone is not a split theorem.
------------------------------------------------------------------------

record ConfirmationBoundary : Set where
  constructor confirmationBoundary
  field
    confirmationExistenceMeansLeakage : Bool
    confirmationExistenceMeansLeakageIsFalse :
      confirmationExistenceMeansLeakage ≡ false
    externallyVisibleSplitRequiresWitness : Bool
    externallyVisibleSplitRequiresWitnessIsTrue :
      externallyVisibleSplitRequiresWitness ≡ true

open ConfirmationBoundary public

canonicalConfirmationBoundary : ConfirmationBoundary
canonicalConfirmationBoundary =
  confirmationBoundary false refl true refl
