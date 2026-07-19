module DASHI.Biology.Levin.ProblemSpaceAgency where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Behaviour is navigation in a typed problem space, not necessarily motion
-- through ordinary three-dimensional space.

data ProblemSpaceKind : Set where
  physical3D : ProblemSpaceKind
  anatomical : ProblemSpaceKind
  physiological : ProblemSpaceKind
  transcriptional : ProblemSpaceKind
  social : ProblemSpaceKind
  abstract : ProblemSpaceKind

canonicalProblemSpaces : List ProblemSpaceKind
canonicalProblemSpaces =
  physical3D ∷ anatomical ∷ physiological ∷ transcriptional ∷ social ∷ abstract ∷ []

record ProblemSpaceNavigation : Set where
  field
    kind : ProblemSpaceKind
    stateObservable : Bool
    admissibleMovesSpecified : Bool
    targetRegionSpecified : Bool
    errorSignalSpecified : Bool
    correctivePolicyWitnessed : Bool
    noStrictStepwiseDescentRequirement : Bool

open ProblemSpaceNavigation public

record ProblemSpaceAgencyBoundary : Set where
  field
    canonicalSpaces : List ProblemSpaceKind
    non3DEmbodimentAllowed : Bool
    embodimentStillTyped : Bool
    navigationNotGlobalOptimization : Bool
    activeInferenceNotAssumed : Bool
    intelligenceNotConsciousness : Bool
    candidateOnly : Bool
    reading : String

open ProblemSpaceAgencyBoundary public

canonicalProblemSpaceAgencyBoundary : ProblemSpaceAgencyBoundary
canonicalProblemSpaceAgencyBoundary = record
  { canonicalSpaces = canonicalProblemSpaces
  ; non3DEmbodimentAllowed = true
  ; embodimentStillTyped = true
  ; navigationNotGlobalOptimization = false
  ; activeInferenceNotAssumed = false
  ; intelligenceNotConsciousness = false
  ; candidateOnly = true
  ; reading =
      "A system may exhibit goal-directed navigation in anatomical, physiological, transcriptional, social, abstract, or physical space; the space, observables, moves, target, and evidence must be supplied explicitly"
  }

canonicalNavigationNotGlobalOptimization :
  navigationNotGlobalOptimization canonicalProblemSpaceAgencyBoundary ≡ false
canonicalNavigationNotGlobalOptimization = refl
