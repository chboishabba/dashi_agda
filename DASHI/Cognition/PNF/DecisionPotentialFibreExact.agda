module DASHI.Cognition.PNF.DecisionPotentialFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- A potential lives ON a fine fibre.  It is not the semantic identity of the
-- fibre and is indexed by context/observer.  This is the DASHI boundary for
-- importing free-energy / attractor ideas without collapsing PNF semantics
-- into one scalar functional.
------------------------------------------------------------------------

data FineState : Set where
  threatState safetyState saddleState : FineState

data CoarseObservation : Set where
  retainedMemory : CoarseObservation
  transitionState : CoarseObservation

data Context : Set where
  ordinaryContext threatContext : Context

data PotentialObserver : Set where
  subjectObserver institutionObserver : PotentialObserver

project : FineState → CoarseObservation
project threatState = retainedMemory
project safetyState = retainedMemory
project saddleState = transitionState

sameMemoryFibre : project threatState ≡ project safetyState
sameMemoryFibre = refl

slowPotential : Context → FineState → Nat
slowPotential ordinaryContext threatState = 2
slowPotential ordinaryContext safetyState = 0
slowPotential ordinaryContext saddleState = 3
slowPotential threatContext threatState = 0
slowPotential threatContext safetyState = 2
slowPotential threatContext saddleState = 3

accessible : Context → FineState → Bool
accessible ordinaryContext threatState = true
accessible ordinaryContext safetyState = true
accessible ordinaryContext saddleState = false
accessible threatContext threatState = true
accessible threatContext safetyState = false
accessible threatContext saddleState = false

sameFibreDifferentPotential :
  project threatState ≡ project safetyState
  × slowPotential ordinaryContext threatState ≡ 2
  × slowPotential ordinaryContext safetyState ≡ 0
sameFibreDifferentPotential = refl , (refl , refl)

lowerPotentialNeedNotBeAccessible :
  slowPotential threatContext safetyState ≡ 2
  × slowPotential threatContext threatState ≡ 0
  × accessible threatContext safetyState ≡ false
  × accessible threatContext threatState ≡ true
lowerPotentialNeedNotBeAccessible = refl , (refl , (refl , refl))

contextCanReversePotentialOrdering :
  slowPotential ordinaryContext threatState ≡ 2
  × slowPotential ordinaryContext safetyState ≡ 0
  × slowPotential threatContext threatState ≡ 0
  × slowPotential threatContext safetyState ≡ 2
contextCanReversePotentialOrdering = refl , (refl , (refl , refl))

------------------------------------------------------------------------
-- Explicit finite barrier geometry.  A globally lower endpoint may remain
-- separated from the current basin by a positive barrier.
------------------------------------------------------------------------

barrierHeight : FineState → FineState → Nat
barrierHeight threatState safetyState = 3
barrierHeight safetyState threatState = 3
barrierHeight _ _ = 0

lowerEndpointCanHavePositiveBarrier :
  slowPotential ordinaryContext safetyState ≡ 0
  × slowPotential ordinaryContext threatState ≡ 2
  × barrierHeight threatState safetyState ≡ 3
lowerEndpointCanHavePositiveBarrier = refl , (refl , refl)

------------------------------------------------------------------------
-- Observer-indexed potential.  Stability for one consumer is not a global
-- optimum.  This mirrors the anti-host / situated-justice discipline.
------------------------------------------------------------------------

data SocialState : Set where
  quietSuppressed quietJust : SocialState

observerPotential : PotentialObserver → SocialState → Nat
observerPotential institutionObserver quietSuppressed = 0
observerPotential institutionObserver quietJust = 2
observerPotential subjectObserver quietSuppressed = 3
observerPotential subjectObserver quietJust = 0

preferred : PotentialObserver → SocialState
preferred institutionObserver = quietSuppressed
preferred subjectObserver = quietJust

observerMinimaNeedNotCoincide :
  preferred institutionObserver ≡ preferred subjectObserver → ⊥
observerMinimaNeedNotCoincide ()

------------------------------------------------------------------------
-- Balanced signed pressure is not the same object as low tension.  The
-- orientation quotient may cancel signed displacement while a squared/energy
-- style residual remains.  This is the decision-facing analogue of the
-- reflection-orbit defect discipline, not an identification with zeta.
------------------------------------------------------------------------

data SignedPressure : Set where
  positive negative neutral : SignedPressure

signedSumCancels : SignedPressure → SignedPressure → Bool
signedSumCancels positive negative = true
signedSumCancels negative positive = true
signedSumCancels neutral neutral = true
signedSumCancels _ _ = false

tensionMass : SignedPressure → SignedPressure → Nat
tensionMass positive negative = 2
tensionMass negative positive = 2
tensionMass neutral neutral = 0
tensionMass _ _ = 1

balancedConflictNotNeutral :
  signedSumCancels positive negative ≡ true
  × signedSumCancels neutral neutral ≡ true
  × tensionMass positive negative ≡ 2
  × tensionMass neutral neutral ≡ 0
balancedConflictNotNeutral = refl , (refl , (refl , refl))

record DecisionPotentialBoundary : Set where
  constructor decisionPotentialBoundary
  field
    potentialDefinesSemanticIdentity : Bool
    potentialDefinesFormalValidity : Bool
    potentialDefinesAuthority : Bool
    lowerPotentialImpliesAccessibility : Bool
    oneObserverPotentialIsUniversal : Bool

canonicalDecisionPotentialBoundary : DecisionPotentialBoundary
canonicalDecisionPotentialBoundary =
  decisionPotentialBoundary false false false false false
