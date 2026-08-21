module DASHI.Cognition.PNF.ActiveInferenceFibreBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.DecisionPotentialFibreExact as Potential

------------------------------------------------------------------------
-- Literature calibration:
-- Karl Friston, "The free-energy principle: a unified brain theory?"
-- Nature Reviews Neuroscience 11 (2010), DOI 10.1038/nrn2787.
--
-- DASHI imports the useful mathematical idea -- a variational/policy
-- potential with distinct epistemic and pragmatic contributions -- while
-- explicitly rejecting the promotion "one free-energy functional
-- definitionally equals semantics + access + audit + decision + action +
-- justice".  The finite Nat-valued decomposition below is an exact structural
-- toy, not a claim to implement KL-divergence or the full active-inference
-- calculus.
------------------------------------------------------------------------

data Policy : Set where
  remain withdraw : Policy

data PolicyObserver : Set where
  person institution : PolicyObserver

-- Distinct policy-pressure components.  Keeping them separate matters: equal
-- total pressure need not mean equal epistemic/pragmatic structure.
epistemicPressure : PolicyObserver → Policy → Nat
epistemicPressure person remain = 0
epistemicPressure person withdraw = 1
epistemicPressure institution remain = 1
epistemicPressure institution withdraw = 0

pragmaticPressure : PolicyObserver → Policy → Nat
pragmaticPressure person remain = 0
pragmaticPressure person withdraw = 2
pragmaticPressure institution remain = 2
pragmaticPressure institution withdraw = 0

expectedPotential : PolicyObserver → Policy → Nat
expectedPotential observer policy =
  epistemicPressure observer policy + pragmaticPressure observer policy

expectedPotentialDecomposes :
  (observer : PolicyObserver) →
  (policy : Policy) →
  expectedPotential observer policy
  ≡ epistemicPressure observer policy + pragmaticPressure observer policy
expectedPotentialDecomposes observer policy = refl

minimumPolicy : PolicyObserver → Policy
minimumPolicy person = remain
minimumPolicy institution = withdraw

samePolicyPotentialNeedNotBeShared :
  expectedPotential person remain ≡ expectedPotential institution remain → ⊥
samePolicyPotentialNeedNotBeShared ()

observerIndexedMinimaDiffer :
  minimumPolicy person ≡ minimumPolicy institution → ⊥
observerIndexedMinimaDiffer ()

componentStructureCanDifferAtSameTotal :
  epistemicPressure person withdraw ≡ 1
  × pragmaticPressure person withdraw ≡ 2
  × expectedPotential person withdraw ≡ 3
componentStructureCanDifferAtSameTotal = refl , (refl , refl)

------------------------------------------------------------------------
-- A potential can supply directional pressure inside a fibre without owning
-- the fibre's semantic equality or formal admissibility.
------------------------------------------------------------------------

record FibrePotentialInterface : Set where
  constructor fibrePotentialInterface
  field
    contextPotential : Potential.Context → Potential.FineState → Nat
    accessSurface : Potential.Context → Potential.FineState → Bool
    potentialIsSemanticIdentity : Bool
    potentialIsFormalValidity : Bool
    potentialIsAuthority : Bool
    potentialIsJustice : Bool

canonicalFibrePotentialInterface : FibrePotentialInterface
canonicalFibrePotentialInterface = fibrePotentialInterface
  Potential.slowPotential
  Potential.accessible
  false false false false

sameSemanticFibreCanSupportDifferentPotential :
  Potential.project Potential.threatState
  ≡ Potential.project Potential.safetyState
  × Potential.slowPotential Potential.ordinaryContext Potential.threatState ≡ 2
  × Potential.slowPotential Potential.ordinaryContext Potential.safetyState ≡ 0
sameSemanticFibreCanSupportDifferentPotential = Potential.sameFibreDifferentPotential

------------------------------------------------------------------------
-- Collapse countermodel: no single observer-independent "best policy" can be
-- definitionally equal to both indexed minima in this finite witness.
------------------------------------------------------------------------

noUniversalMinimumFromTwoObservers :
  (p : Policy) →
  p ≡ minimumPolicy person →
  p ≡ minimumPolicy institution →
  ⊥
noUniversalMinimumFromTwoObservers remain refl ()
noUniversalMinimumFromTwoObservers withdraw () _

record ActiveInferenceComparisonBoundary : Set where
  constructor activeInferenceComparisonBoundary
  field
    freeEnergyPotentialSupported : Bool
    expectedPotentialPolicyScoringSupported : Bool
    epistemicPragmaticDecompositionSupported : Bool
    fullKLVariationalCalculusImplementedHere : Bool
    oneFunctionalDefinesAllPNFLayers : Bool
    oneObserverPotentialIsUniversal : Bool

canonicalActiveInferenceComparisonBoundary : ActiveInferenceComparisonBoundary
canonicalActiveInferenceComparisonBoundary =
  activeInferenceComparisonBoundary true true true false false false
