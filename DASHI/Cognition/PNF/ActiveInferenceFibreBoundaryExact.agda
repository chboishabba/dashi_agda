module DASHI.Cognition.PNF.ActiveInferenceFibreBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.DecisionPotentialFibreExact as Potential

------------------------------------------------------------------------
-- Literature calibration:
-- Karl Friston, "The free-energy principle: a unified brain theory?"
-- Nature Reviews Neuroscience 11 (2010), DOI 10.1038/nrn2787.
--
-- DASHI imports the useful mathematical idea -- a potential/function over
-- states/policies -- while explicitly rejecting the promotion
-- "one free-energy functional definitionally equals semantics + access +
-- audit + decision + action + justice".
------------------------------------------------------------------------

data Policy : Set where
  remain withdraw : Policy

data PolicyObserver : Set where
  person institution : PolicyObserver

expectedPotential : PolicyObserver → Policy → Nat
expectedPotential person remain = 0
expectedPotential person withdraw = 3
expectedPotential institution remain = 3
expectedPotential institution withdraw = 0

minimumPolicy : PolicyObserver → Policy
minimumPolicy person = remain
minimumPolicy institution = withdraw

samePolicyPotentialNeedNotBeShared :
  expectedPotential person remain ≡ expectedPotential institution remain → ⊥
samePolicyPotentialNeedNotBeShared ()

observerIndexedMinimaDiffer :
  minimumPolicy person ≡ minimumPolicy institution → ⊥
observerIndexedMinimaDiffer ()

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
    oneFunctionalDefinesAllPNFLayers : Bool
    oneObserverPotentialIsUniversal : Bool

canonicalActiveInferenceComparisonBoundary : ActiveInferenceComparisonBoundary
canonicalActiveInferenceComparisonBoundary =
  activeInferenceComparisonBoundary true true false false
