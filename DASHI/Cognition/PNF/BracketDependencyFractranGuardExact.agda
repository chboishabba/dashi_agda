module DASHI.Cognition.PNF.BracketDependencyFractranGuardExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact as World

------------------------------------------------------------------------
-- A -> B bracket dependency becomes an executable prime guard: B's lane is
-- produced/entered only through a fraction whose denominator requires A's lane.
-- This is a machine-level prerequisite encoding, not semantic authority.
------------------------------------------------------------------------

compileDependencyGuard : World.BracketDependency → Context.FractranFraction
compileDependencyGuard dependency =
  Context.fractranFraction
    (World.dependentPrime dependency ∷ [])
    (World.prerequisitePrime dependency ∷ [])

compiledGuardRequiresPrerequisite :
  (dependency : World.BracketDependency) →
  Context.denominatorLanes (compileDependencyGuard dependency)
  ≡ World.prerequisitePrime dependency ∷ []
compiledGuardRequiresPrerequisite dependency = refl

compiledGuardProducesDependent :
  (dependency : World.BracketDependency) →
  Context.numeratorLanes (compileDependencyGuard dependency)
  ≡ World.dependentPrime dependency ∷ []
compiledGuardProducesDependent dependency = refl

reciprocalGuardReversesPrimeDirection :
  (dependency : World.BracketDependency) →
  Context.numeratorLanes
    (Context.reciprocal (compileDependencyGuard dependency))
  ≡ World.prerequisitePrime dependency ∷ []
reciprocalGuardReversesPrimeDirection dependency = refl

record BracketGuardBoundary : Set where
  constructor bracketGuardBoundary
  field
    dependencyCanCompileToDivisibilityGuard : Bool
    denominatorRequirementIsSemanticAuthority : Bool
    reciprocalGuardAutomaticallyLawfulSemanticInverse : Bool

canonicalBracketGuardBoundary : BracketGuardBoundary
canonicalBracketGuardBoundary = bracketGuardBoundary true false false
