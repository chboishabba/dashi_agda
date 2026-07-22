module DASHI.Cognition.PhysicalCouplingFactorisation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.CognitiveVacuumClassBoundary as Fixture
import DASHI.Cognition.DashiCognitiveSystem as Cognitive

record PhysicalSemanticFactorisation
    (system : Cognitive.DASHICognitiveSystem) : Set₁ where
  field
    physicalEvolution :
      Cognitive.Control system →
      Cognitive.Hidden system →
      Cognitive.Hidden system

    tokenSemantics :
      Cognitive.Hidden system →
      BT.Trit →
      Cognitive.Hidden system

    transitionFactorises :
      ∀ control hidden token →
      Cognitive.semanticStep system control hidden token
      ≡ tokenSemantics (physicalEvolution control hidden) token

open PhysicalSemanticFactorisation public

record GuardOnlyCoupling
    (system : Cognitive.DASHICognitiveSystem) : Set₁ where
  field
    factorisation : PhysicalSemanticFactorisation system

    physicalEvolutionIsIdentity :
      ∀ control hidden →
      physicalEvolution factorisation control hidden ≡ hidden

    tokenSemanticsMatchesTransition :
      ∀ control hidden token →
      tokenSemantics factorisation hidden token
      ≡ Cognitive.semanticStep system control hidden token

open GuardOnlyCoupling public

record StateAffectingCoupling
    (system : Cognitive.DASHICognitiveSystem) : Set₁ where
  field
    factorisation : PhysicalSemanticFactorisation system
    controlSample : Cognitive.Control system
    hiddenSample : Cognitive.Hidden system
    coupledSample : Cognitive.Hidden system

    sampleEvolution :
      physicalEvolution factorisation controlSample hiddenSample
      ≡ coupledSample

open StateAffectingCoupling public

record StackCouplingFactorisation
    (system : Cognitive.DASHICognitiveSystem) : Set₁ where
  field
    physicalStackUpdate :
      Cognitive.Control system →
      List (Cognitive.StackSymbol system) →
      List (Cognitive.StackSymbol system)

    tokenStackSemantics :
      List (Cognitive.StackSymbol system) →
      BT.Trit →
      List (Cognitive.StackSymbol system)

    stackTransitionFactorises :
      ∀ control stack token →
      Cognitive.stackStep system control stack token
      ≡ tokenStackSemantics (physicalStackUpdate control stack) token

open StackCouplingFactorisation public

------------------------------------------------------------------------
-- Concrete smallest-model witness: in the Boolean fixture, control leaves the
-- carrier and token semantics unchanged, while the control-indexed margin is
-- still free to gate transitions.  Thus external forcing need not add a PDA
-- state or redefine token meaning.
------------------------------------------------------------------------

booleanPhysicalFactorisation :
  PhysicalSemanticFactorisation Fixture.booleanCognitiveSystem
booleanPhysicalFactorisation = record
  { physicalEvolution = λ control hidden → hidden
  ; tokenSemantics = λ hidden token → hidden
  ; transitionFactorises = λ control hidden token → refl
  }

booleanGuardOnlyCoupling :
  GuardOnlyCoupling Fixture.booleanCognitiveSystem
booleanGuardOnlyCoupling = record
  { factorisation = booleanPhysicalFactorisation
  ; physicalEvolutionIsIdentity = λ control hidden → refl
  ; tokenSemanticsMatchesTransition = λ control hidden token → refl
  }
