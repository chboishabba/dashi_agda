module DASHI.Cognition.PhysicalCouplingFactorisation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.DashiCognitiveSystem as Cognitive

------------------------------------------------------------------------
-- A control channel may alter the hidden physical carrier before a token is
-- interpreted without adding a new grammar symbol or stack symbol.  This is
-- the precise form of “external, measurable, not a PDA rule, but able to
-- affect internal state through coupling”.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- A stronger guard-only lane leaves token semantics and hidden state alone;
-- control acts only through the already control-indexed margin.  Keppler's
-- candidate term can be tested first in this smallest model class.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- State-affecting coupling is distinct: the grammar alphabet is unchanged,
-- but the physical carrier passed to token semantics may differ.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Stack coupling is separately typed.  A physical control can alter the
-- maintenance/rebuilding of obligations without changing the stack alphabet.
------------------------------------------------------------------------

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
