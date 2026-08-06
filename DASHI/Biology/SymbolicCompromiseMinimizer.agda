module DASHI.Biology.SymbolicCompromiseMinimizer where

open import DASHI.Core.Prelude

import DASHI.Biology.SymbolicTransformWithoutHomunculus as Symbolic

------------------------------------------------------------------------
-- Finite symbolic-compromise minimiser.
--
-- A complete candidate family is scored by invariant defect, access cost, and
-- coalition penalty.  A minimiser exists constructively, preserves the latent
-- invariant, need not be unique, and does not require an inner translator.

data SymbolCandidate : Set where
  directCandidate : SymbolCandidate
  transformedCandidate : SymbolCandidate
  alternateTransformedCandidate : SymbolCandidate
  condensedCandidate : SymbolCandidate

candidateForm : Bool → SymbolCandidate → Symbolic.SymbolForm
candidateForm latent directCandidate =
  Symbolic.directRender latent
candidateForm latent transformedCandidate =
  Symbolic.transformedRender latent
candidateForm latent alternateTransformedCandidate =
  Symbolic.transformedRender latent
candidateForm latent condensedCandidate =
  Symbolic.condense latent

invariantDefect : Bool → SymbolCandidate → Nat
invariantDefect latent directCandidate = 0
invariantDefect latent transformedCandidate = 0
invariantDefect latent alternateTransformedCandidate = 0
invariantDefect false condensedCandidate = 0
invariantDefect true condensedCandidate = 2

accessCost : SymbolCandidate → Nat
accessCost directCandidate = 3
accessCost transformedCandidate = 1
accessCost alternateTransformedCandidate = 1
accessCost condensedCandidate = 1

coalitionPenalty : SymbolCandidate → Nat
coalitionPenalty directCandidate = 1
coalitionPenalty transformedCandidate = 0
coalitionPenalty alternateTransformedCandidate = 0
coalitionPenalty condensedCandidate = 2

symbolObjective : Bool → SymbolCandidate → Nat
symbolObjective latent candidate =
  invariantDefect latent candidate
  + accessCost candidate
  + coalitionPenalty candidate

selectedSymbol : Bool → SymbolCandidate
selectedSymbol latent = transformedCandidate

selectedTrueObjectiveIsOne :
  symbolObjective true (selectedSymbol true) ≡ 1
selectedTrueObjectiveIsOne = refl

selectedFalseObjectiveIsOne :
  symbolObjective false (selectedSymbol false) ≡ 1
selectedFalseObjectiveIsOne = refl

selectedTrueSymbolMinimal :
  (candidate : SymbolCandidate) →
  symbolObjective true (selectedSymbol true)
  ≤
  symbolObjective true candidate
selectedTrueSymbolMinimal directCandidate = s≤s z≤n
selectedTrueSymbolMinimal transformedCandidate = ≤-refl
selectedTrueSymbolMinimal alternateTransformedCandidate = ≤-refl
selectedTrueSymbolMinimal condensedCandidate = s≤s z≤n

selectedFalseSymbolMinimal :
  (candidate : SymbolCandidate) →
  symbolObjective false (selectedSymbol false)
  ≤
  symbolObjective false candidate
selectedFalseSymbolMinimal directCandidate = s≤s z≤n
selectedFalseSymbolMinimal transformedCandidate = ≤-refl
selectedFalseSymbolMinimal alternateTransformedCandidate = ≤-refl
selectedFalseSymbolMinimal condensedCandidate = s≤s z≤n

selectedTruePreservesInvariant :
  Symbolic.symbolInvariant
    (candidateForm true (selectedSymbol true))
  ≡
  true
selectedTruePreservesInvariant = refl

selectedFalsePreservesInvariant :
  Symbolic.symbolInvariant
    (candidateForm false (selectedSymbol false))
  ≡
  false
selectedFalsePreservesInvariant = refl

------------------------------------------------------------------------
-- Minimality need not imply uniqueness.

alternateTrueObjectiveAlsoOne :
  symbolObjective true alternateTransformedCandidate ≡ 1
alternateTrueObjectiveAlsoOne = refl

selectedAndAlternateCandidatesDiffer :
  transformedCandidate ≡ alternateTransformedCandidate → ⊥
selectedAndAlternateCandidatesDiffer ()

selectedAndAlternateRenderEqually :
  candidateForm true transformedCandidate
  ≡
  candidateForm true alternateTransformedCandidate
selectedAndAlternateRenderEqually = refl

record FiniteSymbolicMinimizer : Set₁ where
  constructor finiteSymbolicMinimizer
  field
    latent : Bool
    candidate : SymbolCandidate
    minimal :
      (other : SymbolCandidate) →
      symbolObjective latent candidate
      ≤
      symbolObjective latent other
    invariantPreserved :
      Symbolic.symbolInvariant (candidateForm latent candidate)
      ≡
      latent
    priorCompromise :
      Symbolic.SymbolicCompromise

open FiniteSymbolicMinimizer public

canonicalTrueSymbolicMinimizer : FiniteSymbolicMinimizer
canonicalTrueSymbolicMinimizer =
  finiteSymbolicMinimizer
    true
    transformedCandidate
    selectedTrueSymbolMinimal
    selectedTruePreservesInvariant
    Symbolic.canonicalSymbolicCompromise

record SymbolicMinimizerBoundary : Set where
  constructor symbolicMinimizerBoundary
  field
    finiteMinimumGivesUniversalSymbolMeaning : Bool
    finiteMinimumGivesUniversalSymbolMeaningIsFalse :
      finiteMinimumGivesUniversalSymbolMeaning ≡ false

    minimumIsNecessarilyUnique : Bool
    minimumIsNecessarilyUniqueIsFalse :
      minimumIsNecessarilyUnique ≡ false

open SymbolicMinimizerBoundary public

canonicalSymbolicMinimizerBoundary : SymbolicMinimizerBoundary
canonicalSymbolicMinimizerBoundary =
  symbolicMinimizerBoundary false refl false refl
