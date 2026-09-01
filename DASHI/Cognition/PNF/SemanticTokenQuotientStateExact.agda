module DASHI.Cognition.PNF.SemanticTokenQuotientStateExact where

-- Concrete token-level state discussed in the SSSP/semantic BIDI thread:
--
--   TokenState = (observed value, unresolved residual fibre, bracket, stratum)
--
-- It reuses the existing PNF occurrence receipt and AlternativeFibre rather
-- than introducing a parallel candidate-world representation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.SemanticBracketFractranDivisibilityExact as Bracket

record TokenQuotientState : Set where
  constructor tokenQuotientState
  field
    occurrence : PNF.SpanReceipt
    observedValue : Trit
    unresolvedWorlds : PNF.AlternativeFibre
    currentBracket : Bracket.DiscriminatorBracket
    currentStratum : Nat

open TokenQuotientState public

------------------------------------------------------------------------
-- Refinement is local: a new query/bracket may change the visible value and
-- residual fibre without changing the occurrence identity.
------------------------------------------------------------------------

refineToken :
  TokenQuotientState →
  Trit →
  PNF.AlternativeFibre →
  Bracket.DiscriminatorBracket →
  TokenQuotientState
refineToken state value residual bracket =
  tokenQuotientState
    (occurrence state)
    value
    residual
    bracket
    (suc (currentStratum state))

refinementPreservesOccurrence :
  (state : TokenQuotientState) →
  (value : Trit) →
  (residual : PNF.AlternativeFibre) →
  (bracket : Bracket.DiscriminatorBracket) →
  occurrence (refineToken state value residual bracket) ≡ occurrence state
refinementPreservesOccurrence state value residual bracket = refl

refinementAdvancesStratum :
  (state : TokenQuotientState) →
  (value : Trit) →
  (residual : PNF.AlternativeFibre) →
  (bracket : Bracket.DiscriminatorBracket) →
  currentStratum (refineToken state value residual bracket)
  ≡ suc (currentStratum state)
refinementAdvancesStratum state value residual bracket = refl

------------------------------------------------------------------------
-- Authority boundary: refinement does not itself publish or erase the residual
-- alternatives.  Selection/publication is a separate downstream authority.
------------------------------------------------------------------------

record TokenQuotientBoundary : Set where
  constructor tokenQuotientBoundary
  field
    residualWorldsRetained : Bool
    residualWorldsRetainedIsTrue : residualWorldsRetained ≡ true
    refinementRequiresDocumentReparse : Bool
    refinementRequiresDocumentReparseIsFalse :
      refinementRequiresDocumentReparse ≡ false
    quotientStatePublishesWorldFact : Bool
    quotientStatePublishesWorldFactIsFalse :
      quotientStatePublishesWorldFact ≡ false

canonicalTokenQuotientBoundary : TokenQuotientBoundary
canonicalTokenQuotientBoundary =
  tokenQuotientBoundary true refl false refl false refl
