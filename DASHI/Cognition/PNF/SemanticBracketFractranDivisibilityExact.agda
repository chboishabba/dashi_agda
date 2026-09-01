module DASHI.Cognition.PNF.SemanticBracketFractranDivisibilityExact where

-- Literal executable weld between semantic bracket availability and the
-- existing FRACTRAN prime-valuation rule gate.
--
-- This is a finite exact witness for the architectural statement:
--
--   discriminator bracket unavailable -> distinguishing rule disabled
--   discriminator bracket available   -> distinguishing rule enabled
--
-- The semantic meaning of the bracket is not inferred from the prime itself;
-- this module supplies an explicit compiler from bracket state to the existing
-- arithmetic controller.

open import DASHI.Core.Prelude

import DASHI.Biology.FRACTRANSSPTransitionExact as F
import DASHI.Geometry.SSP369Ultrametric as SSP
import DASHI.Biology.OrientedZeroWaveTransitionExact as Zero

------------------------------------------------------------------------
-- 1. Semantic bracket state.
------------------------------------------------------------------------

data DiscriminatorBracket : Set where
  bracketUnavailable bracketAvailable : DiscriminatorBracket

-- The distinguished dependency prime for this finite witness is 47.  A zero
-- exponent means the denominator/dependency resource is absent; successor
-- exponent means it is available.  Other coordinates are held fixed.

compileBracket : DiscriminatorBracket → F.PrimeValuationState
compileBracket bracketUnavailable =
  F.primeValuationState
    zero 1 0 0 F.canonicalSSPAddress Zero.fromNegative
compileBracket bracketAvailable =
  F.primeValuationState
    1 1 0 0 F.canonicalSSPAddress Zero.fromNegative

------------------------------------------------------------------------
-- 2. Exact arithmetic gate.
------------------------------------------------------------------------

bracketUnavailableDisablesDistinguishingRule :
  F.ruleEnabled F.transfer47To59 (compileBracket bracketUnavailable) ≡ false
bracketUnavailableDisablesDistinguishingRule = refl

bracketAvailableEnablesDistinguishingRule :
  F.ruleEnabled F.transfer47To59 (compileBracket bracketAvailable) ≡ true
bracketAvailableEnablesDistinguishingRule = refl

------------------------------------------------------------------------
-- 3. Only an available bracket carries split authority.
------------------------------------------------------------------------

data ResidualSplitPermission : DiscriminatorBracket → Set where
  bracketAuthorisesSplit : ResidualSplitPermission bracketAvailable

unavailableBracketCannotAuthoriseSplit :
  ResidualSplitPermission bracketUnavailable → ⊥
unavailableBracketCannotAuthoriseSplit ()

availableBracketAuthorisesSplit :
  ResidualSplitPermission bracketAvailable
availableBracketAuthorisesSplit = bracketAuthorisesSplit

------------------------------------------------------------------------
-- 4. The enabled rule performs an actual state change when the bracket exists.
------------------------------------------------------------------------

availableBracketTransition :
  F.applyRule F.transfer47To59 (compileBracket bracketAvailable)
  ≡
  F.primeValuationState
    0 1 1 0 F.canonicalSSPAddress Zero.fromPositive
availableBracketTransition = refl

unavailableBracketTransitionIsBlocked :
  F.applyRule F.transfer47To59 (compileBracket bracketUnavailable)
  ≡ compileBracket bracketUnavailable
unavailableBracketTransitionIsBlocked = refl

------------------------------------------------------------------------
-- 5. BIDI boundary.
--
-- Forward: bracket availability is compiled to a concrete prime-exponent gate.
-- Reverse: enabledness alone is not semantic authority; the explicit compiler
-- is part of this witness.  No arbitrary FRACTRAN prime is declared to mean a
-- semantic bracket.
------------------------------------------------------------------------

record SemanticBracketDivisibilityBoundary : Set where
  constructor semanticBracketDivisibilityBoundary
  field
    unavailableDisables :
      F.ruleEnabled F.transfer47To59 (compileBracket bracketUnavailable) ≡ false
    availableEnables :
      F.ruleEnabled F.transfer47To59 (compileBracket bracketAvailable) ≡ true
    unavailableHasNoSplitAuthority :
      ResidualSplitPermission bracketUnavailable → ⊥
    availableHasSplitAuthority :
      ResidualSplitPermission bracketAvailable
    arithmeticEnablednessAloneDefinesSemanticMeaning : Bool
    arithmeticEnablednessAloneDefinesSemanticMeaningIsFalse :
      arithmeticEnablednessAloneDefinesSemanticMeaning ≡ false

canonicalSemanticBracketDivisibilityBoundary : SemanticBracketDivisibilityBoundary
canonicalSemanticBracketDivisibilityBoundary =
  semanticBracketDivisibilityBoundary
    bracketUnavailableDisablesDistinguishingRule
    bracketAvailableEnablesDistinguishingRule
    unavailableBracketCannotAuthoriseSplit
    availableBracketAuthorisesSplit
    false refl
