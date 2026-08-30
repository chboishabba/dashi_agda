module DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact where

------------------------------------------------------------------------
-- POLE-QUOTIENT COMPLEMENT-MARGIN COMPILER
--
-- Bidi correction after the rank-two projective-balance no-go:
--
-- The final contradiction lane must not demand
--
--   postSchurOffEnergy < postSchurClusterEnergy
--
-- while exact rank-two Schur balance identifies those same quantities.
--
-- The already-owned universal even-cone lane gives a better backward shape:
-- kill the pole class exactly, use the high-ordinate exact prime-zero theorem,
-- but DO NOT eliminate Gamma.  Then the surviving balance has schematic form
--
--   cluster = offOrdinate + gammaResidual.
--
-- A positive target-cluster margin can contradict a strict upper budget on the
-- whole complement (offOrdinate + gammaResidual) without asking one quantity
-- to be strictly below itself.
--
-- This file is pure order algebra.  It does not manufacture the harmonic,
-- Gamma, or target-margin inputs and it does not transport Lean proofs.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

record OrderedComplementSurface : Set₁ where
  constructor ordered-complement-surface
  field
    Scalar : Set
    _≤_ _<_ : Scalar → Scalar → Set

    leTrans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    leLtTrans : ∀ {a b c} → a ≤ b → b < c → a < c
    ltIrreflexive : ∀ a → a < a → ⊥

open OrderedComplementSurface public

record PoleQuotientComplementMargin
  (S : OrderedComplementSurface) : Set where
  constructor pole-quotient-complement-margin
  field
    clusterResponse : Scalar S
    complementResponse : Scalar S
    complementBudget : Scalar S
    clusterMargin : Scalar S

    -- Exact source balance after pole quotient / high-ordinate prime removal.
    clusterEqualsComplement : clusterResponse ≡ complementResponse

    -- Quantitative positive target signal.
    clusterMarginLower : clusterMargin ≤ clusterResponse

    -- Whole surviving complement = off-ordinate zeros + Gamma residual.
    complementUpper : complementResponse ≤ complementBudget
    budgetStrictBelowMargin : complementBudget < clusterMargin

open PoleQuotientComplementMargin public

poleQuotientComplementMarginContradiction :
  (S : OrderedComplementSurface) →
  PoleQuotientComplementMargin S →
  ⊥
poleQuotientComplementMarginContradiction S d
  with clusterEqualsComplement d
... | refl =
  ltIrreflexive S (clusterMargin d)
    (leLtTrans S
      (leTrans S
        (clusterMarginLower d)
        (complementUpper d))
      (budgetStrictBelowMargin d))

------------------------------------------------------------------------
-- Provenance/boundary.
------------------------------------------------------------------------

record PoleQuotientComplementMarginBoundary : Set where
  constructor pole-quotient-complement-margin-boundary
  field
    universalPoleQuotientOwnerExists : Bool
    universalPoleQuotientOwnerExistsIsTrue :
      universalPoleQuotientOwnerExists ≡ true

    highOrdinatePrimeVectorZeroOwnerExists : Bool
    highOrdinatePrimeVectorZeroOwnerExistsIsTrue :
      highOrdinatePrimeVectorZeroOwnerExists ≡ true

    rankTwoExactSchurRequiredInFinalContradictionLane : Bool
    rankTwoExactSchurRequiredInFinalContradictionLaneIsFalse :
      rankTwoExactSchurRequiredInFinalContradictionLane ≡ false

    gammaResidualDeliberatelyRetained : Bool
    gammaResidualDeliberatelyRetainedIsTrue :
      gammaResidualDeliberatelyRetained ≡ true

    complementMarginCompilerClosedInAgda : Bool
    complementMarginCompilerClosedInAgdaIsTrue :
      complementMarginCompilerClosedInAgda ≡ true

    offOrdinateHarmonicEstimateManufacturedHere : Bool
    offOrdinateHarmonicEstimateManufacturedHereIsFalse :
      offOrdinateHarmonicEstimateManufacturedHere ≡ false

    gammaResidualBudgetManufacturedHere : Bool
    gammaResidualBudgetManufacturedHereIsFalse :
      gammaResidualBudgetManufacturedHere ≡ false

    quantitativeClusterMarginManufacturedHere : Bool
    quantitativeClusterMarginManufacturedHereIsFalse :
      quantitativeClusterMarginManufacturedHere ≡ false

canonicalPoleQuotientComplementMarginBoundary :
  PoleQuotientComplementMarginBoundary
canonicalPoleQuotientComplementMarginBoundary =
  pole-quotient-complement-margin-boundary
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
