module DASHI.Core.ZeroValueFibreNontrivialityExact where

------------------------------------------------------------------------
-- ZERO-VALUE FIBRE NONTRIVIALITY
--
-- INTERNAL THEOREM-PATTERN PROVENANCE
--
-- Existing repository owners independently establish stronger domain examples:
--
-- * DASHI.Cognition.ZeroFibreContextuality:
--     distinct hidden orientations share visible zero; an odd-cycle gluing
--     obstruction blocks a global section.
-- * DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact:
--     approaching-zero and leaving-zero share scalar zero but have different
--     future signatures.
-- * draft PR #622 contextual-alternative lane:
--     a zero grouped amplitude is not promoted to absence of every underlying
--     contribution.
--
-- Core does not import those higher-domain modules.  This owner extracts only
-- the domain-neutral finite theorem shape.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Two fine states share one visible zero.
------------------------------------------------------------------------

data FineZeroState : Set where
  hiddenApproach hiddenDeparture : FineZeroState

data ZeroObservation : Set where
  observedZero : ZeroObservation

data FutureClass : Set where
  remainsAtZero leavesZero : FutureClass

zeroObserver : FineZeroState → ZeroObservation
zeroObserver hiddenApproach = observedZero
zeroObserver hiddenDeparture = observedZero

futureClass : FineZeroState → FutureClass
futureClass hiddenApproach = remainsAtZero
futureClass hiddenDeparture = leavesZero

zeroFibreCollision :
  zeroObserver hiddenApproach ≡ zeroObserver hiddenDeparture
zeroFibreCollision = refl

futureClassDistinct :
  futureClass hiddenApproach ≡ futureClass hiddenDeparture → ⊥
futureClassDistinct ()

zeroObservationCannotRecoverFutureClass :
  INF.FactorsThrough zeroObserver futureClass → ⊥
zeroObservationCannotRecoverFutureClass =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      hiddenApproach hiddenDeparture refl futureClassDistinct)

record ZeroValueFibreBoundary : Set where
  constructor zero-value-fibre-boundary
  field
    observerReturnsZeroImpliesFineStateAbsent : Bool
    observerReturnsZeroImpliesFineStateAbsentIsFalse :
      observerReturnsZeroImpliesFineStateAbsent ≡ false
    observerReturnsZeroImpliesTrivialFibre : Bool
    observerReturnsZeroImpliesTrivialFibreIsFalse :
      observerReturnsZeroImpliesTrivialFibre ≡ false
    sameZeroObservationImpliesSameFuture : Bool
    sameZeroObservationImpliesSameFutureIsFalse :
      sameZeroObservationImpliesSameFuture ≡ false
    philosophicalZeroIsBalancedTernaryZero : Bool
    philosophicalZeroIsBalancedTernaryZeroIsFalse :
      philosophicalZeroIsBalancedTernaryZero ≡ false
    philosophicalZeroIsRiemannZetaZero : Bool
    philosophicalZeroIsRiemannZetaZeroIsFalse :
      philosophicalZeroIsRiemannZetaZero ≡ false

canonicalZeroValueFibreBoundary : ZeroValueFibreBoundary
canonicalZeroValueFibreBoundary =
  zero-value-fibre-boundary
    false refl false refl false refl false refl false refl
