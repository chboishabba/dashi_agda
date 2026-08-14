module DASHI.Biology.Physical.FiniteFluctuationRelationExact where

------------------------------------------------------------------------
-- Finite multiplicative precursor of the stochastic-thermodynamic path
-- fluctuation relation.  Instead of introducing analytic log/exp prematurely,
-- each directed edge carries an exact positive likelihood/entropy factor rho
-- satisfying forwardRate = rho * reverseRate.  Path factors multiply exactly.
-- A later real-analysis owner may identify rho = exp(Delta S_tot).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

record BalancedEdge : Set where
  constructor balancedEdge
  field
    forwardRate reverseRate entropyFactor : ℚ
    reverseNonnegative : 0ℚ ≤ reverseRate
    factorNonnegative : 0ℚ ≤ entropyFactor
    localBalance : forwardRate ≡ entropyFactor * reverseRate

open BalancedEdge public

record TwoEdgePath : Set where
  constructor twoEdgePath
  field first second : BalancedEdge

open TwoEdgePath public

forwardWeight : TwoEdgePath → ℚ
forwardWeight p = forwardRate (first p) * forwardRate (second p)

reverseWeight : TwoEdgePath → ℚ
reverseWeight p = reverseRate (first p) * reverseRate (second p)

pathEntropyFactor : TwoEdgePath → ℚ
pathEntropyFactor p = entropyFactor (first p) * entropyFactor (second p)

multiplicativeFluctuationRelation : (p : TwoEdgePath) →
  forwardWeight p ≡ pathEntropyFactor p * reverseWeight p
multiplicativeFluctuationRelation (twoEdgePath e1 e2)
  rewrite localBalance e1 | localBalance e2 = solve-∀

-- Exact driven regression: each forward step is twice its reverse rate, so a
-- two-edge forward trajectory is four times its time-reversed weight.
doubleDrivenEdge : BalancedEdge
doubleDrivenEdge = balancedEdge 2 1 2 (s≤s z≤n) (s≤s z≤n) refl

canonicalDrivenPath : TwoEdgePath
canonicalDrivenPath = twoEdgePath doubleDrivenEdge doubleDrivenEdge

canonicalForwardWeight : forwardWeight canonicalDrivenPath ≡ 4
canonicalForwardWeight = solve-∀

canonicalReverseWeight : reverseWeight canonicalDrivenPath ≡ 1
canonicalReverseWeight = solve-∀

canonicalEntropyFactor : pathEntropyFactor canonicalDrivenPath ≡ 4
canonicalEntropyFactor = solve-∀

record FluctuationAuthorityBoundary : Set where
  field
    rationalFactorIsAnalyticEntropy : Bool
    rationalFactorIsAnalyticEntropyIsFalse : rationalFactorIsAnalyticEntropy ≡ false
    multiplicativeRelationProvesLogFluctuationTheorem : Bool
    multiplicativeRelationProvesLogFluctuationTheoremIsFalse :
      multiplicativeRelationProvesLogFluctuationTheorem ≡ false

canonicalFluctuationAuthorityBoundary : FluctuationAuthorityBoundary
canonicalFluctuationAuthorityBoundary = record
  { rationalFactorIsAnalyticEntropy = false
  ; rationalFactorIsAnalyticEntropyIsFalse = refl
  ; multiplicativeRelationProvesLogFluctuationTheorem = false
  ; multiplicativeRelationProvesLogFluctuationTheoremIsFalse = refl
  }
