module DASHI.Biology.Physical.FiniteFluctuationRelationExact where

------------------------------------------------------------------------
-- Finite multiplicative precursor of the stochastic-thermodynamic path
-- fluctuation relation.  Each directed edge carries an exact likelihood factor
-- rho satisfying forwardRate = rho * reverseRate.  Path factors multiply.
-- Positivity and the analytic identification rho = exp(Delta S_tot) remain
-- separate physical obligations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

record BalancedEdge : Set where
  constructor balancedEdge
  field
    forwardRate reverseRate entropyFactor : ℚ
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

doubleDrivenEdge : BalancedEdge
doubleDrivenEdge = balancedEdge 2 1 2 refl

canonicalDrivenPath : TwoEdgePath
canonicalDrivenPath = twoEdgePath doubleDrivenEdge doubleDrivenEdge

canonicalForwardWeight : forwardWeight canonicalDrivenPath ≡ 4
canonicalForwardWeight = solve-∀

canonicalReverseWeight : reverseWeight canonicalDrivenPath ≡ 1
canonicalReverseWeight = solve-∀

canonicalEntropyFactor : pathEntropyFactor canonicalDrivenPath ≡ 4
canonicalEntropyFactor = solve-∀

record PositiveBalancedEdge (e : BalancedEdge) : Set₁ where
  field
    ForwardPositive ReversePositive FactorPositive : Set

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
