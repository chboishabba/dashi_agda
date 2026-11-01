module DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularFrechetBridgeRound67Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Brian C. Hall.
-- Title: "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Jean-Luc Guermond.
-- Title: "Banach and Hilbert Spaces: Linear Mappings", Chapter 7 lecture
-- notes, Texas A&M University (2017). No DOI recorded.
--
-- ROUND 67 / B-E CROSS-POLLINATION
--
-- Reuse the exact finite-dimensional Frechet expansion carrier developed in
-- the Yang-Mills lane.  The explicit Round67 C^4 transition polynomial is now
-- not merely a list of endpoint identities: it is an exact first-order
-- expansion on Q with
--
--   derivative(x)[h] = S'(x) h
--
-- and a literal remainder
--
--   R(x,h) = S(x+h) - S(x) - S'(x)h.
--
-- The increment identity and derivative additivity are proved exactly by ring
-- normalization.  No differentiability receipt is inserted.  This gives the
-- NS multiplier lane the same `ExactFirstOrderExpansion` object already used
-- by the Balaban/YM derivative DAG, so later same-object product/chain proofs
-- can reuse one calculus substrate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanClayGate4FiniteDimensionalFrechetChainProductExact as Frechet
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact as C4

rationalAdditiveCarrier : Frechet.AdditiveCarrier ℚ
rationalAdditiveCarrier = record
  { Frechet.AdditiveCarrier.zero = 0ℚ
  ; Frechet.AdditiveCarrier.add = _+_
  ; Frechet.AdditiveCarrier.addAssociative = λ left middle right →
      solve (left ∷ middle ∷ right ∷ [])
  }

smoothStep4LinearDerivative : ℚ → ℚ → ℚ
smoothStep4LinearDerivative point increment =
  C4.smoothStep4D1 point * increment

smoothStep4ExactRemainder : ℚ → ℚ → ℚ
smoothStep4ExactRemainder point increment =
  C4.smoothStep4 (point + increment)
  + (- (C4.smoothStep4 point))
  + (- (smoothStep4LinearDerivative point increment))

smoothStep4DerivativeAdditive : ∀ point left right →
  smoothStep4LinearDerivative point (left + right)
  ≡ smoothStep4LinearDerivative point left
      + smoothStep4LinearDerivative point right
smoothStep4DerivativeAdditive point left right =
  solve (C4.smoothStep4D1 point ∷ left ∷ right ∷ [])

smoothStep4IncrementExpansion : ∀ point increment →
  C4.smoothStep4 (point + increment)
  ≡ C4.smoothStep4 point
      + (smoothStep4LinearDerivative point increment
        + smoothStep4ExactRemainder point increment)
smoothStep4IncrementExpansion point increment =
  solve
    ( C4.smoothStep4 (point + increment)
    ∷ C4.smoothStep4 point
    ∷ smoothStep4LinearDerivative point increment
    ∷ [])

smoothStep4ExactFirstOrderExpansion :
  Frechet.ExactFirstOrderExpansion
    rationalAdditiveCarrier rationalAdditiveCarrier
smoothStep4ExactFirstOrderExpansion = record
  { Frechet.ExactFirstOrderExpansion.function = C4.smoothStep4
  ; Frechet.ExactFirstOrderExpansion.derivative = smoothStep4LinearDerivative
  ; Frechet.ExactFirstOrderExpansion.remainder = smoothStep4ExactRemainder
  ; Frechet.ExactFirstOrderExpansion.derivativeAdditive =
      smoothStep4DerivativeAdditive
  ; Frechet.ExactFirstOrderExpansion.incrementExpansion =
      smoothStep4IncrementExpansion
  }

smoothStep4FrechetFunctionSameObject :
  Frechet.function smoothStep4ExactFirstOrderExpansion ≡ C4.smoothStep4
smoothStep4FrechetFunctionSameObject = refl

smoothStep4FrechetDerivativeSameObject : ∀ point increment →
  Frechet.derivative smoothStep4ExactFirstOrderExpansion point increment
  ≡ C4.smoothStep4D1 point * increment
smoothStep4FrechetDerivativeSameObject point increment = refl

smoothStep4FrechetRemainderSameObject : ∀ point increment →
  Frechet.remainder smoothStep4ExactFirstOrderExpansion point increment
  ≡ smoothStep4ExactRemainder point increment
smoothStep4FrechetRemainderSameObject point increment = refl

round67AnnularCutoffFrechetExpansionConstructed : Bool
round67AnnularCutoffFrechetExpansionConstructed = true

round67AnnularCutoffFrechetExpansionConstructedIsTrue :
  round67AnnularCutoffFrechetExpansionConstructed ≡ true
round67AnnularCutoffFrechetExpansionConstructedIsTrue = refl
