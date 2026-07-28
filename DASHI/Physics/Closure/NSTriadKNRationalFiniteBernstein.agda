module DASHI.Physics.Closure.NSTriadKNRationalFiniteBernstein where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Sergei Bernstein; Hajer Bahouri; Jean-Yves Chemin; Raphael
-- Danchin; DASHI repository contributors.
-- Title: "Finite Fourier-support Bernstein inequality in squared rational
-- form".
-- Venue/year: classical Bernstein inequality; Fourier Analysis and Nonlinear
-- Partial Differential Equations, Springer, 2011; DASHI formal development,
-- 2026.
-- DOI: 10.1007/978-3-642-16830-7; the classical result and the exact
-- finite-list specialization have no separate DOI.
-- Uses: finite squared Cauchy--Schwarz with the constant-one sequence.
-- Relationship: supplies the counting inequality behind the four favourable
-- shell archetypes without invoking a continuous multiplier theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

coefficientPairs : List ℚ → List L2.Pair
coefficientPairs [] = []
coefficientPairs (coefficient ∷ rest) =
  (coefficient , 1ℚ) ∷ coefficientPairs rest

coefficientSum : List ℚ → ℚ
coefficientSum [] = 0ℚ
coefficientSum (coefficient ∷ rest) = coefficient + coefficientSum rest

coefficientNormSquared : List ℚ → ℚ
coefficientNormSquared [] = 0ℚ
coefficientNormSquared (coefficient ∷ rest) =
  L2.square coefficient + coefficientNormSquared rest

supportCardinality : List ℚ → ℚ
supportCardinality [] = 0ℚ
supportCardinality (_ ∷ rest) = 1ℚ + supportCardinality rest

pairDotMeaning : ∀ coefficients →
  L2.pairDot (coefficientPairs coefficients) ≡ coefficientSum coefficients
pairDotMeaning [] = refl
pairDotMeaning (coefficient ∷ rest)
  rewrite pairDotMeaning rest = solve (coefficient ∷ coefficientSum rest ∷ [])

leftNormMeaning : ∀ coefficients →
  L2.leftNormSquared (coefficientPairs coefficients)
  ≡ coefficientNormSquared coefficients
leftNormMeaning [] = refl
leftNormMeaning (coefficient ∷ rest)
  rewrite leftNormMeaning rest = refl

rightNormMeaning : ∀ coefficients →
  L2.rightNormSquared (coefficientPairs coefficients)
  ≡ supportCardinality coefficients
rightNormMeaning [] = refl
rightNormMeaning (coefficient ∷ rest)
  rewrite rightNormMeaning rest = solve (supportCardinality rest ∷ [])

squareCong : ∀ {left right : ℚ} →
  left ≡ right → L2.square left ≡ L2.square right
squareCong refl = refl

congProduct : ∀ {a b c d : ℚ} →
  a ≡ b → c ≡ d → a * c ≡ b * d
congProduct refl refl = refl

finiteBernsteinSquared : ∀ coefficients →
  L2.square (coefficientSum coefficients)
  ≤ supportCardinality coefficients * coefficientNormSquared coefficients
finiteBernsteinSquared coefficients =
  let
    cauchy = L2.finiteCauchySchwarzSquared (coefficientPairs coefficients)
    normalized :
      L2.square (coefficientSum coefficients)
      ≤ coefficientNormSquared coefficients * supportCardinality coefficients
    normalized =
      subst
        (λ left → left ≤
          coefficientNormSquared coefficients * supportCardinality coefficients)
        (squareCong (pairDotMeaning coefficients))
        (subst
          (λ right →
            L2.square (L2.pairDot (coefficientPairs coefficients)) ≤ right)
          (congProduct
            (leftNormMeaning coefficients)
            (rightNormMeaning coefficients))
          cauchy)
  in
  subst
    (λ right → L2.square (coefficientSum coefficients) ≤ right)
    (ℚₚ.*-comm
      (coefficientNormSquared coefficients)
      (supportCardinality coefficients))
    normalized

finiteBernsteinCountingClosed : Bool
finiteBernsteinCountingClosed = true

finiteBernsteinCountingClosedIsTrue :
  finiteBernsteinCountingClosed ≡ true
finiteBernsteinCountingClosedIsTrue = refl
