module DASHI.Mathematics.Automorphic.EllipticDirichletBaselMajorantExact where

------------------------------------------------------------------------
-- DIRICHLET TERMS DOMINATED BY THE CONSTRUCTIVE BASEL SERIES
--
-- DASHI already owns a machine-checked Bishop proof that
--
--   sum_n 1/(n+1)^2
--
-- converges.  Therefore an elliptic Dirichlet-series convergence proof does
-- not need another completeness or p-series interface: once the literal
-- elliptic terms satisfy an eventual absolute-value bound by this sequence,
-- Bishop's comparison theorem gives convergence directly.
--
-- The actual all-n elliptic coefficient estimate is intentionally NOT supplied
-- here.  The current repository only has finite Frobenius rows / finite Euler
-- products and a modularity receipt interface, not a proved global coefficient
-- growth theorem for the selected elliptic curve.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel

baselDominatedDirichletSeriesConvergent :
  (term : Nat → BishopReal.ℝ) →
  (dominationStart : Nat) →
  ((index : Nat) →
    dominationStart ≤ index →
    BishopReal._≤_
      (BishopReal.∣ term index ∣)
      (Basel.baselTerm index)) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf term)
baselDominatedDirichletSeriesConvergent
    term dominationStart eventuallyDominated =
  BishopSequence.proposition-3-5
    Basel.baselSeriesConvergent
    (dominationStart , eventuallyDominated)

baselDominationIsLiteralAbsoluteInequality :
  (term : Nat → BishopReal.ℝ) →
  (dominationStart : Nat) →
  ((index : Nat) →
    dominationStart ≤ index →
    BishopReal._≤_
      (BishopReal.∣ term index ∣)
      (Basel.baselTerm index)) →
  (index : Nat) →
  dominationStart ≤ index →
  BishopReal._≤_
    (BishopReal.∣ term index ∣)
    (Basel.baselTerm index)
baselDominationIsLiteralAbsoluteInequality
    term dominationStart domination index indexLarge =
  domination index indexLarge

record EllipticDirichletBaselMajorantBoundary : Set where
  constructor elliptic-dirichlet-basel-majorant-boundary
  field
    constructiveBaselSeriesReused : Bool
    bishopComparisonTheoremReused : Bool
    literalAbsoluteMajorantShapePaid : Bool
    baselMajorantToDirichletConvergencePaid : Bool
    allNHeckeCoefficientFamilyPaid : Bool
    actualEllipticCoefficientMajorantPaid : Bool
    actualEllipticDirichletSeriesConvergencePaid : Bool
    eulerDirichletSameObjectPaid : Bool
    mellinRealizationPaid : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticDirichletBaselMajorantBoundary :
  EllipticDirichletBaselMajorantBoundary
canonicalEllipticDirichletBaselMajorantBoundary =
  elliptic-dirichlet-basel-majorant-boundary
    true true true true false false false false false false
