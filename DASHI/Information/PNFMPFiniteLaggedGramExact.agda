module DASHI.Information.PNFMPFiniteLaggedGramExact where

-- Original DASHI maximum-cut: explicit non-symmetric lag-one Gram for
-- the *same* 4×2 examples in the MP static Gram negative-control owners.
-- G1(a,b) = sum_{t=0}^{2} X(t,a) * X(t+1,b).
-- This is an order-aware finite operator, not a proof of free probability,
-- Brown measure, circular law, iid statistics, or causal direction.
--
-- Exact results:
-- (i) static moments agree but a labelled lag entry differs;
-- (ii) source full-rank static moments also agree, and their lag entry differs;
-- (iii) the full-rank lag matrices have the same trace and 2×2
--       characteristic-polynomial coefficients: even dynamic eigenvalues
--       can discard orientation information.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Information.PNFMPTemporalOrderingNonIdentificationExact as Time
import DASHI.Information.PNFMPStaticGramTemporalNonIdentificationExact as Static
import DASHI.Information.PNFMPFullRankTemporalNonIdentificationExact as Full

-- General finite four-row lag pairing for the existing column carrier.
lagWith :
  (Time.TimeOrder → Time.FourSample → Static.Column → Nat) →
  Time.TimeOrder → Static.Column → Static.Column → Nat
lagWith entry h a b =
  entry h Time.first a * entry h Time.second b +
  entry h Time.second a * entry h Time.third b +
  entry h Time.third a * entry h Time.fourth b

singularLag : Time.TimeOrder → Static.Column → Static.Column → Nat
singularLag = lagWith Static.entry

fullRankLag : Time.TimeOrder → Static.Column → Static.Column → Nat
fullRankLag = lagWith Full.entry

-- Singular example: A=[[0,1],[2,0]], B=[[1,0],[1,1]]
-- under previous-row transpose times next-row convention.
singularA11 : singularLag Time.alternating Static.firstColumn Static.firstColumn ≡ 0
singularA11 = refl

singularA12 : singularLag Time.alternating Static.firstColumn Static.secondColumn ≡ 1
singularA12 = refl

singularA21 : singularLag Time.alternating Static.secondColumn Static.firstColumn ≡ 2
singularA21 = refl

singularA22 : singularLag Time.alternating Static.secondColumn Static.secondColumn ≡ 0
singularA22 = refl

singularB11 : singularLag Time.clustered Static.firstColumn Static.firstColumn ≡ 1
singularB11 = refl

singularB12 : singularLag Time.clustered Static.firstColumn Static.secondColumn ≡ 0
singularB12 = refl

singularB21 : singularLag Time.clustered Static.secondColumn Static.firstColumn ≡ 1
singularB21 = refl

singularB22 : singularLag Time.clustered Static.secondColumn Static.secondColumn ≡ 1
singularB22 = refl

-- Source observer can recover the *selected* lost first-column lag
-- because the diagonal of the labelled G1 equals its original lag sum.
lagDiagonalIsOriginal :
  (h : Time.TimeOrder) →
  singularLag h Static.firstColumn Static.firstColumn
    ≡ Time.lagOneProducts h
lagDiagonalIsOriginal Time.alternating = refl
lagDiagonalIsOriginal Time.clustered = refl

lagDiagonalSeparatesSingularOrders :
  singularLag Time.alternating Static.firstColumn Static.firstColumn
    ≡ singularLag Time.clustered Static.firstColumn Static.firstColumn → ⊥
lagDiagonalSeparatesSingularOrders ()

staticStatsStillCollide :
  Static.staticTwoColumnStatistics Time.alternating
    ≡ Static.staticTwoColumnStatistics Time.clustered
staticStatsStillCollide = Static.equalFullTwoColumnStatistics

-- The *full-rank* example has the same labelled diagonal separation.
-- A=[[0,1],[1,1]], B=[[1,1],[1,0]].
fullA11 : fullRankLag Time.alternating Static.firstColumn Static.firstColumn ≡ 0
fullA11 = refl
fullA12 : fullRankLag Time.alternating Static.firstColumn Static.secondColumn ≡ 1
fullA12 = refl
fullA21 : fullRankLag Time.alternating Static.secondColumn Static.firstColumn ≡ 1
fullA21 = refl
fullA22 : fullRankLag Time.alternating Static.secondColumn Static.secondColumn ≡ 1
fullA22 = refl

fullB11 : fullRankLag Time.clustered Static.firstColumn Static.firstColumn ≡ 1
fullB11 = refl
fullB12 : fullRankLag Time.clustered Static.firstColumn Static.secondColumn ≡ 1
fullB12 = refl
fullB21 : fullRankLag Time.clustered Static.secondColumn Static.firstColumn ≡ 1
fullB21 = refl
fullB22 : fullRankLag Time.clustered Static.secondColumn Static.secondColumn ≡ 0
fullB22 = refl

fullLagDiagonalSeparatesOrders :
  fullRankLag Time.alternating Static.firstColumn Static.firstColumn
    ≡ fullRankLag Time.clustered Static.firstColumn Static.firstColumn → ⊥
fullLagDiagonalSeparatesOrders ()

fullRankStaticStatsStillCollide :
  Full.stats Time.alternating ≡ Full.stats Time.clustered
fullRankStaticStatsStillCollide = Full.equalFullRankStaticStatistics

-- Equality of lag spectra is weaker than equality of lag operators.
-- For a 2×2 matrix the characteristic polynomial is
-- x² - (a+d)x + (ad-bc). We record the trace a+d and both nonnegative
-- determinant constituents ad and bc, avoiding an integer subtraction.
lagTrace : (Time.TimeOrder → Static.Column → Static.Column → Nat) →
  Time.TimeOrder → Nat
lagTrace L h = L h Static.firstColumn Static.firstColumn +
               L h Static.secondColumn Static.secondColumn

lagDetPositivePart : (Time.TimeOrder → Static.Column → Static.Column → Nat) →
  Time.TimeOrder → Nat
lagDetPositivePart L h =
  L h Static.firstColumn Static.firstColumn *
  L h Static.secondColumn Static.secondColumn

lagDetNegativePart : (Time.TimeOrder → Static.Column → Static.Column → Nat) →
  Time.TimeOrder → Nat
lagDetNegativePart L h =
  L h Static.firstColumn Static.secondColumn *
  L h Static.secondColumn Static.firstColumn

fullRankLagTraceMatches :
  lagTrace fullRankLag Time.alternating
    ≡ lagTrace fullRankLag Time.clustered
fullRankLagTraceMatches = refl

fullRankLagPositiveDetMatches :
  lagDetPositivePart fullRankLag Time.alternating
    ≡ lagDetPositivePart fullRankLag Time.clustered
fullRankLagPositiveDetMatches = refl

fullRankLagNegativeDetMatches :
  lagDetNegativePart fullRankLag Time.alternating
    ≡ lagDetNegativePart fullRankLag Time.clustered
fullRankLagNegativeDetMatches = refl

-- Here trace=1, determinant=-1 for both, so both characteristic
-- polynomials are x²-x-1. This is an exact finite arithmetic statement;
-- no field-level characteristic-polynomial theorem is imported here.
fullLagTraceOne :
  lagTrace fullRankLag Time.alternating ≡ 1
fullLagTraceOne = refl

fullLagPositiveDetZero :
  lagDetPositivePart fullRankLag Time.alternating ≡ 0
fullLagPositiveDetZero = refl

fullLagNegativeDetOne :
  lagDetNegativePart fullRankLag Time.alternating ≡ 1
fullLagNegativeDetOne = refl

-- A representation that keeps only the two polynomial coefficients
-- continues to erase the distinction between the two labelled G1's.
data LagPolynomialCoefficients : Set where
  lag-polynomial : Nat → Nat → Nat → LagPolynomialCoefficients

lagPolyObservation : Time.TimeOrder → LagPolynomialCoefficients
lagPolyObservation h =
  lag-polynomial (lagTrace fullRankLag h)
    (lagDetPositivePart fullRankLag h)
    (lagDetNegativePart fullRankLag h)

sameLagPolynomialCoefficients :
  lagPolyObservation Time.alternating
    ≡ lagPolyObservation Time.clustered
sameLagPolynomialCoefficients = refl

lagSpectrumCoefficientsCannotRecoverDiagonal :
  NF.FactorsThrough lagPolyObservation Time.lagOneProducts → ⊥
lagSpectrumCoefficientsCannotRecoverDiagonal =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      Time.alternating Time.clustered
      sameLagPolynomialCoefficients Time.differentLagOne)

anyLagEigenvalueRechartCannotRecoverDiagonal :
  ∀ {Out : Set} (eigenChart : LagPolynomialCoefficients → Out) →
  NF.FactorsThrough
    (λ h → eigenChart (lagPolyObservation h))
    Time.lagOneProducts → ⊥
anyLagEigenvalueRechartCannotRecoverDiagonal eigenChart =
  NF.rechartingCannotRecoverErasedPhenomenon eigenChart
    (NF.nonFactorabilityWitness
      Time.alternating Time.clustered
      sameLagPolynomialCoefficients Time.differentLagOne)

-- Strict modelling boundary: adding labelled G1 recovers the particular
-- chosen lag statistic, but not every historical row or latent controller.
-- Beyond lag-one, retain original source times and suitable delay data.
