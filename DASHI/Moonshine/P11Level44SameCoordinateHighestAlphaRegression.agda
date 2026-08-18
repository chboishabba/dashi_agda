module DASHI.Moonshine.P11Level44SameCoordinateHighestAlphaRegression where

------------------------------------------------------------------------
-- Focused regression for the p=11 level-44 same-coordinate weld.
--
-- This root consumes theorem surfaces, not only boundary receipts:
--
--   one Old3 coordinate module
--     -> analytic d=1,2,4 oldspace realization
--     -> marked v1,v2,v4 realization
--
-- and the whole analytic oldspace inherits every good-prime eigencharacter of
-- the level-11 source.  The remaining automorphic/Jacquet--Langlands same-
-- object identification stays explicitly outside this finite/formal theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.FormalQSeriesOldformDegeneracyHeckeExact as Deg
import DASHI.Moonshine.FormalQSeriesOldformEigencharacterTransportExact as Eig
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Marked
import DASHI.Moonshine.P11Level44OldspaceSameObjectCutsetExact as Cutset
import DASHI.Moonshine.P11Level44FormalSameCoordinateComparisonExact as Same

formalComparisonRegression :
  (D : Same.Level44DegeneracyTriple) →
  Cutset.Level44OldspaceSameObjectComparison
formalComparisonRegression = Same.formalSameCoordinateComparison

analyticBasis1Regression :
  (D : Same.Level44DegeneracyTriple) → (n : Nat) →
  Same.analyticRealize D Marked.oldBasis1 n ≡ Same.copy1Series D n
analyticBasis1Regression = Same.analyticBasis1

analyticBasis2Regression :
  (D : Same.Level44DegeneracyTriple) → (n : Nat) →
  Same.analyticRealize D Marked.oldBasis2 n ≡ Same.copy2Series D n
analyticBasis2Regression = Same.analyticBasis2

analyticBasis4Regression :
  (D : Same.Level44DegeneracyTriple) → (n : Nat) →
  Same.analyticRealize D Marked.oldBasis4 n ≡ Same.copy4Series D n
analyticBasis4Regression = Same.analyticBasis4

wholeOldspaceGoodPrimeRegression :
  {D : Same.Level44DegeneracyTriple} {ell : Nat} →
  (H : Same.Level44GoodPrimeEigenData D ell) →
  (v : Marked.Old3) → (n : Nat) →
  Same.analyticHeckeRealize H v n
  ≡ Eig.scaleSeries (Same.eigenvalue H) (Same.analyticRealize D v) n
wholeOldspaceGoodPrimeRegression = Same.wholeOldspaceGoodPrimeEigen

markedDeckRRegression :
  (v : Marked.Old3) →
  Marked.realizeOld3 (Marked.oldR v)
  ≡ DASHI.Moonshine.P11MarkedLevel44PermutationOldspaceExact.deckR5
      (Marked.realizeOld3 v)
markedDeckRRegression = Marked.realizeDeckR

markedDeckSRegression :
  (v : Marked.Old3) →
  Marked.realizeOld3 (Marked.oldS v)
  ≡ DASHI.Moonshine.P11MarkedLevel44PermutationOldspaceExact.deckS5
      (Marked.realizeOld3 v)
markedDeckSRegression = Marked.realizeDeckS

actualAutomorphicComparisonStillOpen :
  Same.actualEichlerJacquetLanglandsComparisonConstructed
    Same.canonicalP11Level44FormalSameCoordinateBoundary ≡ false
actualAutomorphicComparisonStillOpen = refl
