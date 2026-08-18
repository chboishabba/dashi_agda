module DASHI.Moonshine.MarkedOldspaceGeometricOggFrontierEverything where

------------------------------------------------------------------------
-- Focused frontier root after the p11/p37/p43 marked-Hecke tranches.
--
-- OLDSPACE SIDE
--   one common Old3 coordinate module now realizes both:
--     * the formal analytic d=1,2,4 degeneracy span;
--     * the source-native marked v1,v2,v4 permutation span.
--   The entire analytic span inherits every good-prime level-11 eigencharacter.
--   Remaining seam: actual automorphic/Eichler--Jacquet--Langlands same-object
--   identification of those already-common coordinates.
--
-- OGG SELECTOR SIDE
--   generic count algebra proves pair defect = Fricke genus once the standard
--   supersingular/Fricke count identities are supplied;
--   stronger geometric route: one rational special-fibre component with one
--   node per quadratic supersingular pair has arithmetic genus equal to the
--   pair count, hence flat genus preservation gives
--
--       g(X0+(p)) = Frobenius pair defect.
--
--   Remaining seam: construct the Deligne--Rapoport/Fricke special-fibre
--   realization for arbitrary p on the actual modular-curve carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.FormalQSeriesOldformEigencharacterTransportExact as Eig
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Marked
import DASHI.Moonshine.P11Level44FormalSameCoordinateComparisonExact as Same
import DASHI.Moonshine.P11Level44SameCoordinateHighestAlphaRegression as SameReg
import DASHI.Moonshine.SupersingularFrobeniusFrickeGenusReductionExact as CountReduce
import DASHI.Moonshine.SupersingularFrobeniusFrickeGenusReductionRegression as CountReg
import DASHI.Moonshine.RationalNodalSpecialFibreGenusExact as Nodal
import DASHI.Moonshine.SupersingularFrickeSpecialFibreSelectorExact as Geometric

wholeOldspaceRegression :
  {D : Same.Level44DegeneracyTriple} {ell : Nat} →
  (H : Same.Level44GoodPrimeEigenData D ell) →
  (v : Marked.Old3) →
  (n : Nat) →
  Same.analyticHeckeRealize H v n
  ≡ Eig.scaleSeries (Same.eigenvalue H) (Same.analyticRealize D v) n
wholeOldspaceRegression = Same.wholeOldspaceGoodPrimeEigen

countReductionRegression :
  (D : CountReduce.SupersingularFrickeCountData) →
  CountReduce.frobeniusPairDefect D ≡ CountReduce.genusX0Plus D
countReductionRegression = CountReduce.frobeniusPairDefectEqualsFrickeGenus

nodalGenusRegression :
  (D : Nodal.NodalDualGraphGenusData) →
  Nodal.arithmeticGenus D ≡ Nodal.nodeCount D
nodalGenusRegression = Nodal.arithmeticGenusEqualsNodeCount

geometricSelectorRegression :
  (R : Geometric.PrimeFrickeSpecialFibreRealization) →
  Geometric.genericFrickeGenus R ≡ Geometric.frobeniusPairDefect R
geometricSelectorRegression = Geometric.frickeGenusEqualsFrobeniusPairDefect
