module DASHI.Moonshine.P11P37P43GeometricFrobeniusSelectorInstantiationsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7,
-- MR 417184; no DOI asserted.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Josep Gonzalez,
-- "On the p-th division polynomial", Journal of Number Theory 233 (2022),
-- 285--300. DOI: 10.1016/j.jnt.2021.06.011.
--
-- DASHI CONTRIBUTION
--
-- Exercise GeometricSupersingularFrobeniusSelectorConsequenceExact on THREE
-- source-facing arithmetic realizations that already exist in the repo:
--
--   p=11 : actual j={0,1728}, Frobenius pointwise fixed;
--   p=37 : Sage-labelled j={8,27a+23,10a+20}, one quadratic pair;
--   p=43 : Deuring/Legendre coarse j carrier, two fixed + one quadratic pair.
--
-- Thus the generic selector theorem is not left as an empty interface layer.
-- We prove directly on the geometric carriers:
--
--   p11 : Frobenius is pointwise identity;
--   p37 : Frobenius is NOT pointwise identity;
--   p43 : Frobenius is NOT pointwise identity.
--
-- and consume the generic realization theorem to recover the corresponding
-- genus/Ogg selector consequences.  This establishes the entire current
-- source-facing Ogg/control cutset using real arithmetic states rather than the
-- Fricke-derived normal-form counts alone.
--
-- IMPORTANT BOUNDARY
-- The all-prime realization is still not constructed.  These are three exact
-- control instantiations of the one generic theorem whose remaining producer is
-- a source-native realization for arbitrary relevant prime p.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke
import DASHI.Moonshine.GeometricSupersingularFrobeniusSelectorConsequenceExact as Selector
import DASHI.Moonshine.P11GeometricFrobeniusRealizationExact as P11
import DASHI.Moonshine.P37SageSupersingularFrobeniusExact as P37
import DASHI.Moonshine.P43GeometricFrobeniusRealizationExact as P43
import DASHI.Moonshine.P43NonOggFullLevel2DeuringControlExact as P43Carrier

------------------------------------------------------------------------
-- p=11: actual geometric Frobenius is pointwise fixed.
------------------------------------------------------------------------

p11GeometricallyFullyFixed : Selector.GeometricallyFullyFixed P11.p11FrobeniusCarrier
p11GeometricallyFullyFixed =
  Selector.realizationGenusZeroImpliesAllFixed
    P11.p11FrobeniusCarrier
    P11.p11GeometricSpectrumRealization
    refl

p11GeometricAllFixedImpliesGenusZero :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime11) ≡ 0
p11GeometricAllFixedImpliesGenusZero =
  Selector.realizationAllFixedImpliesGenusZero
    P11.p11FrobeniusCarrier
    P11.p11GeometricSpectrumRealization
    p11GeometricallyFullyFixed

p11ExternalOggTrueFromGeometry : Matrix.externalOggLabel Matrix.prime11 ≡ true
p11ExternalOggTrueFromGeometry =
  Selector.realizationAllFixedImpliesExternalOgg
    P11.p11FrobeniusCarrier
    P11.p11GeometricSpectrumRealization
    p11GeometricallyFullyFixed

------------------------------------------------------------------------
-- p=37: explicit quadratic Frobenius pair witnesses non-fixed geometry.
------------------------------------------------------------------------

p37NotGeometricallyFullyFixed :
  Selector.GeometricallyFullyFixed P37.p37FrobeniusCarrier → ⊥
p37NotGeometricallyFullyFixed allFixed
  with allFixed P37.j27aPlus23
... | ()

p37GenusNotZero :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime37) ≡ 0 → ⊥
p37GenusNotZero genusZero =
  p37NotGeometricallyFullyFixed
    (Selector.realizationGenusZeroImpliesAllFixed
      P37.p37FrobeniusCarrier
      P37.p37GeometricSpectrumRealization
      genusZero)

p37ExternalOggCannotBeTrue :
  Matrix.externalOggLabel Matrix.prime37 ≡ true → ⊥
p37ExternalOggCannotBeTrue externalTrue =
  p37NotGeometricallyFullyFixed
    (Selector.realizationExternalOggImpliesAllFixed
      P37.p37FrobeniusCarrier
      P37.p37GeometricSpectrumRealization
      externalTrue)

------------------------------------------------------------------------
-- p=43: explicit quadratic j-pair gives the same source-facing non-Ogg result.
------------------------------------------------------------------------

p43NotGeometricallyFullyFixed :
  Selector.GeometricallyFullyFixed P43.p43FrobeniusCarrier → ⊥
p43NotGeometricallyFullyFixed allFixed
  with allFixed P43Carrier.jQuadratic0
... | ()

p43GenusNotZero :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime43) ≡ 0 → ⊥
p43GenusNotZero genusZero =
  p43NotGeometricallyFullyFixed
    (Selector.realizationGenusZeroImpliesAllFixed
      P43.p43FrobeniusCarrier
      P43.p43GeometricSpectrumRealization
      genusZero)

p43ExternalOggCannotBeTrue :
  Matrix.externalOggLabel Matrix.prime43 ≡ true → ⊥
p43ExternalOggCannotBeTrue externalTrue =
  p43NotGeometricallyFullyFixed
    (Selector.realizationExternalOggImpliesAllFixed
      P43.p43FrobeniusCarrier
      P43.p43GeometricSpectrumRealization
      externalTrue)

------------------------------------------------------------------------
-- Exact three-control separator summary.
------------------------------------------------------------------------

record GeometricThreePrimeSelectorControl : Set where
  field
    p11ActualCarrierAllFixed : Bool
    p37ActualCarrierHasNontrivialPair : Bool
    p43ActualCarrierHasNontrivialPair : Bool
    p11GeometryForcesOggTrue : Bool
    p37OggTrueContradictedByGeometry : Bool
    p43OggTrueContradictedByGeometry : Bool
    sameGenericSelectorTheoremUsed : Bool
    allPrimeGeometricRealizationConstructed : Bool

canonicalGeometricThreePrimeSelectorControl : GeometricThreePrimeSelectorControl
canonicalGeometricThreePrimeSelectorControl = record
  { p11ActualCarrierAllFixed = true
  ; p37ActualCarrierHasNontrivialPair = true
  ; p43ActualCarrierHasNontrivialPair = true
  ; p11GeometryForcesOggTrue = true
  ; p37OggTrueContradictedByGeometry = true
  ; p43OggTrueContradictedByGeometry = true
  ; sameGenericSelectorTheoremUsed = true
  ; allPrimeGeometricRealizationConstructed = false
  }
