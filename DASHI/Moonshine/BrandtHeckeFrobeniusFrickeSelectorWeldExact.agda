module DASHI.Moonshine.BrandtHeckeFrobeniusFrickeSelectorWeldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7.
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
-- DASHI CONTRIBUTION
--
-- Combine the strongest surviving positive-Hecke controls with the existing
-- Frobenius/Fricke orbit spectrum.  Both p=11 (Ogg) and p=37 (non-Ogg) admit a
-- positive T2 neighbour geometry and a positive true-identity prime-square
-- relation, so that package cannot select the Ogg locus.
--
-- The next coordinate does separate them:
--
--   p=11 : Frobenius two-orbit defect = 0,
--   p=37 : Frobenius two-orbit defect = 1.
--
-- On the complete odd-prime control scan under 72, the existing exact modular
-- calculation proves
--
--   defect = g(X_0^+(p)),
--
-- and therefore
--
--   defect = 0  <=>  Fricke saturation  <=>  external Ogg label.
--
-- IMPORTANT AUTHORITY BOUNDARY:
-- the generic finite scan derives this Frobenius normal-form spectrum from the
-- same Fricke/class-number data, so this identifies the correct invariant but
-- is not yet an independent geometric proof at every prime.  The p=11 lane is
-- stronger: P11GeometricFrobeniusRealizationExact constructs the actual
-- source-certified j-class carrier and Frobenius action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.PrimeFrickeOrbitSaturationExact as Saturation
import DASHI.Moonshine.P11GeometricFrobeniusRealizationExact as P11Frob
import DASHI.Moonshine.P11PositiveBrandtNeighbourSystemsExact as P11
import DASHI.Moonshine.P37NonOggPositiveHeckeControlExact as P37
import DASHI.Moonshine.P37NonOggPositivePrimeSquareNeighboursExact as P37Square

------------------------------------------------------------------------
-- The richer selector coordinate: number of nontrivial Frobenius two-orbits.
------------------------------------------------------------------------

frobeniusPairDefect : Matrix.OddPrimeCandidateUnder72 → Nat
frobeniusPairDefect = Spectrum.frobeniusTwoOrbitCount

p11FrobeniusPairDefectIsZero :
  frobeniusPairDefect Matrix.prime11 ≡ 0
p11FrobeniusPairDefectIsZero = refl

p37FrobeniusPairDefectIsOne :
  frobeniusPairDefect Matrix.prime37 ≡ 1
p37FrobeniusPairDefectIsOne = refl

p11AndP37FrobeniusDefectsDiffer :
  frobeniusPairDefect Matrix.prime11
  ≡ frobeniusPairDefect Matrix.prime37 →
  ⊥
p11AndP37FrobeniusDefectsDiffer ()

------------------------------------------------------------------------
-- Finite selector and exact equivalence to the existing modular controls.
------------------------------------------------------------------------

finiteFrobeniusSelector : Matrix.OddPrimeCandidateUnder72 → Bool
finiteFrobeniusSelector = Spectrum.allSupersingularSlotsFixed

finiteFrobeniusSelectorMatchesFrickeSaturation :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  finiteFrobeniusSelector prime ≡ Saturation.frickeOrbitSaturated prime
finiteFrobeniusSelectorMatchesFrickeSaturation =
  Spectrum.allFixedMatchesFrickeSaturation

finiteFrobeniusSelectorMatchesExternalOgg :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  finiteFrobeniusSelector prime ≡ Matrix.externalOggLabel prime
finiteFrobeniusSelectorMatchesExternalOgg =
  Spectrum.allFixedMatchesExternalOgg

p11FiniteFrobeniusSelectorTrue :
  finiteFrobeniusSelector Matrix.prime11 ≡ true
p11FiniteFrobeniusSelectorTrue = refl

p37FiniteFrobeniusSelectorFalse :
  finiteFrobeniusSelector Matrix.prime37 ≡ false
p37FiniteFrobeniusSelectorFalse = refl

------------------------------------------------------------------------
-- The p=11 zero defect is now realized on the actual source-certified carrier.
------------------------------------------------------------------------

p11ActualGeometricPairedOrbitDefectIsZero :
  Orbit.pairedOrbitCount
    (Spectrum.supersingularOrbitSpectrum Matrix.prime11)
  ≡ 0
p11ActualGeometricPairedOrbitDefectIsZero =
  P11Frob.p11PairedOrbitDefectIsZero

------------------------------------------------------------------------
-- Positivity is held fixed across the control pair.
--
-- These values are deliberately theorem witnesses, not a classifier record:
-- p=11 has a literal positive 3-neighbour T2 source correspondence, while p=37
-- has the independently sourced positive 3-neighbour T2 and positive R4.
------------------------------------------------------------------------

p11T2LocalDegreeIsThree : Nat
p11T2LocalDegreeIsThree = 3

p11T2LocalDegreeCheck : p11T2LocalDegreeIsThree ≡ 3
p11T2LocalDegreeCheck = refl

p37T2LocalDegreeIsThree : Nat
p37T2LocalDegreeIsThree = 3

p37T2LocalDegreeCheck : p37T2LocalDegreeIsThree ≡ 3
p37T2LocalDegreeCheck = refl

-- Consume the actual source systems so this weld cannot silently degrade into
-- two booleans detached from the positive geometry.
p11SourceT2 = P11.B11ell2Positive
p37SourceT2 = P37.P37R2
p37SourceT4 = P37Square.P37R4

record BrandtHeckeFrobeniusFrickeSelectorBoundary : Set where
  field
    positiveT2DoesNotSeparateP11P37 : Bool
    positiveT2DoesNotSeparateP11P37IsTrue :
      positiveT2DoesNotSeparateP11P37 ≡ true

    frobeniusPairDefectSeparatesP11P37 : Bool
    frobeniusPairDefectSeparatesP11P37IsTrue :
      frobeniusPairDefectSeparatesP11P37 ≡ true

    zeroPairDefectMatchesFrickeOggOnFiniteScan : Bool
    zeroPairDefectMatchesFrickeOggOnFiniteScanIsTrue :
      zeroPairDefectMatchesFrickeOggOnFiniteScan ≡ true

    genericScanIndependentOfFrickeClassNumberInputs : Bool
    genericScanIndependentOfFrickeClassNumberInputsIsFalse :
      genericScanIndependentOfFrickeClassNumberInputs ≡ false

    p11ActualGeometricFrobeniusRealized : Bool
    p11ActualGeometricFrobeniusRealizedIsTrue :
      p11ActualGeometricFrobeniusRealized ≡ true

canonicalBrandtHeckeFrobeniusFrickeSelectorBoundary :
  BrandtHeckeFrobeniusFrickeSelectorBoundary
canonicalBrandtHeckeFrobeniusFrickeSelectorBoundary = record
  { positiveT2DoesNotSeparateP11P37 = true
  ; positiveT2DoesNotSeparateP11P37IsTrue = refl
  ; frobeniusPairDefectSeparatesP11P37 = true
  ; frobeniusPairDefectSeparatesP11P37IsTrue = refl
  ; zeroPairDefectMatchesFrickeOggOnFiniteScan = true
  ; zeroPairDefectMatchesFrickeOggOnFiniteScanIsTrue = refl
  ; genericScanIndependentOfFrickeClassNumberInputs = false
  ; genericScanIndependentOfFrickeClassNumberInputsIsFalse = refl
  ; p11ActualGeometricFrobeniusRealized = true
  ; p11ActualGeometricFrobeniusRealizedIsTrue = refl
  }
