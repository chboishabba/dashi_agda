module DASHI.Moonshine.PrimeFrickeOrbitSaturationExact where

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
-- DASHI CONTRIBUTION
--
-- Re-express the finite Fricke genus-zero condition as symmetry-orbit
-- saturation.  Riemann-Hurwitz is stored in PrimeFrickeGenusControlExact as
--
--   4*gPlus + fixed = 2*g0 + 2.
--
-- Therefore genus zero is the saturated case in which the Fricke fixed-point
-- count consumes the whole topological budget:
--
--   fixed = 2*g0 + 2.
--
-- On the complete odd-prime control scan below 72 this saturation Boolean is
-- definitionally equal both to the internally computed genus-zero Boolean and
-- to the separately supplied external Ogg label.  This gives the modular side
-- a literal reduced-symmetry closure law without importing a representation-
-- side explanation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc left) (suc right) = natEqual left right

topologicalBudget : Fricke.PrimeFrickeGenusRow → Nat
topologicalBudget row = 2 * Fricke.genusX0 row + 2

frickeOrbitSaturated : Matrix.OddPrimeCandidateUnder72 → Bool
frickeOrbitSaturated prime =
  natEqual
    (Fricke.frickeFixedPointCount (Fricke.frickeRow prime))
    (topologicalBudget (Fricke.frickeRow prime))

saturationMatchesGenusZero :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  frickeOrbitSaturated prime ≡ Fricke.frickeGenusZero prime
saturationMatchesGenusZero Matrix.prime3 = refl
saturationMatchesGenusZero Matrix.prime5 = refl
saturationMatchesGenusZero Matrix.prime7 = refl
saturationMatchesGenusZero Matrix.prime11 = refl
saturationMatchesGenusZero Matrix.prime13 = refl
saturationMatchesGenusZero Matrix.prime17 = refl
saturationMatchesGenusZero Matrix.prime19 = refl
saturationMatchesGenusZero Matrix.prime23 = refl
saturationMatchesGenusZero Matrix.prime29 = refl
saturationMatchesGenusZero Matrix.prime31 = refl
saturationMatchesGenusZero Matrix.prime37 = refl
saturationMatchesGenusZero Matrix.prime41 = refl
saturationMatchesGenusZero Matrix.prime43 = refl
saturationMatchesGenusZero Matrix.prime47 = refl
saturationMatchesGenusZero Matrix.prime53 = refl
saturationMatchesGenusZero Matrix.prime59 = refl
saturationMatchesGenusZero Matrix.prime61 = refl
saturationMatchesGenusZero Matrix.prime67 = refl
saturationMatchesGenusZero Matrix.prime71 = refl

saturationMatchesExternalOgg :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  frickeOrbitSaturated prime ≡ Matrix.externalOggLabel prime
saturationMatchesExternalOgg prime =
  trans
    (saturationMatchesGenusZero prime)
    (Fricke.frickeGenusZeroMatchesExternalOggLabel prime)

prime37NotSaturated : frickeOrbitSaturated Matrix.prime37 ≡ false
prime37NotSaturated = refl

prime43NotSaturated : frickeOrbitSaturated Matrix.prime43 ≡ false
prime43NotSaturated = refl

prime53NotSaturated : frickeOrbitSaturated Matrix.prime53 ≡ false
prime53NotSaturated = refl

prime61NotSaturated : frickeOrbitSaturated Matrix.prime61 ≡ false
prime61NotSaturated = refl

prime67NotSaturated : frickeOrbitSaturated Matrix.prime67 ≡ false
prime67NotSaturated = refl

prime29Saturated : frickeOrbitSaturated Matrix.prime29 ≡ true
prime29Saturated = refl

prime71Saturated : frickeOrbitSaturated Matrix.prime71 ≡ true
prime71Saturated = refl

record PrimeFrickeOrbitSaturationBoundary : Set where
  field
    fixedPointSaturationConstructed : Bool
    fixedPointSaturationConstructedIsTrue :
      fixedPointSaturationConstructed ≡ true

    saturationEquivalentToGenusZeroOnFiniteScan : Bool
    saturationEquivalentToGenusZeroOnFiniteScanIsTrue :
      saturationEquivalentToGenusZeroOnFiniteScan ≡ true

    saturationMatchesExternalOggOnFiniteScan : Bool
    saturationMatchesExternalOggOnFiniteScanIsTrue :
      saturationMatchesExternalOggOnFiniteScan ≡ true

    representationRestrictionUsedToDefineSaturation : Bool
    representationRestrictionUsedToDefineSaturationIsFalse :
      representationRestrictionUsedToDefineSaturation ≡ false

    representationReductionProvedToPredictSaturation : Bool
    representationReductionProvedToPredictSaturationIsFalse :
      representationReductionProvedToPredictSaturation ≡ false

canonicalPrimeFrickeOrbitSaturationBoundary : PrimeFrickeOrbitSaturationBoundary
canonicalPrimeFrickeOrbitSaturationBoundary =
  record
    { fixedPointSaturationConstructed = true
    ; fixedPointSaturationConstructedIsTrue = refl
    ; saturationEquivalentToGenusZeroOnFiniteScan = true
    ; saturationEquivalentToGenusZeroOnFiniteScanIsTrue = refl
    ; saturationMatchesExternalOggOnFiniteScan = true
    ; saturationMatchesExternalOggOnFiniteScanIsTrue = refl
    ; representationRestrictionUsedToDefineSaturation = false
    ; representationRestrictionUsedToDefineSaturationIsFalse = refl
    ; representationReductionProvedToPredictSaturation = false
    ; representationReductionProvedToPredictSaturationIsFalse = refl
    }
