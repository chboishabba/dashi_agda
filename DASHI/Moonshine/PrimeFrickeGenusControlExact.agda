module DASHI.Moonshine.PrimeFrickeGenusControlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1--8,
-- MR 417184; no DOI asserted.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Compute a finite Fricke-quotient genus defect independently on every odd
-- prime candidate below 72.  The table records exact class-number inputs and
-- verifies, without subtraction in Nat,
--
--   12*g(X0(p)) + 3*e2 + 4*e3 = p + 1,
--   r_p = h(-4p) + h(-p),
--   4*g(X0+(p)) + r_p = 2*g(X0(p)) + 2.
--
-- Here h(-p) is stored as zero on p == 1 mod 4, so the second identity is a
-- uniform finite table interface.  For p=3 the elliptic-order-three count is
-- the special value one, making the genus identity exact.
--
-- The resulting genus-zero locus on the 19 odd prime controls is
--
--   3,5,7,11,13,17,19,23,29,31,41,47,59,71,
--
-- while 37,43,53,61,67 have positive Fricke genus 1,1,1,1,2.
--
-- This is a finite exact control calculation.  It does not prove the global
-- Ogg theorem, construct modular curves internally, or identify a
-- representation-theoretic defect with the Fricke genus defect.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix

record PrimeFrickeGenusRow : Set where
  constructor prime-fricke-genus-row
  field
    candidate : Matrix.OddPrimeCandidateUnder72
    level : Nat
    levelExact : level ≡ Matrix.primeLevel candidate

    ellipticOrder2Count : Nat
    ellipticOrder3Count : Nat
    genusX0 : Nat

    classNumberMinus4p : Nat
    classNumberMinusP : Nat
    frickeFixedPointCount : Nat

    genusX0Plus : Nat

    genusX0Formula :
      12 * genusX0
      + 3 * ellipticOrder2Count
      + 4 * ellipticOrder3Count
      ≡ level + 1

    fixedPointFormula :
      frickeFixedPointCount
      ≡ classNumberMinus4p + classNumberMinusP

    riemannHurwitzFormula :
      4 * genusX0Plus + frickeFixedPointCount
      ≡ 2 * genusX0 + 2

open PrimeFrickeGenusRow public

frickeRow : Matrix.OddPrimeCandidateUnder72 → PrimeFrickeGenusRow
frickeRow Matrix.prime3 =
  prime-fricke-genus-row Matrix.prime3 3 refl 0 1 0 1 1 2 0 refl refl refl
frickeRow Matrix.prime5 =
  prime-fricke-genus-row Matrix.prime5 5 refl 2 0 0 2 0 2 0 refl refl refl
frickeRow Matrix.prime7 =
  prime-fricke-genus-row Matrix.prime7 7 refl 0 2 0 1 1 2 0 refl refl refl
frickeRow Matrix.prime11 =
  prime-fricke-genus-row Matrix.prime11 11 refl 0 0 1 3 1 4 0 refl refl refl
frickeRow Matrix.prime13 =
  prime-fricke-genus-row Matrix.prime13 13 refl 2 2 0 2 0 2 0 refl refl refl
frickeRow Matrix.prime17 =
  prime-fricke-genus-row Matrix.prime17 17 refl 2 0 1 4 0 4 0 refl refl refl
frickeRow Matrix.prime19 =
  prime-fricke-genus-row Matrix.prime19 19 refl 0 2 1 3 1 4 0 refl refl refl
frickeRow Matrix.prime23 =
  prime-fricke-genus-row Matrix.prime23 23 refl 0 0 2 3 3 6 0 refl refl refl
frickeRow Matrix.prime29 =
  prime-fricke-genus-row Matrix.prime29 29 refl 2 0 2 6 0 6 0 refl refl refl
frickeRow Matrix.prime31 =
  prime-fricke-genus-row Matrix.prime31 31 refl 0 2 2 3 3 6 0 refl refl refl
frickeRow Matrix.prime37 =
  prime-fricke-genus-row Matrix.prime37 37 refl 2 2 2 2 0 2 1 refl refl refl
frickeRow Matrix.prime41 =
  prime-fricke-genus-row Matrix.prime41 41 refl 2 0 3 8 0 8 0 refl refl refl
frickeRow Matrix.prime43 =
  prime-fricke-genus-row Matrix.prime43 43 refl 0 2 3 3 1 4 1 refl refl refl
frickeRow Matrix.prime47 =
  prime-fricke-genus-row Matrix.prime47 47 refl 0 0 4 5 5 10 0 refl refl refl
frickeRow Matrix.prime53 =
  prime-fricke-genus-row Matrix.prime53 53 refl 2 0 4 6 0 6 1 refl refl refl
frickeRow Matrix.prime59 =
  prime-fricke-genus-row Matrix.prime59 59 refl 0 0 5 9 3 12 0 refl refl refl
frickeRow Matrix.prime61 =
  prime-fricke-genus-row Matrix.prime61 61 refl 2 2 4 6 0 6 1 refl refl refl
frickeRow Matrix.prime67 =
  prime-fricke-genus-row Matrix.prime67 67 refl 0 2 5 3 1 4 2 refl refl refl
frickeRow Matrix.prime71 =
  prime-fricke-genus-row Matrix.prime71 71 refl 0 0 6 7 7 14 0 refl refl refl

isZero : Nat → Bool
isZero zero = true
isZero (suc _) = false

frickeGenusZero : Matrix.OddPrimeCandidateUnder72 → Bool
frickeGenusZero prime = isZero (genusX0Plus (frickeRow prime))

frickeGenusZeroMatchesExternalOggLabel :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  frickeGenusZero prime ≡ Matrix.externalOggLabel prime
frickeGenusZeroMatchesExternalOggLabel Matrix.prime3 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime5 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime7 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime11 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime13 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime17 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime19 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime23 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime29 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime31 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime37 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime41 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime43 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime47 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime53 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime59 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime61 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime67 = refl
frickeGenusZeroMatchesExternalOggLabel Matrix.prime71 = refl

prime37FrickeGenusIsOne : genusX0Plus (frickeRow Matrix.prime37) ≡ 1
prime37FrickeGenusIsOne = refl

prime43FrickeGenusIsOne : genusX0Plus (frickeRow Matrix.prime43) ≡ 1
prime43FrickeGenusIsOne = refl

prime53FrickeGenusIsOne : genusX0Plus (frickeRow Matrix.prime53) ≡ 1
prime53FrickeGenusIsOne = refl

prime61FrickeGenusIsOne : genusX0Plus (frickeRow Matrix.prime61) ≡ 1
prime61FrickeGenusIsOne = refl

prime67FrickeGenusIsTwo : genusX0Plus (frickeRow Matrix.prime67) ≡ 2
prime67FrickeGenusIsTwo = refl

record PrimeFrickeGenusBoundary : Set where
  field
    finiteOddPrimeGenusControlConstructed : Bool
    finiteOddPrimeGenusControlConstructedIsTrue :
      finiteOddPrimeGenusControlConstructed ≡ true

    classNumberInputsCarriedExplicitly : Bool
    classNumberInputsCarriedExplicitlyIsTrue :
      classNumberInputsCarriedExplicitly ≡ true

    internalGenusZeroColumnMatchesExternalOggOnScan : Bool
    internalGenusZeroColumnMatchesExternalOggOnScanIsTrue :
      internalGenusZeroColumnMatchesExternalOggOnScan ≡ true

    representationReductionUsedToDefineFrickeGenus : Bool
    representationReductionUsedToDefineFrickeGenusIsFalse :
      representationReductionUsedToDefineFrickeGenus ≡ false

    globalOggTheoremClaimed : Bool
    globalOggTheoremClaimedIsFalse : globalOggTheoremClaimed ≡ false

    representationModularIntertwinerClaimed : Bool
    representationModularIntertwinerClaimedIsFalse :
      representationModularIntertwinerClaimed ≡ false

canonicalPrimeFrickeGenusBoundary : PrimeFrickeGenusBoundary
canonicalPrimeFrickeGenusBoundary =
  record
    { finiteOddPrimeGenusControlConstructed = true
    ; finiteOddPrimeGenusControlConstructedIsTrue = refl
    ; classNumberInputsCarriedExplicitly = true
    ; classNumberInputsCarriedExplicitlyIsTrue = refl
    ; internalGenusZeroColumnMatchesExternalOggOnScan = true
    ; internalGenusZeroColumnMatchesExternalOggOnScanIsTrue = refl
    ; representationReductionUsedToDefineFrickeGenus = false
    ; representationReductionUsedToDefineFrickeGenusIsFalse = refl
    ; globalOggTheoremClaimed = false
    ; globalOggTheoremClaimedIsFalse = refl
    ; representationModularIntertwinerClaimed = false
    ; representationModularIntertwinerClaimedIsFalse = refl
    }
