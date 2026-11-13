module DASHI.Mathematics.Arithmetic.EllipticRationalPlaceTwoDescentProducerExact where

------------------------------------------------------------------------
-- K1→K3: ORIGINAL ALL-PLACE AGDA SELMER TO FINITE TORSION CODE
--
-- This is a source-preserving bridge from the ACTUAL existing Agda
-- RationalPlaceTwoDescentData and SelmerTwoElement owners to the
-- 16→8→4 combinatorial sieve on S={2,infinity}.
--
-- The bridge REQUIRES, and does not pretend to prove:
-- (a) original H¹(E[2]) realization in rational square classes;
-- (b) an actual prime-2 place and correct local image predicate;
-- (c) real diagonal-sign and dyadic v₂ parity necessary conditions.
--
-- It proves a genuine term-level implication:
--   all-place Selmer element + actual arithmetic sieve producers
--   → original finite rational two-torsion code with matching bits.
--
-- It does NOT identify a finite code with a complete global
-- square class, the original Mordell–Weil quotient, or classical Sha.
-- The missing injective same-object projection and H¹ exactness
-- remain named original K1/K2/K3 gates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact as Torsion
import DASHI.Mathematics.Arithmetic.EllipticCurveFiniteTwoDescentSeedExact as Seed
import DASHI.Mathematics.Arithmetic.EllipticRationalKummerOpenExact as Kummer
import DASHI.Mathematics.Arithmetic.EllipticTwoDescentRoadExact as Descent
import DASHI.Mathematics.Arithmetic.EllipticRationalPlaceSelmerExact as Place
import DASHI.Mathematics.Arithmetic.EllipticSupportedSquareClassSieveExact as Sieve
import DASHI.Mathematics.Arithmetic.EllipticActualDyadicPrimePlaceExact as Dyadic

record OriginalAllPlaceSieveEvidence
    (data : Place.RationalPlaceTwoDescentData
      Elliptic.curveY2EqualsX3MinusX) : Set₁ where
  field
    fourBitProjection : Sieve.OriginalFourBitProjection

    -- Original global H¹ classes must be connected to the genuine
    -- rational-square-class setoid, not replaced by new Bool codes.
    originalGlobalSquareClass :
      Place.GlobalCohomology data →
      Kummer.RationalSquareClassPairRepresentative

    -- The prime-2 place is now the source-written canonical Agda
    -- inhabitant Dyadic.actualDyadicFinitePrime, not a record field.

    -- Mathematical source requirements, not assumed status flags.
    archimedeanNecessary :
      (x : Place.GlobalCohomology data) →
      Place.InfiniteKummerImage data (Place.localizeInfinity data x) →
      Sieve.firstNegative
        (Sieve.projectOriginalSquareClassPair fourBitProjection
          (originalGlobalSquareClass x))
      ≡ Sieve.secondNegative
        (Sieve.projectOriginalSquareClassPair fourBitProjection
          (originalGlobalSquareClass x))

    dyadicNecessary :
      (x : Place.GlobalCohomology data) →
      Place.FiniteKummerImage data Dyadic.actualDyadicFinitePrime
        (Place.localizeFinite data Dyadic.actualDyadicFinitePrime x) →
      Sieve.firstOddAtTwo
        (Sieve.projectOriginalSquareClassPair fourBitProjection
          (originalGlobalSquareClass x))
      ≡ Torsion.bit0

open OriginalAllPlaceSieveEvidence public

originalSelmerSupportedCode :
  ∀ {data} →
  OriginalAllPlaceSieveEvidence data →
  Place.GlobalCohomology data →
  Sieve.SupportedSquareClassPairCode
originalSelmerSupportedCode evidence x =
  Sieve.projectOriginalSquareClassPair
    (fourBitProjection evidence)
    (originalGlobalSquareClass evidence x)

-- The abstract Selmer compiler already owns all-place membership;
-- the two required arithmetic consequences are extracted at the
-- ACTUAL real and ACTUAL specified dyadic places.
originalSelmerSatisfiesRealDyadicFilter :
  ∀ {data} →
  (evidence : OriginalAllPlaceSieveEvidence data) →
  (s : Descent.SelmerTwoElement (Place.rationalPlaceCarrier data)) →
  Sieve.RealAndDyadicNecessaryFilter
    (originalSelmerSupportedCode evidence
      (Descent.cohomologyClass s))
originalSelmerSatisfiesRealDyadicFilter evidence s =
  Sieve.filtered
    (archimedeanNecessary evidence
      (Descent.cohomologyClass s)
      (Descent.satisfiesEveryLocalCondition s Place.infinitePlace))
    (dyadicNecessary evidence
      (Descent.cohomologyClass s)
      (Descent.satisfiesEveryLocalCondition s
        Dyadic.actualDyadicRationalPlace))

-- The finite exhaustive K1→K3 weld. It does not infer that the
-- global H¹ class equals the rational torsion Kummer class; such
-- equality needs the actual support/faithfulness theorem.
originalAllPlaceSelmerProjectsToTorsionCode :
  ∀ {data} →
  (evidence : OriginalAllPlaceSieveEvidence data) →
  (s : Descent.SelmerTwoElement (Place.rationalPlaceCarrier data)) →
  Σ Torsion.TwoTorsionCode
    (λ torsion →
      Sieve.torsionSupportedCode torsion
      ≡ originalSelmerSupportedCode evidence
          (Descent.cohomologyClass s))
originalAllPlaceSelmerProjectsToTorsionCode evidence s =
  Sieve.filteredSupportedCodeHasTorsionPreimage
    (originalSelmerSupportedCode evidence
      (Descent.cohomologyClass s))
    (originalSelmerSatisfiesRealDyadicFilter evidence s)

-- Original four-point seed recovered from the projection:
-- NOT a synthetic replacement for rational square classes.
originalAllPlaceSelmerProjectsToFiniteKummerSeed :
  ∀ {data} →
  (evidence : OriginalAllPlaceSieveEvidence data) →
  (s : Descent.SelmerTwoElement (Place.rationalPlaceCarrier data)) →
  Σ Torsion.TwoTorsionCode
    (λ torsion →
      Seed.finiteKummerMap torsion ≡
        Seed.squareClassPair
          (Sieve.firstNegative
            (originalSelmerSupportedCode evidence
              (Descent.cohomologyClass s)))
          (Sieve.secondOddAtTwo
            (originalSelmerSupportedCode evidence
              (Descent.cohomologyClass s))))
originalAllPlaceSelmerProjectsToFiniteKummerSeed evidence s =
  Sieve.filteredSupportedCodeRecoversFiniteSeed
    (originalSelmerSupportedCode evidence
      (Descent.cohomologyClass s))
    (originalSelmerSatisfiesRealDyadicFilter evidence s)
