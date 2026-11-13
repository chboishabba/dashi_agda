module DASHI.Mathematics.Arithmetic.EllipticOriginalSelmerCohomologyExhaustionExact where

------------------------------------------------------------------------
-- K1–K3: ORIGINAL H¹ ALL-PLACE SELMER EXHAUSTION BY ACTUAL E(Q)[2]
--
-- Compared with finite-code exhaustiveness, this pins the genuinely
-- missing ORIGINAL-CARRIER hypotheses required to conclude that every
-- Selmer H¹ class is one of the four original torsion Kummer classes:
--
--   [1] ORIGINAL global H¹ → rational x-T square-class
--   [2] good-prime S={2,infinity} SUPPORTED-class realization
--   [3] real + Q₂ actual local Kummer necessary filters
--   [4] original torsion Kummer class ≈ its rational representative
--   [5] injectivity / faithfulness of this H¹ square-class encoding
--
-- Given those explicit proofs, this file derives an actual H¹-level
-- equality to the original torsion class. It is NOT an axiom and
-- does NOT simply define Sha as the cokernel to claim classical Sha.
--
-- This is a conditional theorem: the five concrete original-carrier
-- witnesses are NOT manufactured here. Full local cohomology K1,
-- classical E(Qbar)-valued K2/Sha[2], Mordell–Weil rank K3 and
-- analytic K4/K5 remain independent proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact as Torsion
import DASHI.Mathematics.Arithmetic.EllipticRationalKummerOpenExact as Kummer
import DASHI.Mathematics.Arithmetic.EllipticRationalTwoTorsionKummerExact as TorsionKummer
import DASHI.Mathematics.Arithmetic.RationalSquareClassSetoidExact as Square
import DASHI.Mathematics.Arithmetic.EllipticTwoDescentRoadExact as Descent
import DASHI.Mathematics.Arithmetic.EllipticRationalPlaceSelmerExact as Place
import DASHI.Mathematics.Arithmetic.EllipticSupportedSquareClassSieveExact as Sieve
import DASHI.Mathematics.Arithmetic.EllipticRationalPlaceTwoDescentProducerExact as Producer

originalPairSquareEquivalenceSym :
  ∀ {x y : Kummer.RationalSquareClassPairRepresentative} →
  Kummer.RationalSquareClassPairEquivalent x y →
  Kummer.RationalSquareClassPairEquivalent y x
originalPairSquareEquivalenceSym
    (Kummer.pair-equivalent firstEq secondEq) =
  Kummer.pair-equivalent
    (Square.square-sym firstEq)
    (Square.square-sym secondEq)

originalPairSquareEquivalenceTrans :
  ∀ {x y z : Kummer.RationalSquareClassPairRepresentative} →
  Kummer.RationalSquareClassPairEquivalent x y →
  Kummer.RationalSquareClassPairEquivalent y z →
  Kummer.RationalSquareClassPairEquivalent x z
originalPairSquareEquivalenceTrans
    (Kummer.pair-equivalent firstEq secondEq)
    (Kummer.pair-equivalent firstEq' secondEq') =
  Kummer.pair-equivalent
    (Square.square-trans firstEq firstEq')
    (Square.square-trans secondEq secondEq')

record OriginalSelmerCohomologyRealization
    (data : Place.RationalPlaceTwoDescentData
      Elliptic.curveY2EqualsX3MinusX)
    (evidence : Producer.OriginalAllPlaceSieveEvidence data) : Set₁ where
  field
    -- Actual global H¹ classes of all four original rational torsion
    -- points. Their existence and local conditions are NOT a new
    -- finite square-class coding assumption.
    actualTorsionGlobalH1 :
      Torsion.TwoTorsionCode → Place.GlobalCohomology data

    originalTorsionAllLocalKummerConditions :
      (torsion : Torsion.TwoTorsionCode) →
      Place.RationalSelmerConditions data
        (actualTorsionGlobalH1 torsion)

    -- Actual GOOD-PRIME support: an arbitrary Selmer H¹ class is
    -- square-equivalent to the literal rational S-unit pair whose
    -- signed/2-adic code the sieve computed.
    genuineSUnitSupport :
      (s : Descent.SelmerTwoElement (Place.rationalPlaceCarrier data)) →
      Kummer.RationalSquareClassPairEquivalent
        (Producer.originalGlobalSquareClass evidence
          (Descent.cohomologyClass s))
        (Sieve.supportedPairRationalRepresentative
          (Producer.originalSelmerSupportedCode evidence
            (Descent.cohomologyClass s)))

    -- Original actual torsion class agrees in the genuine global
    -- square-class setoid with the existing Kummer representative.
    actualTorsionKummerCompatibility :
      (torsion : Torsion.TwoTorsionCode) →
      Kummer.RationalSquareClassPairEquivalent
        (Producer.originalGlobalSquareClass evidence
          (actualTorsionGlobalH1 torsion))
        (TorsionKummer.torsionKummerRepresentative torsion)

    -- Genuine cohomological faithfulness, not mere equality of a
    -- 4-bit projection: different global H¹ classes cannot map to
    -- the same ORIGINAL rational square-class equivalence class.
    globalCohomologicalSquareClassFaithful :
      (x y : Place.GlobalCohomology data) →
      Kummer.RationalSquareClassPairEquivalent
        (Producer.originalGlobalSquareClass evidence x)
        (Producer.originalGlobalSquareClass evidence y) →
      x ≡ y

open OriginalSelmerCohomologyRealization public

actualTorsionSelmerElement :
  ∀ {data evidence} →
  (realization : OriginalSelmerCohomologyRealization data evidence) →
  Torsion.TwoTorsionCode →
  Descent.SelmerTwoElement (Place.rationalPlaceCarrier data)
actualTorsionSelmerElement realization torsion =
  Place.rationalConditionsGiveSelmerElement
    (actualTorsionGlobalH1 realization torsion)
    (originalTorsionAllLocalKummerConditions realization torsion)

-- The actual H¹ class of ANY original Selmer element equals the
-- ACTUAL original rational 2-torsion H¹ Kummer class. This statement
-- is not merely equality of the 4-bit sieve projection.
originalSelmerGlobalH1ExhaustedByActualTorsion :
  ∀ {data evidence} →
  (realization : OriginalSelmerCohomologyRealization data evidence) →
  (s : Descent.SelmerTwoElement (Place.rationalPlaceCarrier data)) →
  Σ Torsion.TwoTorsionCode
    (λ torsion →
      Descent.cohomologyClass s
      ≡ actualTorsionGlobalH1 realization torsion)
originalSelmerGlobalH1ExhaustedByActualTorsion
    {data} {evidence} realization s
  with Sieve.filteredCodeRationalRepresentativeIsOriginalTorsion
    (Producer.originalSelmerSupportedCode evidence
      (Descent.cohomologyClass s))
    (Producer.originalSelmerSatisfiesRealDyadicFilter evidence s)
... | torsion , literalEquality =
  torsion ,
    globalCohomologicalSquareClassFaithful realization
      (Descent.cohomologyClass s)
      (actualTorsionGlobalH1 realization torsion)
      (originalPairSquareEquivalenceTrans
        (genuineSUnitSupport realization s)
        (originalPairSquareEquivalenceTrans
          (literalEqualityGivesEquivalent literalEquality)
          (originalPairSquareEquivalenceSym
            (actualTorsionKummerCompatibility realization torsion))))
  where
    literalEqualityGivesEquivalent :
      ∀ {x y : Kummer.RationalSquareClassPairRepresentative} →
      x ≡ y → Kummer.RationalSquareClassPairEquivalent x y
    literalEqualityGivesEquivalent {x} refl =
      Kummer.pair-equivalent
        (Square.square-refl (Kummer.first x))
        (Square.square-refl (Kummer.second x))

-- Kernel-free same-object statement: the original Selmer H¹ class
-- equals the class underlying an actual torsion Selmer element.
originalSelmerElementH1ImageExhausted :
  ∀ {data evidence} →
  (realization : OriginalSelmerCohomologyRealization data evidence) →
  (s : Descent.SelmerTwoElement (Place.rationalPlaceCarrier data)) →
  Σ Torsion.TwoTorsionCode
    (λ torsion →
      Descent.cohomologyClass s
      ≡ Descent.cohomologyClass
          (actualTorsionSelmerElement realization torsion))
originalSelmerElementH1ImageExhausted realization s =
  originalSelmerGlobalH1ExhaustedByActualTorsion realization s
