module DASHI.Analysis.RiemannG21SymmetricSampleBlockReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Symmetric-sample block reduction for the G21 two-height determinant.
--
-- For a real-even taper and symmetric real samples r1,-r1,r2,-r2, a complex
-- response at height y has schematic coordinates
--
--   [ a1 , conj a1 , a2 , conj a2 ].
--
-- Pairing y with -y therefore separates into:
--
--   even channel : [ Re a1, Re a1, Re a2, Re a2 ]
--   odd channel  : [ Im a1,-Im a1, Im a2,-Im a2 ].
--
-- Consequently the four-vector transversality of two conjugate-height pairs
-- can be tested by two 2x2 minors: an even/cosh-like minor and an odd/sinh-like
-- minor.  This module owns the exact finite algebraic admission shape; the
-- analytic theorem that the actual taper gives nonzero minors remains open.
------------------------------------------------------------------------

record TwoSampleParityResponse : Set where
  constructor parityResponse
  field
    evenAtOne evenAtTwo : Nat
    oddAtOne oddAtTwo : Nat

open TwoSampleParityResponse public

record OrientedMinorCode : Set where
  constructor minorCode
  field
    positiveMonomial negativeMonomial : Nat

open OrientedMinorCode public

minor2 : TwoSampleParityResponse → TwoSampleParityResponse →
  (TwoSampleParityResponse → Nat) →
  (TwoSampleParityResponse → Nat) →
  OrientedMinorCode
minor2 x y left right =
  minorCode (left x * right y) (right x * left y)

evenMinor : TwoSampleParityResponse → TwoSampleParityResponse → OrientedMinorCode
evenMinor x y = minor2 x y evenAtOne evenAtTwo

oddMinor : TwoSampleParityResponse → TwoSampleParityResponse → OrientedMinorCode
oddMinor x y = minor2 x y oddAtOne oddAtTwo

MinorNonzero : OrientedMinorCode → Set
MinorNonzero (minorCode zero zero) = ⊥
MinorNonzero (minorCode zero (suc n)) = ⊤
MinorNonzero (minorCode (suc n) zero) = ⊤
MinorNonzero (minorCode (suc n) (suc m)) =
  suc n ≡ suc m → ⊥

record SymmetricSampleTwoHeightAdmission : Set where
  constructor symmetricSampleTwoHeightAdmission
  field
    offLineHeightResponse poleHeightResponse : TwoSampleParityResponse

    evenHeightMinorNonzero :
      MinorNonzero (evenMinor offLineHeightResponse poleHeightResponse)

    oddHeightMinorNonzero :
      MinorNonzero (oddMinor offLineHeightResponse poleHeightResponse)

    admissionReading : String

open SymmetricSampleTwoHeightAdmission public

------------------------------------------------------------------------
-- Exact positive witness: the criterion is non-vacuous.
------------------------------------------------------------------------

toyOffLineResponse : TwoSampleParityResponse
toyOffLineResponse = parityResponse 1 0 0 1

toyPoleResponse : TwoSampleParityResponse
toyPoleResponse = parityResponse 0 1 1 0

toyEvenMinor : evenMinor toyOffLineResponse toyPoleResponse ≡ minorCode 1 0
toyEvenMinor = refl

toyOddMinor : oddMinor toyOffLineResponse toyPoleResponse ≡ minorCode 0 1
toyOddMinor = refl

canonicalSymmetricSampleAdmission : SymmetricSampleTwoHeightAdmission
canonicalSymmetricSampleAdmission =
  symmetricSampleTwoHeightAdmission
    toyOffLineResponse
    toyPoleResponse
    tt
    tt
    "Finite regression witness only: symmetric sampling can simultaneously separate the even and odd response sectors of two height pairs."

------------------------------------------------------------------------
-- Exact failure witnesses keep the two sectors separate.
------------------------------------------------------------------------

evenOnlyOffLine : TwoSampleParityResponse
evenOnlyOffLine = parityResponse 1 0 1 0

evenOnlyPole : TwoSampleParityResponse
evenOnlyPole = parityResponse 0 1 2 0

evenOnlyEvenMinorPasses : MinorNonzero (evenMinor evenOnlyOffLine evenOnlyPole)
evenOnlyEvenMinorPasses = tt

evenOnlyOddMinorFails : MinorNonzero (oddMinor evenOnlyOffLine evenOnlyPole) → ⊥
evenOnlyOddMinorFails z = z

record SymmetricSampleBlockBoundary : Set where
  constructor symmetricSampleBlockBoundary
  field
    fourByFourReducedToParitySubproblems : Bool
    fourByFourReducedToParitySubproblemsIsTrue :
      fourByFourReducedToParitySubproblems ≡ true

    evenMinorAloneSuffices : Bool
    evenMinorAloneSufficesIsFalse : evenMinorAloneSuffices ≡ false

    oddMinorAloneSuffices : Bool
    oddMinorAloneSufficesIsFalse : oddMinorAloneSuffices ≡ false

    actualTaperEvenMinorDerived : Bool
    actualTaperEvenMinorDerivedIsFalse : actualTaperEvenMinorDerived ≡ false

    actualTaperOddMinorDerived : Bool
    actualTaperOddMinorDerivedIsFalse : actualTaperOddMinorDerived ≡ false

canonicalSymmetricSampleBlockBoundary : SymmetricSampleBlockBoundary
canonicalSymmetricSampleBlockBoundary =
  symmetricSampleBlockBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
