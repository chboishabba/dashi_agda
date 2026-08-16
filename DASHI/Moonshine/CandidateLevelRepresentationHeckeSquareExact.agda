module DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Graduate Texts in Mathematics 7,
-- Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires", Seminaire Delange-Pisot-Poitou,
-- 1974/75, exp. 7.  No DOI asserted.
--
-- DASHI CONTRIBUTION
--
-- Remove Ogg-selection circularity from the representation/Hecke commuting
-- square.  The upstream scan is NOT indexed by the 15 known Ogg primes.  It is
-- indexed by the complete finite candidate lane used in the current research:
--
--   * the SU(2) spinor doublet at level 2;
--   * every SO(3) angular momentum j=0..35 at level 2*j+1.
--
-- Thus non-Ogg controls such as 9,15,21,25,27,33,43,53,67 are first-class
-- inputs.  Only downstream may an independently supplied Ogg predicate be
-- compared with a defect/closure predicate derived from the square.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin

data CandidateLevel : Set where
  spinorLevel2 : CandidateLevel
  spatialLevel : Spin.AngularMomentum0To35 → CandidateLevel

candidateLevelNat : CandidateLevel → Nat
candidateLevelNat spinorLevel2 = 2
candidateLevelNat (spatialLevel j) = Spin.jDimension j

level2IsTwo : candidateLevelNat spinorLevel2 ≡ 2
level2IsTwo = refl

levelJ4IsNine : candidateLevelNat (spatialLevel Spin.j4) ≡ 9
levelJ4IsNine = refl

levelJ7IsFifteen : candidateLevelNat (spatialLevel Spin.j7) ≡ 15
levelJ7IsFifteen = refl

levelJ21IsFortyThree : candidateLevelNat (spatialLevel Spin.j21) ≡ 43
levelJ21IsFortyThree = refl

levelJ26IsFiftyThree : candidateLevelNat (spatialLevel Spin.j26) ≡ 53
levelJ26IsFiftyThree = refl

levelJ33IsSixtySeven : candidateLevelNat (spatialLevel Spin.j33) ≡ 67
levelJ33IsSixtySeven = refl

levelJ35IsSeventyOne : candidateLevelNat (spatialLevel Spin.j35) ≡ 71
levelJ35IsSeventyOne = refl

record CandidateIndexedReductionFamily : Set₁ where
  field
    RepresentationCarrier : Set
    reduce : CandidateLevel → RepresentationCarrier → RepresentationCarrier
    reductionLabel : String

open CandidateIndexedReductionFamily public

record NatIndexedArithmeticFamily : Set₁ where
  field
    ArithmeticCarrier : Set
    arithmeticOperator : Nat → ArithmeticCarrier → ArithmeticCarrier
    arithmeticLabel : String

open NatIndexedArithmeticFamily public

record CandidateLevelIntertwiner
    (representation : CandidateIndexedReductionFamily)
    (arithmetic : NatIndexedArithmeticFamily) : Set₁ where
  field
    phi :
      RepresentationCarrier representation →
      ArithmeticCarrier arithmetic

    intertwines :
      (level : CandidateLevel) →
      (state : RepresentationCarrier representation) →
      phi (reduce representation level state)
      ≡ arithmeticOperator arithmetic
          (candidateLevelNat level)
          (phi state)

    intertwinerReceipt : String

open CandidateLevelIntertwiner public

------------------------------------------------------------------------
-- Defect-level formulation.  No equality of carriers is required.
------------------------------------------------------------------------

record CandidateDefectComparison : Set₁ where
  field
    RepresentationDefect : Set
    ArithmeticDefect : Set

    representationDefect : CandidateLevel → RepresentationDefect
    arithmeticDefect : Nat → ArithmeticDefect

    representationClosed : RepresentationDefect → Set
    arithmeticClosed : ArithmeticDefect → Set

    comparisonReceipt : String

open CandidateDefectComparison public

record ExceptionalLocusAgreement
    (comparison : CandidateDefectComparison) : Set₁ where
  field
    closesTogether :
      (level : CandidateLevel) →
      representationClosed comparison
        (representationDefect comparison level)
      ↔
      arithmeticClosed comparison
        (arithmeticDefect comparison (candidateLevelNat level))

    agreementReceipt : String

open ExceptionalLocusAgreement public

------------------------------------------------------------------------
-- Ogg comparison is downstream and separately supplied.
------------------------------------------------------------------------

record ExternalExceptionalPredicate : Set₁ where
  field
    exceptional : Nat → Set
    predicateReceipt : String

open ExternalExceptionalPredicate public

record DerivedExceptionalLocusMatchesExternal
    (comparison : CandidateDefectComparison)
    (external : ExternalExceptionalPredicate) : Set₁ where
  field
    representationMatchesExternal :
      (level : CandidateLevel) →
      representationClosed comparison
        (representationDefect comparison level)
      ↔ exceptional external (candidateLevelNat level)

    arithmeticMatchesExternal :
      (level : CandidateLevel) →
      arithmeticClosed comparison
        (arithmeticDefect comparison (candidateLevelNat level))
      ↔ exceptional external (candidateLevelNat level)

    matchingReceipt : String

open DerivedExceptionalLocusMatchesExternal public

record CandidateLevelSquareBoundary : Set where
  field
    scanDomainDefinedFromKnownOggList : Bool
    scanDomainDefinedFromKnownOggListIsFalse :
      scanDomainDefinedFromKnownOggList ≡ false

    nonOggControlsAreFirstClassInputs : Bool
    nonOggControlsAreFirstClassInputsIsTrue :
      nonOggControlsAreFirstClassInputs ≡ true

    carrierEqualityRequired : Bool
    carrierEqualityRequiredIsFalse : carrierEqualityRequired ≡ false

    classicalIntertwinerConstructed : Bool
    classicalIntertwinerConstructedIsFalse :
      classicalIntertwinerConstructed ≡ false

    exceptionalLocusEqualityConstructed : Bool
    exceptionalLocusEqualityConstructedIsFalse :
      exceptionalLocusEqualityConstructed ≡ false

canonicalCandidateLevelSquareBoundary : CandidateLevelSquareBoundary
canonicalCandidateLevelSquareBoundary =
  record
    { scanDomainDefinedFromKnownOggList = false
    ; scanDomainDefinedFromKnownOggListIsFalse = refl
    ; nonOggControlsAreFirstClassInputs = true
    ; nonOggControlsAreFirstClassInputsIsTrue = refl
    ; carrierEqualityRequired = false
    ; carrierEqualityRequiredIsFalse = refl
    ; classicalIntertwinerConstructed = false
    ; classicalIntertwinerConstructedIsFalse = refl
    ; exceptionalLocusEqualityConstructed = false
    ; exceptionalLocusEqualityConstructedIsFalse = refl
    }
