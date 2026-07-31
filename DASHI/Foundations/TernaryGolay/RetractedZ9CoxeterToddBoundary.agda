module DASHI.Foundations.TernaryGolay.RetractedZ9CoxeterToddBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Calderbank–Sloane correction boundary.
--
-- The 1996 paper claimed that a Z/9Z lift of the ternary Golay code followed
-- by Construction A produced K12.  The authors' published correction states
-- that the resulting lattice is not the Coxeter–Todd lattice, corrects the
-- determinant from 3^6 to 3^12, and rules out the stated block-9I generator
-- form.  This module makes the correction impossible to omit downstream.
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

threePowerTwelve : pow 3 12 ≡ 531441
threePowerTwelve = refl

threePowerSix : pow 3 6 ≡ 729
threePowerSix = refl

data ClaimStatus : Set where
  originalPublishedClaim : ClaimStatus
  correctedAndWithdrawnIdentification : ClaimStatus

data LatticeIdentityStatus : Set where
  distinctFromCoxeterTodd : LatticeIdentityStatus

record CorrectedZ9LiftFacts : Set where
  constructor correctedZ9LiftFacts
  field
    originalAuthor : String
    originalTitle : String
    originalDOI : String
    correctionAuthor : String
    correctionTitle : String
    correctionDOI : String
    originalStatus : ClaimStatus
    finalStatus : ClaimStatus
    minimumNorm : Nat
    determinant : Nat
    centreDensityDenominator : Nat
    latticeIdentity : LatticeIdentityStatus
    minimumNormIsFour : minimumNorm ≡ 4
    determinantIsThreePowerTwelve : determinant ≡ pow 3 12
    centreDensityDenominatorIs729 : centreDensityDenominator ≡ 729
    constructionProducesK12 : Bool
    constructionProducesK12IsFalse : constructionProducesK12 ≡ false
    correctedResultMustAccompanyOriginal : Bool
    correctedResultMustAccompanyOriginalIsTrue :
      correctedResultMustAccompanyOriginal ≡ true

open CorrectedZ9LiftFacts public

canonicalCorrectedZ9LiftFacts : CorrectedZ9LiftFacts
canonicalCorrectedZ9LiftFacts =
  correctedZ9LiftFacts
    (Sources.author Sources.calderbankSloaneClaimEntry)
    (Sources.title Sources.calderbankSloaneClaimEntry)
    "10.1109/18.485733"
    (Sources.author Sources.calderbankSloaneCorrectionEntry)
    (Sources.title Sources.calderbankSloaneCorrectionEntry)
    "10.1109/TIT.2002.806139"
    originalPublishedClaim
    correctedAndWithdrawnIdentification
    4
    531441
    729
    distinctFromCoxeterTodd
    refl
    refl
    refl
    false refl
    true refl

record Block9GeneratorFamily {IntegerMatrix Lattice K12 : Set} : Set₁ where
  field
    blockGenerator : IntegerMatrix
    generatedLattice : Lattice
    targetK12 : K12
    hasBlock9IForm : Set
    integerSquaredLengths : Set
    k12Identification : Set

open Block9GeneratorFamily public

-- This is the exact proof obligation extracted from the correction.  It is an
-- interface rather than a postulate: a downstream formal import must provide
-- the arithmetic contradiction for its chosen integer-matrix and real-lattice
-- carriers.
record NoBlock9LiftCanProduceK12
    {IntegerMatrix Lattice K12 : Set}
    (family : Block9GeneratorFamily {IntegerMatrix} {Lattice} {K12}) : Set₁ where
  field
    requiredMinimumSquaredLengthIsTwelveSqrtThree : Set
    twelveSqrtThreeIsNotInteger : Set
    integerLatticeMinimumSquaredLengthIsInteger : Set
    contradiction :
      requiredMinimumSquaredLengthIsTwelveSqrtThree →
      twelveSqrtThreeIsNotInteger →
      integerLatticeMinimumSquaredLengthIsInteger →
      k12Identification family →
      Set

open NoBlock9LiftCanProduceK12 public

record RetractionConsumptionGate : Set where
  constructor retractionConsumptionGate
  field
    originalClaimMayBeUsedAsK12Theorem : Bool
    originalClaimMayBeUsedAsK12TheoremIsFalse :
      originalClaimMayBeUsedAsK12Theorem ≡ false
    correctionAttached : Bool
    correctionAttachedIsTrue : correctionAttached ≡ true
    nonaryReductionStillValid : Bool
    nonaryReductionStillValidIsTrue : nonaryReductionStillValid ≡ true
    ternaryGolayCodeStillValid : Bool
    ternaryGolayCodeStillValidIsTrue : ternaryGolayCodeStillValid ≡ true
    k12MustUseIndependentRoute : Bool
    k12MustUseIndependentRouteIsTrue : k12MustUseIndependentRoute ≡ true

canonicalRetractionConsumptionGate : RetractionConsumptionGate
canonicalRetractionConsumptionGate =
  retractionConsumptionGate
    false refl
    true refl
    true refl
    true refl
    true refl

retractedLiftGenericReceipt : GenericReceipt.GenericReceipt
retractedLiftGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "corrected ternary-Golay Z9 lift boundary"
    "DASHI.Foundations.TernaryGolay.RetractedZ9CoxeterToddBoundary"
    "canonicalCorrectedZ9LiftFacts"
    "the original DOI, correction DOI, determinant 3^12, minimum norm 4, centre-density denominator 729, and K12 non-identification are attached"
    "the corrected lattice is not K12; any K12 theorem must enter through an independent fixed-sublattice or Eisenstein construction receipt"
    "agda -i . DASHI/Foundations/TernaryGolay/RetractedZ9CoxeterToddBoundary.agda"

retractedLiftGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim retractedLiftGenericReceipt ≡ false
retractedLiftGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse retractedLiftGenericReceipt
