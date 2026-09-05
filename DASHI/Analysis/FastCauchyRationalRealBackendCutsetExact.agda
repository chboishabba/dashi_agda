module DASHI.Analysis.FastCauchyRationalRealBackendCutsetExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; _*_; _≤_; ∣_∣; _/_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using () renaming (_≤_ to _≤N_)

------------------------------------------------------------------------
-- FAST-CAUCHY RATIONAL REAL BACKEND CUTSET
--
-- Concrete pre-quotient carrier for the missing ConstructedOrderedCompleteReal
-- implementation.  The approximants are literal rationals and the error scale
-- is a dyadic sequence.  Quotient well-definedness and field/completeness laws
-- remain explicit theorem payments below.
------------------------------------------------------------------------

one : ℚ
one = + 1 / 1

half : ℚ
half = + 1 / 2

dyadic : Nat → ℚ
dyadic zero = one
dyadic (suc n) = dyadic n * half

record FastCauchyRationalSequence : Set where
  field
    approximate : Nat → ℚ
    modulus : Nat → Nat

    tailBound :
      (precision m n : Nat) →
      modulus precision ≤N m →
      modulus precision ≤N n →
      ∣ approximate m - approximate n ∣ ≤ dyadic precision

open FastCauchyRationalSequence public

------------------------------------------------------------------------
-- Extensional equality candidate: two representatives are equivalent when
-- their tails become arbitrarily dyadically close.
------------------------------------------------------------------------

record FastCauchyEquivalent
    (left right : FastCauchyRationalSequence) : Set where
  field
    cutoff : Nat → Nat

    tailEquivalent :
      (precision m n : Nat) →
      cutoff precision ≤N m →
      cutoff precision ≤N n →
      ∣ approximate left m - approximate right n ∣ ≤ dyadic precision

open FastCauchyEquivalent public

record FastCauchyQuotientLaws : Set₁ where
  field
    equivalenceReflexive :
      (x : FastCauchyRationalSequence) → FastCauchyEquivalent x x

    equivalenceSymmetric :
      {x y : FastCauchyRationalSequence} →
      FastCauchyEquivalent x y →
      FastCauchyEquivalent y x

    equivalenceTransitive :
      {x y z : FastCauchyRationalSequence} →
      FastCauchyEquivalent x y →
      FastCauchyEquivalent y z →
      FastCauchyEquivalent x z

open FastCauchyQuotientLaws public

------------------------------------------------------------------------
-- Operations are intentionally represented before quotient promotion.  Any
-- implementation of the constructed-real spine must prove representative
-- independence, order compatibility and completeness.
------------------------------------------------------------------------

record FastCauchyPreRealOperations : Set₁ where
  field
    zeroRepresentative oneRepresentative : FastCauchyRationalSequence

    add subtract multiply :
      FastCauchyRationalSequence →
      FastCauchyRationalSequence →
      FastCauchyRationalSequence

    negate absolute :
      FastCauchyRationalSequence → FastCauchyRationalSequence

    LessEqual LessThan :
      FastCauchyRationalSequence → FastCauchyRationalSequence → Set

    additionRespectsEquivalent : Set
    subtractionRespectsEquivalent : Set
    multiplicationRespectsEquivalent : Set
    negationRespectsEquivalent : Set
    absoluteRespectsEquivalent : Set
    orderRespectsEquivalent : Set

open FastCauchyPreRealOperations public

record FastCauchyCompletionReceipt
    (ops : FastCauchyPreRealOperations) : Set₁ where
  field
    QuotientReal : Set
    injectRepresentative : FastCauchyRationalSequence → QuotientReal

    quotientIdentifiesEquivalent : Set
    quotientSeparatesNonequivalent : Set

    fieldLawsDescend : Set
    orderedRingLawsDescend : Set
    absoluteValueLawsDescend : Set

    Sequence : Set
    IsCauchy : Sequence → Set
    ConvergesTo : Sequence → QuotientReal → Set

    everyCauchySequenceHasLimit :
      (s : Sequence) →
      IsCauchy s →
      Σ QuotientReal (λ x → ConvergesTo s x)

open FastCauchyCompletionReceipt public

------------------------------------------------------------------------
-- Remaining bridge to ConstructedOrderedCompleteReal.
------------------------------------------------------------------------

record FastCauchyConstructedRealBackend : Set₁ where
  field
    quotientLaws : FastCauchyQuotientLaws
    operations : FastCauchyPreRealOperations
    completion : FastCauchyCompletionReceipt operations

    constructedOrderedCompleteRealBuilt : Set
    absoluteValueTopologyBuilt : Set
    divisionSquareRootBuilt : Set
    exponentialPackageBuilt : Set

open FastCauchyConstructedRealBackend public

record FastCauchyBackendStatus : Set where
  field
    rationalApproximationCarrierOwned : Bool
    dyadicPrecisionScaleOwned : Bool
    fastCauchyPredicateOwned : Bool
    equivalenceCandidateOwned : Bool
    quotientFieldClosed : Bool
    quotientCompletenessClosed : Bool
    constructiveRealSpineInstantiated : Bool

    rationalApproximationCarrierOwnedIsTrue : rationalApproximationCarrierOwned ≡ true
    dyadicPrecisionScaleOwnedIsTrue : dyadicPrecisionScaleOwned ≡ true
    fastCauchyPredicateOwnedIsTrue : fastCauchyPredicateOwned ≡ true
    equivalenceCandidateOwnedIsTrue : equivalenceCandidateOwned ≡ true
    quotientFieldClosedIsFalse : quotientFieldClosed ≡ false
    quotientCompletenessClosedIsFalse : quotientCompletenessClosed ≡ false
    constructiveRealSpineInstantiatedIsFalse : constructiveRealSpineInstantiated ≡ false

open FastCauchyBackendStatus public

canonicalFastCauchyBackendStatus : FastCauchyBackendStatus
canonicalFastCauchyBackendStatus = record
  { rationalApproximationCarrierOwned = true
  ; dyadicPrecisionScaleOwned = true
  ; fastCauchyPredicateOwned = true
  ; equivalenceCandidateOwned = true
  ; quotientFieldClosed = false
  ; quotientCompletenessClosed = false
  ; constructiveRealSpineInstantiated = false
  ; rationalApproximationCarrierOwnedIsTrue = refl
  ; dyadicPrecisionScaleOwnedIsTrue = refl
  ; fastCauchyPredicateOwnedIsTrue = refl
  ; equivalenceCandidateOwnedIsTrue = refl
  ; quotientFieldClosedIsFalse = refl
  ; quotientCompletenessClosedIsFalse = refl
  ; constructiveRealSpineInstantiatedIsFalse = refl
  }
