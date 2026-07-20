module DASHI.Foundations.PrimorialFactorAddressBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-labelled interface for the primorial-base exponent map associated in
-- the supplied material with OEIS A276086, and its twofold composition A276087.
--
-- The exact sequence values are not fabricated here.  A concrete source-backed
-- implementation must supply digit extraction and value agreement receipts.

record PrimorialExponentFunction : Set₁ where
  field
    apply : Nat → Nat
    primorialDigits : Nat → List Nat
    exponentAddress : Nat → List Nat
    digitToExponentAgreement : Set
    sourceAgreement : Set

open PrimorialExponentFunction public

twofoldApply : PrimorialExponentFunction → Nat → Nat
twofoldApply f n = apply f (apply f n)

twofoldDefinition :
  (f : PrimorialExponentFunction) →
  (n : Nat) →
  twofoldApply f n ≡ apply f (apply f n)
twofoldDefinition f n = refl

record FactorAddress : Set where
  constructor factorAddress
  field
    exponents : List Nat
    sourceInteger : Nat
    addressLabel : String

record FactorVectorBridge : Set₁ where
  field
    FactorVec : Set
    fromAddress : FactorAddress → FactorVec
    toAddress : FactorVec → FactorAddress
    roundTrip : Set
    primeAxesDeclared : Set
    zeroExponentMeaningDeclared : Set

record PrimorialOrbitStudy : Set₁ where
  field
    exponentFunction : PrimorialExponentFunction
    OrbitInvariant DescriptionLength : Set
    orbit : Nat → Nat → Nat
    orbitLaw : Set
    invariantTest : Set
    cycleTest : Set
    descriptionLength : Nat → DescriptionLength
    mdlTrendTest : Set

record LogisticPrimorialBridge : Set₁ where
  field
    LogisticState SymbolicItinerary : Set
    itinerary : LogisticState → SymbolicItinerary
    itineraryToInteger : SymbolicItinerary → Nat
    exponentFunction : PrimorialExponentFunction
    mappedAddress : SymbolicItinerary → Nat
    mappingLaw : Set
    empiricalUsefulnessReceipt : Set

record PrimorialFactorAddressBoundary : Set where
  constructor primorialFactorAddressBoundary
  field
    A276086LabelRecorded : String
    A276087LabelRecorded : String
    twofoldCompositionChecked : Bool
    exactSequenceValuesImplemented : Bool
    exactSequenceValuesImplementedIsFalse : exactSequenceValuesImplemented ≡ false
    logisticBranchesAutomaticallyIndexed : Bool
    logisticBranchesAutomaticallyIndexedIsFalse :
      logisticBranchesAutomaticallyIndexed ≡ false
    systemicRebirthTheoremClaimed : Bool
    systemicRebirthTheoremClaimedIsFalse : systemicRebirthTheoremClaimed ≡ false
    sourceBackedImplementationRequired : Bool
    interpretation : String

canonicalPrimorialFactorAddressBoundary : PrimorialFactorAddressBoundary
canonicalPrimorialFactorAddressBoundary =
  primorialFactorAddressBoundary
    "OEIS A276086: primorial-base exponent function, as named in the supplied material"
    "OEIS A276087: twofold application of the A276086-style function, as named in the supplied material"
    true
    false refl
    false refl
    false refl
    true
    "primorial digits may address prime-exponent vectors and their iterates, but exact OEIS values and any logistic/MDL usefulness require source-backed implementations and tests"
