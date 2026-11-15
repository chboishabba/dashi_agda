module DASHI.Physics.YangMills.BalabanRegular240PointwisePermutationModuleExact where

-- Exact source/target scalar coefficient transport over the SAME
-- regular 240 Round56 support×F4-half incidence equivalence.
-- Values are proof-insensitive: the observable depends only on the
-- original grid cell (respectively the encoded support/sign pair),
-- never on the particular Nat equality witness of regularity.
--
-- This is a generic pointwise equivalence preserving any supplied
-- additive/scalar operation. It does not assume a field, supply an
-- F3 matrix rank theorem, or prove analytic source-integrand symmetry.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
import DASHI.Physics.YangMills.BalabanRegular240SupportHalfExact as R

record OriginalCoefficients (K : Set) : Set₁ where
  field
    value : R.Regular240 → K
    proofInsensitive :
      (x y : R.Regular240) →
      R.original x ≡ R.original y →
      value x ≡ value y
open OriginalCoefficients public

record EncodedCoefficients (K : Set) : Set₁ where
  field
    encodedValue : R.SupportHalf240 → K
    proofInsensitiveEncoded :
      (x y : R.SupportHalf240) →
      R.supportSigns x ≡ R.supportSigns y →
      encodedValue x ≡ encodedValue y
open EncodedCoefficients public

-- Pull the original coefficient along the concrete encoded decoder.
encodeCoefficients :
  {K : Set} → OriginalCoefficients K → EncodedCoefficients K
encodeCoefficients f = record
  { encodedValue = λ p → value f (R.decode240 p)
  ; proofInsensitiveEncoded = λ p q eq →
      proofInsensitive f (R.decode240 p) (R.decode240 q)
        (cong R.decode256 eq)
  }

-- Conversely pull the encoded coefficient back along original encoder.
decodeCoefficients :
  {K : Set} → EncodedCoefficients K → OriginalCoefficients K
decodeCoefficients f = record
  { value = λ c → encodedValue f (R.encode240 c)
  ; proofInsensitive = λ x y eq →
      proofInsensitiveEncoded f (R.encode240 x) (R.encode240 y)
        (cong R.encode256 eq)
  }

-- Two real inverse laws (POINTWISE, thus no function extensionality
-- or hidden Agda proof irrelevance assumption is needed).
originalCoefficientRoundTrip :
  {K : Set} (f : OriginalCoefficients K) (c : R.Regular240) →
  value (decodeCoefficients (encodeCoefficients f)) c ≡ value f c
originalCoefficientRoundTrip f c =
  proofInsensitive f (R.decode240 (R.encode240 c)) c
    (R.regularOriginalRoundTrip c)

encodedCoefficientRoundTrip :
  {K : Set} (f : EncodedCoefficients K) (p : R.SupportHalf240) →
  encodedValue (encodeCoefficients (decodeCoefficients f)) p ≡
  encodedValue f p
encodedCoefficientRoundTrip f p =
  proofInsensitiveEncoded f (R.encode240 (R.decode240 p)) p
    (R.regularPackedRoundTrip p)

-- Linear operations are performed POINTWISE. No ungrounded field
-- structure is assumed; if the consumer K is F3 with its genuine
-- addition/multiplication then these are concrete F3-linear maps.
combineOriginal :
  {K : Set} (_⊕_ : K → K → K) →
  OriginalCoefficients K → OriginalCoefficients K →
  OriginalCoefficients K
combineOriginal _⊕_ f g = record
  { value = λ c → value f c ⊕ value g c
  ; proofInsensitive = λ x y eq →
      cong₂ _⊕_ (proofInsensitive f x y eq)
                  (proofInsensitive g x y eq)
  }

combineEncoded :
  {K : Set} (_⊕_ : K → K → K) →
  EncodedCoefficients K → EncodedCoefficients K →
  EncodedCoefficients K
combineEncoded _⊕_ f g = record
  { encodedValue = λ p → encodedValue f p ⊕ encodedValue g p
  ; proofInsensitiveEncoded = λ x y eq →
      cong₂ _⊕_ (proofInsensitiveEncoded f x y eq)
                  (proofInsensitiveEncoded g x y eq)
  }

encodePreservesPointwiseAddition :
  {K : Set} (_⊕_ : K → K → K)
  (f g : OriginalCoefficients K) (p : R.SupportHalf240) →
  encodedValue (encodeCoefficients (combineOriginal _⊕_ f g)) p ≡
  encodedValue (combineEncoded _⊕_
    (encodeCoefficients f) (encodeCoefficients g)) p
encodePreservesPointwiseAddition _⊕_ f g p = refl

decodePreservesPointwiseAddition :
  {K : Set} (_⊕_ : K → K → K)
  (f g : EncodedCoefficients K) (c : R.Regular240) →
  value (decodeCoefficients (combineEncoded _⊕_ f g)) c ≡
  value (combineOriginal _⊕_
    (decodeCoefficients f) (decodeCoefficients g)) c
decodePreservesPointwiseAddition _⊕_ f g c = refl

mapOriginal :
  {K L : Set} (h : K → L) →
  OriginalCoefficients K → OriginalCoefficients L
mapOriginal h f = record
  { value = λ c → h (value f c)
  ; proofInsensitive = λ x y eq →
      cong h (proofInsensitive f x y eq)
  }

mapEncoded :
  {K L : Set} (h : K → L) →
  EncodedCoefficients K → EncodedCoefficients L
mapEncoded h f = record
  { encodedValue = λ c → h (encodedValue f c)
  ; proofInsensitiveEncoded = λ x y eq →
      cong h (proofInsensitiveEncoded f x y eq)
  }

encodeCommutesWithAnyScalarOperation :
  {K : Set} (operation : K → K)
  (f : OriginalCoefficients K) (p : R.SupportHalf240) →
  encodedValue (encodeCoefficients (mapOriginal operation f)) p ≡
  encodedValue (mapEncoded operation (encodeCoefficients f)) p
encodeCommutesWithAnyScalarOperation operation f p = refl

-- Correct scope: for proof-insensitive pointwise coefficients, encoding
-- is an additive (and scalar-operation-preserving) source identification.
-- It does not identify the original physical scalar with an E8 or F4
-- analytic integrand. Character tests and physical invariance are separate.
