module DASHI.Foundations.PrimorialFactorAddressConcrete where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)

pow : Nat → Nat → Nat
pow b zero = 1
pow b (suc n) = b * pow b n

record PrimorialDigits4 : Set where
  constructor primorialDigits4
  field
    digit2 digit3 digit5 digit7 : Nat

open PrimorialDigits4 public

primorialDecode4 : PrimorialDigits4 → Nat
primorialDecode4 d =
  digit2 d + 2 * digit3 d + 6 * digit5 d + 30 * digit7 d

primeExponentProduct4 : PrimorialDigits4 → Nat
primeExponentProduct4 d =
  pow 2 (digit2 d) *
  (pow 3 (digit3 d) *
  (pow 5 (digit5 d) * pow 7 (digit7 d)))

record FactorVec4 : Set where
  constructor factorVec4
  field
    exponent2 exponent3 exponent5 exponent7 : Nat

fromPrimorialDigits : PrimorialDigits4 → FactorVec4
fromPrimorialDigits d =
  factorVec4 (digit2 d) (digit3 d) (digit5 d) (digit7 d)

example24Digits : PrimorialDigits4
example24Digits = primorialDigits4 0 0 4 0

example24Decode : primorialDecode4 example24Digits ≡ 24
example24Decode = refl

example24Product : primeExponentProduct4 example24Digits ≡ 625
example24Product = refl

example35Digits : PrimorialDigits4
example35Digits = primorialDigits4 1 2 0 1

example35Decode : primorialDecode4 example35Digits ≡ 35
example35Decode = refl

example35Product : primeExponentProduct4 example35Digits ≡ 126
example35Product = refl

a276086PrefixList : List Nat
a276086PrefixList =
  1 ∷ 2 ∷ 3 ∷ 6 ∷ 9 ∷ 18 ∷ 5 ∷ 10 ∷ 15 ∷ 30 ∷
  45 ∷ 90 ∷ 25 ∷ 50 ∷ 75 ∷ 150 ∷ 225 ∷ 450 ∷ 125 ∷ 250 ∷
  375 ∷ 750 ∷ 1125 ∷ 2250 ∷ 625 ∷ 1250 ∷ 1875 ∷ 3750 ∷ 5625 ∷ 11250 ∷ []

nthDef : Nat → Nat → List Nat → Nat
nthDef def zero (x ∷ _) = x
nthDef def (suc n) (_ ∷ xs) = nthDef def n xs
nthDef def _ [] = def

a276086Prefix : Nat → Nat
a276086Prefix n = nthDef 0 n a276086PrefixList

a276087Prefix : Nat → Nat
a276087Prefix 0 = 2
a276087Prefix 1 = 3
a276087Prefix 2 = 6
a276087Prefix 3 = 5
a276087Prefix 4 = 30
a276087Prefix 5 = 125
a276087Prefix 6 = 18
a276087Prefix 7 = 45
a276087Prefix 8 = 150
a276087Prefix 9 = 7
a276087Prefix n = 0

prefix086At24 : a276086Prefix 24 ≡ 625
prefix086At24 = refl

prefix087At5 : a276087Prefix 5 ≡ 125
prefix087At5 = refl

record GeneralPrimorialAlgorithmAuthority : Set₁ where
  field
    primeAt : Nat → Nat
    mixedRadixDigit : Nat → Nat → Nat
    a276086 : Nat → Nat
    digitsWithinPrimeRadix : Set
    reconstructionTheorem : Set
    exponentProductTheorem : Set
    a276087IsTwofoldComposition : Set
    factorVecTransportSound : Set
    orbitClassification : Set
    fixedPointClassification : Set
    mdlComparisonEvidence : Set

record PrimorialFactorAddressConcreteReceipt : Set where
  constructor mkPrimorialFactorAddressConcreteReceipt
  field
    boundedDigitDecodeChecked : Bool
    boundedPrimeProductChecked : Bool
    boundedFactorVecTransportChecked : Bool
    sourceBackedA276086PrefixChecked : Bool
    sourceBackedA276087PrefixChecked : Bool
    generalAlgorithmPromotedFromFallbackTable : Bool
    generalAlgorithmPromotedFromFallbackTableIsFalse :
      generalAlgorithmPromotedFromFallbackTable ≡ false
    globalOrbitClaimsPromoted : Bool
    globalOrbitClaimsPromotedIsFalse : globalOrbitClaimsPromoted ≡ false
    compressionAdvantageClaimedWithoutBenchmark : Bool
    compressionAdvantageClaimedWithoutBenchmarkIsFalse :
      compressionAdvantageClaimedWithoutBenchmark ≡ false
    source : String
    interpretation : String

primorialFactorAddressConcreteReceipt :
  PrimorialFactorAddressConcreteReceipt
primorialFactorAddressConcreteReceipt =
  mkPrimorialFactorAddressConcreteReceipt
    true true true true true
    false refl false refl false refl
    "OEIS A276086 and A276087"
    "four-prime mixed-radix examples and source-backed finite prefixes are executable; the unbounded prime algorithm, orbit theory and MDL benefit remain separately receipted"
