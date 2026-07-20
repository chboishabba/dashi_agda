module DASHI.Foundations.PrimorialFactorAddressConcrete where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
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

a276086Prefix : Nat → Nat
a276086Prefix 0 = 1
a276086Prefix 1 = 2
a276086Prefix 2 = 3
a276086Prefix 3 = 6
a276086Prefix 4 = 9
a276086Prefix 5 = 18
a276086Prefix 6 = 5
a276086Prefix 7 = 10
a276086Prefix 8 = 15
a276086Prefix 9 = 30
a276086Prefix 10 = 45
a276086Prefix 11 = 90
a276086Prefix 12 = 25
a276086Prefix 13 = 50
a276086Prefix 14 = 75
a276086Prefix 15 = 150
a276086Prefix 16 = 225
a276086Prefix 17 = 450
a276086Prefix 18 = 125
a276086Prefix 19 = 250
a276086Prefix 20 = 375
a276086Prefix 21 = 750
a276086Prefix 22 = 1125
a276086Prefix 23 = 2250
a276086Prefix 24 = 625
a276086Prefix 25 = 1250
a276086Prefix 26 = 1875
a276086Prefix 27 = 3750
a276086Prefix 28 = 5625
a276086Prefix 29 = 11250
a276086Prefix n = 0

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
