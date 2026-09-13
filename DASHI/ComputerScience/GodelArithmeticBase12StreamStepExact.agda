module DASHI.ComputerScience.GodelArithmeticBase12StreamStepExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (NonZero; nonZero; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.DivMod using
  (_/_; _%_; [m+kn]%n≡m%n; m<n⇒m%n≡m; m<n⇒m/n≡0;
   m*n/n≡m; +-distrib-/-∣ʳ)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Properties using (≤-refl)

import DASHI.ComputerScience.GodelArithmeticPrefixStreamCodecExact as Stream

base : Nat
base = 12

tokenDigit : Stream.SyntaxToken → Nat
tokenDigit Stream.natZeroToken = 1
tokenDigit Stream.natSuccToken = 2
tokenDigit Stream.termVariableToken = 3
tokenDigit Stream.termZeroToken = 4
tokenDigit Stream.termSuccessorToken = 5
tokenDigit Stream.termAddToken = 6
tokenDigit Stream.termMultiplyToken = 7
tokenDigit Stream.formulaEqualToken = 8
tokenDigit Stream.formulaFalseToken = 9
tokenDigit Stream.formulaImplyToken = 10
tokenDigit Stream.formulaForallToken = 11

digitToken : Nat → Maybe Stream.SyntaxToken
digitToken 1 = just Stream.natZeroToken
digitToken 2 = just Stream.natSuccToken
digitToken 3 = just Stream.termVariableToken
digitToken 4 = just Stream.termZeroToken
digitToken 5 = just Stream.termSuccessorToken
digitToken 6 = just Stream.termAddToken
digitToken 7 = just Stream.termMultiplyToken
digitToken 8 = just Stream.formulaEqualToken
digitToken 9 = just Stream.formulaFalseToken
digitToken 10 = just Stream.formulaImplyToken
digitToken 11 = just Stream.formulaForallToken
digitToken _ = nothing

digitTokenRoundtrip : (token : Stream.SyntaxToken) → digitToken (tokenDigit token) ≡ just token
digitTokenRoundtrip Stream.natZeroToken = refl
digitTokenRoundtrip Stream.natSuccToken = refl
digitTokenRoundtrip Stream.termVariableToken = refl
digitTokenRoundtrip Stream.termZeroToken = refl
digitTokenRoundtrip Stream.termSuccessorToken = refl
digitTokenRoundtrip Stream.termAddToken = refl
digitTokenRoundtrip Stream.termMultiplyToken = refl
digitTokenRoundtrip Stream.formulaEqualToken = refl
digitTokenRoundtrip Stream.formulaFalseToken = refl
digitTokenRoundtrip Stream.formulaImplyToken = refl
digitTokenRoundtrip Stream.formulaForallToken = refl

oneLt12 : 1 < 12
oneLt12 = s≤s (s≤s z≤n)
twoLt12 : 2 < 12
twoLt12 = s≤s (s≤s (s≤s z≤n))
threeLt12 : 3 < 12
threeLt12 = s≤s (s≤s (s≤s (s≤s z≤n)))
fourLt12 : 4 < 12
fourLt12 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
fiveLt12 : 5 < 12
fiveLt12 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
sixLt12 : 6 < 12
sixLt12 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
sevenLt12 : 7 < 12
sevenLt12 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
eightLt12 : 8 < 12
eightLt12 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
nineLt12 : 9 < 12
nineLt12 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))
tenLt12 : 10 < 12
tenLt12 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
elevenLt12 : 11 < 12
elevenLt12 = ≤-refl

tokenDigitLtBase : (token : Stream.SyntaxToken) → tokenDigit token < base
tokenDigitLtBase Stream.natZeroToken = oneLt12
tokenDigitLtBase Stream.natSuccToken = twoLt12
tokenDigitLtBase Stream.termVariableToken = threeLt12
tokenDigitLtBase Stream.termZeroToken = fourLt12
tokenDigitLtBase Stream.termSuccessorToken = fiveLt12
tokenDigitLtBase Stream.termAddToken = sixLt12
tokenDigitLtBase Stream.termMultiplyToken = sevenLt12
tokenDigitLtBase Stream.formulaEqualToken = eightLt12
tokenDigitLtBase Stream.formulaFalseToken = nineLt12
tokenDigitLtBase Stream.formulaImplyToken = tenLt12
tokenDigitLtBase Stream.formulaForallToken = elevenLt12

encodeTokenStream : List Stream.SyntaxToken → Nat
encodeTokenStream [] = 0
encodeTokenStream (token ∷ rest) = tokenDigit token + encodeTokenStream rest * base

encodedHeadRemainder :
  (token : Stream.SyntaxToken) → (rest : List Stream.SyntaxToken) →
  encodeTokenStream (token ∷ rest) % base ≡ tokenDigit token
encodedHeadRemainder token rest =
  trans ([m+kn]%n≡m%n (tokenDigit token) (encodeTokenStream rest) base)
        (m<n⇒m%n≡m (tokenDigitLtBase token))

baseDividesEncodedTail : (rest : List Stream.SyntaxToken) → base ∣ (encodeTokenStream rest * base)
baseDividesEncodedTail rest = divides (encodeTokenStream rest) refl

encodedTailQuotient :
  (token : Stream.SyntaxToken) → (rest : List Stream.SyntaxToken) →
  encodeTokenStream (token ∷ rest) / base ≡ encodeTokenStream rest
encodedTailQuotient token rest
  rewrite +-distrib-/-∣ʳ (tokenDigit token) (baseDividesEncodedTail rest)
        | m<n⇒m/n≡0 (tokenDigitLtBase token)
        | m*n/n≡m (encodeTokenStream rest) base
  = refl

recoverEncodedHead :
  (token : Stream.SyntaxToken) → (rest : List Stream.SyntaxToken) →
  digitToken (encodeTokenStream (token ∷ rest) % base) ≡ just token
recoverEncodedHead token rest rewrite encodedHeadRemainder token rest = digitTokenRoundtrip token

recoverEncodedTailCode :
  (token : Stream.SyntaxToken) → (rest : List Stream.SyntaxToken) →
  encodeTokenStream (token ∷ rest) / base ≡ encodeTokenStream rest
recoverEncodedTailCode = encodedTailQuotient

data OneStepRecoveryIsTotalNatDecoder : Set where
data Base12StreamStepImpliesRepresentability : Set where
oneStepRecoveryDoesNotYetSupplyTotalDecoder : OneStepRecoveryIsTotalNatDecoder → ⊥
oneStepRecoveryDoesNotYetSupplyTotalDecoder ()
base12ArithmeticDoesNotSupplyRepresentability : Base12StreamStepImpliesRepresentability → ⊥
base12ArithmeticDoesNotSupplyRepresentability ()

record GodelArithmeticBase12StreamStepBoundary : Set where
  constructor godelArithmeticBase12StreamStepBoundary
  field
    elevenTokenDigitsOwned : Bool
    zeroReservedForTerminator : Bool
    streamNatEncoderOwned : Bool
    headRemainderRecoveryOwned : Bool
    tailQuotientRecoveryOwned : Bool
    totalNatDecoderOwned : Bool
    formulaNatRetractionOwned : Bool
    internalRepresentabilityOwned : Bool

canonicalGodelArithmeticBase12StreamStepBoundary : GodelArithmeticBase12StreamStepBoundary
canonicalGodelArithmeticBase12StreamStepBoundary = godelArithmeticBase12StreamStepBoundary true true true true true false false false
