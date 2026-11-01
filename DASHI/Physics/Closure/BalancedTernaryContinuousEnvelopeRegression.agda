module DASHI.Physics.Closure.BalancedTernaryContinuousEnvelopeRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Env

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

canonicalStream : Env.Stream
canonicalStream zero = Env.neg
canonicalStream (suc zero) = Env.zer
canonicalStream (suc (suc zero)) = Env.pos
canonicalStream (suc (suc (suc n))) = Env.zer

canonicalPrefix3 : Env.TritPrefix three
canonicalPrefix3 = Env.neg Env.∷ Env.zer Env.∷ Env.pos Env.∷ Env.[]

canonicalTake3 :
  Env.take three canonicalStream ≡ canonicalPrefix3
canonicalTake3 = refl

canonicalPrefixAgreement :
  Env.PrefixAgreement three canonicalStream canonicalStream
canonicalPrefixAgreement = Env.prefix-refl three canonicalStream

canonicalPrefixAgreementDeterminesTake :
  Env.take three canonicalStream ≡ Env.take three canonicalStream
canonicalPrefixAgreementDeterminesTake =
  Env.prefixAgreement→takeEquality canonicalPrefixAgreement

canonicalFiniteEnvelope3 :
  Env.finiteEnvelope three canonicalStream
  ≡
  ((Env.envelope-zero Env.⊕ Env.digit-at Env.neg zero)
    Env.⊕ Env.digit-at Env.zer one)
    Env.⊕ Env.digit-at Env.pos two
canonicalFiniteEnvelope3 = refl

canonicalInvolutionNeg :
  Env.involution Env.neg ≡ Env.pos
canonicalInvolutionNeg = refl

canonicalInvolutionRoundTrip :
  Env.involution (Env.involution Env.neg) ≡ Env.neg
canonicalInvolutionRoundTrip = Env.involution-involutive Env.neg
