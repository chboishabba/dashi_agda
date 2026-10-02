module DASHI.Physics.CondensedMatter.MajoranaB4BraidExact where

------------------------------------------------------------------------
-- Exact four-Majorana signed braid action.
--
-- Adjacent exchanges:
--   sigma1 exchanges gamma1,gamma2 with the fermionic sign;
--   sigma2 exchanges gamma2,gamma3;
--   sigma3 exchanges gamma3,gamma4.
--
-- Proved:
--   sigma1 sigma2 sigma1 = sigma2 sigma1 sigma2
--   sigma2 sigma3 sigma2 = sigma3 sigma2 sigma3
--   sigma1 sigma3 = sigma3 sigma1
-- and explicit noncommutativity of adjacent generators.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data Sign : Set where
  plus minus : Sign

flip : Sign → Sign
flip plus = minus
flip minus = plus

data Majorana4 : Set where
  gamma1 gamma2 gamma3 gamma4 : Majorana4

record SignedMajorana4 : Set where
  constructor signed
  field
    sign : Sign
    mode : Majorana4

open SignedMajorana4 public

negateSigned : SignedMajorana4 → SignedMajorana4
negateSigned (signed s m) = signed (flip s) m

applyOuterSign : Sign → SignedMajorana4 → SignedMajorana4
applyOuterSign plus x = x
applyOuterSign minus x = negateSigned x

sigma1Basis : Majorana4 → SignedMajorana4
sigma1Basis gamma1 = signed plus gamma2
sigma1Basis gamma2 = signed minus gamma1
sigma1Basis gamma3 = signed plus gamma3
sigma1Basis gamma4 = signed plus gamma4

sigma2Basis : Majorana4 → SignedMajorana4
sigma2Basis gamma1 = signed plus gamma1
sigma2Basis gamma2 = signed plus gamma3
sigma2Basis gamma3 = signed minus gamma2
sigma2Basis gamma4 = signed plus gamma4

sigma3Basis : Majorana4 → SignedMajorana4
sigma3Basis gamma1 = signed plus gamma1
sigma3Basis gamma2 = signed plus gamma2
sigma3Basis gamma3 = signed plus gamma4
sigma3Basis gamma4 = signed minus gamma3

sigma1 sigma2 sigma3 : SignedMajorana4 → SignedMajorana4
sigma1 (signed s m) = applyOuterSign s (sigma1Basis m)
sigma2 (signed s m) = applyOuterSign s (sigma2Basis m)
sigma3 (signed s m) = applyOuterSign s (sigma3Basis m)

yangBaxter12 :
  (x : SignedMajorana4) →
  sigma1 (sigma2 (sigma1 x))
  ≡ sigma2 (sigma1 (sigma2 x))
yangBaxter12 (signed plus gamma1) = refl
yangBaxter12 (signed plus gamma2) = refl
yangBaxter12 (signed plus gamma3) = refl
yangBaxter12 (signed plus gamma4) = refl
yangBaxter12 (signed minus gamma1) = refl
yangBaxter12 (signed minus gamma2) = refl
yangBaxter12 (signed minus gamma3) = refl
yangBaxter12 (signed minus gamma4) = refl

yangBaxter23 :
  (x : SignedMajorana4) →
  sigma2 (sigma3 (sigma2 x))
  ≡ sigma3 (sigma2 (sigma3 x))
yangBaxter23 (signed plus gamma1) = refl
yangBaxter23 (signed plus gamma2) = refl
yangBaxter23 (signed plus gamma3) = refl
yangBaxter23 (signed plus gamma4) = refl
yangBaxter23 (signed minus gamma1) = refl
yangBaxter23 (signed minus gamma2) = refl
yangBaxter23 (signed minus gamma3) = refl
yangBaxter23 (signed minus gamma4) = refl

farCommutation13 :
  (x : SignedMajorana4) →
  sigma1 (sigma3 x) ≡ sigma3 (sigma1 x)
farCommutation13 (signed plus gamma1) = refl
farCommutation13 (signed plus gamma2) = refl
farCommutation13 (signed plus gamma3) = refl
farCommutation13 (signed plus gamma4) = refl
farCommutation13 (signed minus gamma1) = refl
farCommutation13 (signed minus gamma2) = refl
farCommutation13 (signed minus gamma3) = refl
farCommutation13 (signed minus gamma4) = refl

gamma2NotGamma3 :
  signed plus gamma2 ≡ signed plus gamma3 →
  ⊥
gamma2NotGamma3 ()

adjacent12Noncommuting :
  ((x : SignedMajorana4) →
    sigma1 (sigma2 x) ≡ sigma2 (sigma1 x))
  →
  ⊥
adjacent12Noncommuting commute =
  gamma2NotGamma3 (commute (signed plus gamma1))

data B4Generator : Set where
  s1 s2 s3 : B4Generator

applyGenerator : B4Generator → SignedMajorana4 → SignedMajorana4
applyGenerator s1 = sigma1
applyGenerator s2 = sigma2
applyGenerator s3 = sigma3
