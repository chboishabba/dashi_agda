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


sigma1InvBasis : Majorana4 → SignedMajorana4
sigma1InvBasis gamma1 = signed minus gamma2
sigma1InvBasis gamma2 = signed plus gamma1
sigma1InvBasis gamma3 = signed plus gamma3
sigma1InvBasis gamma4 = signed plus gamma4

sigma2InvBasis : Majorana4 → SignedMajorana4
sigma2InvBasis gamma1 = signed plus gamma1
sigma2InvBasis gamma2 = signed minus gamma3
sigma2InvBasis gamma3 = signed plus gamma2
sigma2InvBasis gamma4 = signed plus gamma4

sigma3InvBasis : Majorana4 → SignedMajorana4
sigma3InvBasis gamma1 = signed plus gamma1
sigma3InvBasis gamma2 = signed plus gamma2
sigma3InvBasis gamma3 = signed minus gamma4
sigma3InvBasis gamma4 = signed plus gamma3

sigma1Inv sigma2Inv sigma3Inv :
  SignedMajorana4 → SignedMajorana4
sigma1Inv (signed s m) = applyOuterSign s (sigma1InvBasis m)
sigma2Inv (signed s m) = applyOuterSign s (sigma2InvBasis m)
sigma3Inv (signed s m) = applyOuterSign s (sigma3InvBasis m)

sigma1InverseLeft :
  (x : SignedMajorana4) →
  sigma1Inv (sigma1 x) ≡ x
sigma1InverseLeft (signed plus gamma1) = refl
sigma1InverseLeft (signed plus gamma2) = refl
sigma1InverseLeft (signed plus gamma3) = refl
sigma1InverseLeft (signed plus gamma4) = refl
sigma1InverseLeft (signed minus gamma1) = refl
sigma1InverseLeft (signed minus gamma2) = refl
sigma1InverseLeft (signed minus gamma3) = refl
sigma1InverseLeft (signed minus gamma4) = refl

sigma2InverseLeft :
  (x : SignedMajorana4) →
  sigma2Inv (sigma2 x) ≡ x
sigma2InverseLeft (signed plus gamma1) = refl
sigma2InverseLeft (signed plus gamma2) = refl
sigma2InverseLeft (signed plus gamma3) = refl
sigma2InverseLeft (signed plus gamma4) = refl
sigma2InverseLeft (signed minus gamma1) = refl
sigma2InverseLeft (signed minus gamma2) = refl
sigma2InverseLeft (signed minus gamma3) = refl
sigma2InverseLeft (signed minus gamma4) = refl

sigma3InverseLeft :
  (x : SignedMajorana4) →
  sigma3Inv (sigma3 x) ≡ x
sigma3InverseLeft (signed plus gamma1) = refl
sigma3InverseLeft (signed plus gamma2) = refl
sigma3InverseLeft (signed plus gamma3) = refl
sigma3InverseLeft (signed plus gamma4) = refl
sigma3InverseLeft (signed minus gamma1) = refl
sigma3InverseLeft (signed minus gamma2) = refl
sigma3InverseLeft (signed minus gamma3) = refl
sigma3InverseLeft (signed minus gamma4) = refl

sigma1InverseRight :
  (x : SignedMajorana4) →
  sigma1 (sigma1Inv x) ≡ x
sigma1InverseRight (signed plus gamma1) = refl
sigma1InverseRight (signed plus gamma2) = refl
sigma1InverseRight (signed plus gamma3) = refl
sigma1InverseRight (signed plus gamma4) = refl
sigma1InverseRight (signed minus gamma1) = refl
sigma1InverseRight (signed minus gamma2) = refl
sigma1InverseRight (signed minus gamma3) = refl
sigma1InverseRight (signed minus gamma4) = refl

sigma2InverseRight :
  (x : SignedMajorana4) →
  sigma2 (sigma2Inv x) ≡ x
sigma2InverseRight (signed plus gamma1) = refl
sigma2InverseRight (signed plus gamma2) = refl
sigma2InverseRight (signed plus gamma3) = refl
sigma2InverseRight (signed plus gamma4) = refl
sigma2InverseRight (signed minus gamma1) = refl
sigma2InverseRight (signed minus gamma2) = refl
sigma2InverseRight (signed minus gamma3) = refl
sigma2InverseRight (signed minus gamma4) = refl

sigma3InverseRight :
  (x : SignedMajorana4) →
  sigma3 (sigma3Inv x) ≡ x
sigma3InverseRight (signed plus gamma1) = refl
sigma3InverseRight (signed plus gamma2) = refl
sigma3InverseRight (signed plus gamma3) = refl
sigma3InverseRight (signed plus gamma4) = refl
sigma3InverseRight (signed minus gamma1) = refl
sigma3InverseRight (signed minus gamma2) = refl
sigma3InverseRight (signed minus gamma3) = refl
sigma3InverseRight (signed minus gamma4) = refl

data B4Letter : Set where
  s1+ s1- s2+ s2- s3+ s3- : B4Letter

applyLetter : B4Letter → SignedMajorana4 → SignedMajorana4
applyLetter s1+ = sigma1
applyLetter s1- = sigma1Inv
applyLetter s2+ = sigma2
applyLetter s2- = sigma2Inv
applyLetter s3+ = sigma3
applyLetter s3- = sigma3Inv

data B4Word : Set where
  halt : B4Word
  _then_ : B4Letter → B4Word → B4Word

runWord : B4Word → SignedMajorana4 → SignedMajorana4
runWord halt x = x
runWord (letter then rest) x =
  runWord rest (applyLetter letter x)
