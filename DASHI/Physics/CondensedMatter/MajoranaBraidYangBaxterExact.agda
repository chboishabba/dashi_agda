module DASHI.Physics.CondensedMatter.MajoranaBraidYangBaxterExact where

------------------------------------------------------------------------
-- Exact finite Majorana braid action on three generators.
--
-- DASHI DERIVATION:
--   sigma1 : gamma1 -> gamma2, gamma2 -> -gamma1, gamma3 -> gamma3
--   sigma2 : gamma1 -> gamma1, gamma2 -> gamma3, gamma3 -> -gamma2
--
-- We prove:
--   * inverse actions for sigma1 and sigma2;
--   * Artin/Yang-Baxter relation sigma1 sigma2 sigma1
--       = sigma2 sigma1 sigma2;
--   * explicit noncommutativity sigma1 sigma2 /= sigma2 sigma1.
--
-- This is an exact signed-generator braid representation.  It is not yet
-- a Hilbert-space unitary representation or a physical YbSb2 braid device.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data Sign : Set where
  plus minus : Sign

flip : Sign → Sign
flip plus = minus
flip minus = plus

data Majorana3 : Set where
  gamma1 gamma2 gamma3 : Majorana3

record SignedMajorana : Set where
  constructor signed
  field
    sign : Sign
    mode : Majorana3

open SignedMajorana public

negateSigned : SignedMajorana → SignedMajorana
negateSigned (signed s m) = signed (flip s) m

sigma1Basis : Majorana3 → SignedMajorana
sigma1Basis gamma1 = signed plus gamma2
sigma1Basis gamma2 = signed minus gamma1
sigma1Basis gamma3 = signed plus gamma3

sigma2Basis : Majorana3 → SignedMajorana
sigma2Basis gamma1 = signed plus gamma1
sigma2Basis gamma2 = signed plus gamma3
sigma2Basis gamma3 = signed minus gamma2

applyOuterSign : Sign → SignedMajorana → SignedMajorana
applyOuterSign plus x = x
applyOuterSign minus x = negateSigned x

sigma1 : SignedMajorana → SignedMajorana
sigma1 (signed s m) = applyOuterSign s (sigma1Basis m)

sigma2 : SignedMajorana → SignedMajorana
sigma2 (signed s m) = applyOuterSign s (sigma2Basis m)

sigma1InvBasis : Majorana3 → SignedMajorana
sigma1InvBasis gamma1 = signed minus gamma2
sigma1InvBasis gamma2 = signed plus gamma1
sigma1InvBasis gamma3 = signed plus gamma3

sigma2InvBasis : Majorana3 → SignedMajorana
sigma2InvBasis gamma1 = signed plus gamma1
sigma2InvBasis gamma2 = signed minus gamma3
sigma2InvBasis gamma3 = signed plus gamma2

sigma1Inv : SignedMajorana → SignedMajorana
sigma1Inv (signed s m) = applyOuterSign s (sigma1InvBasis m)

sigma2Inv : SignedMajorana → SignedMajorana
sigma2Inv (signed s m) = applyOuterSign s (sigma2InvBasis m)

sigma1InverseLeft :
  (x : SignedMajorana) →
  sigma1Inv (sigma1 x) ≡ x
sigma1InverseLeft (signed plus gamma1) = refl
sigma1InverseLeft (signed plus gamma2) = refl
sigma1InverseLeft (signed plus gamma3) = refl
sigma1InverseLeft (signed minus gamma1) = refl
sigma1InverseLeft (signed minus gamma2) = refl
sigma1InverseLeft (signed minus gamma3) = refl

sigma1InverseRight :
  (x : SignedMajorana) →
  sigma1 (sigma1Inv x) ≡ x
sigma1InverseRight (signed plus gamma1) = refl
sigma1InverseRight (signed plus gamma2) = refl
sigma1InverseRight (signed plus gamma3) = refl
sigma1InverseRight (signed minus gamma1) = refl
sigma1InverseRight (signed minus gamma2) = refl
sigma1InverseRight (signed minus gamma3) = refl

sigma2InverseLeft :
  (x : SignedMajorana) →
  sigma2Inv (sigma2 x) ≡ x
sigma2InverseLeft (signed plus gamma1) = refl
sigma2InverseLeft (signed plus gamma2) = refl
sigma2InverseLeft (signed plus gamma3) = refl
sigma2InverseLeft (signed minus gamma1) = refl
sigma2InverseLeft (signed minus gamma2) = refl
sigma2InverseLeft (signed minus gamma3) = refl

sigma2InverseRight :
  (x : SignedMajorana) →
  sigma2 (sigma2Inv x) ≡ x
sigma2InverseRight (signed plus gamma1) = refl
sigma2InverseRight (signed plus gamma2) = refl
sigma2InverseRight (signed plus gamma3) = refl
sigma2InverseRight (signed minus gamma1) = refl
sigma2InverseRight (signed minus gamma2) = refl
sigma2InverseRight (signed minus gamma3) = refl

yangBaxterB3 :
  (x : SignedMajorana) →
  sigma1 (sigma2 (sigma1 x))
  ≡
  sigma2 (sigma1 (sigma2 x))
yangBaxterB3 (signed plus gamma1) = refl
yangBaxterB3 (signed plus gamma2) = refl
yangBaxterB3 (signed plus gamma3) = refl
yangBaxterB3 (signed minus gamma1) = refl
yangBaxterB3 (signed minus gamma2) = refl
yangBaxterB3 (signed minus gamma3) = refl

gamma2NotGamma3 :
  signed plus gamma2 ≡ signed plus gamma3 →
  ⊥
gamma2NotGamma3 ()

sigma1Sigma2AtGamma1 :
  sigma1 (sigma2 (signed plus gamma1))
  ≡ signed plus gamma2
sigma1Sigma2AtGamma1 = refl

sigma2Sigma1AtGamma1 :
  sigma2 (sigma1 (signed plus gamma1))
  ≡ signed plus gamma3
sigma2Sigma1AtGamma1 = refl

sigma1Sigma2Noncommuting :
  ((x : SignedMajorana) →
    sigma1 (sigma2 x) ≡ sigma2 (sigma1 x))
  →
  ⊥
sigma1Sigma2Noncommuting commute =
  gamma2NotGamma3 (commute (signed plus gamma1))

-- Exchange squared gives the expected fermionic minus sign on the exchanged
-- pair while fixing the spectator.
sigma1SquareGamma1 :
  sigma1 (sigma1 (signed plus gamma1))
  ≡ signed minus gamma1
sigma1SquareGamma1 = refl

sigma1SquareGamma2 :
  sigma1 (sigma1 (signed plus gamma2))
  ≡ signed minus gamma2
sigma1SquareGamma2 = refl

sigma1SquareGamma3 :
  sigma1 (sigma1 (signed plus gamma3))
  ≡ signed plus gamma3
sigma1SquareGamma3 = refl
