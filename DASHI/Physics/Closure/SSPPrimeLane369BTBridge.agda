module DASHI.Physics.Closure.SSPPrimeLane369BTBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Foundations.SSPPrimeLaneSymmetryProfile using
  ( PrimeLaneSymmetryProfile
  ; primeLaneSymmetryProfile
  ; unitOrder
  )
open import DASHI.TrackedPrimes using
  ( SSP
  ; toNat
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )

btValencyFromPrime : SSP → Nat
btValencyFromPrime p = suc (toNat p)

record SSPPrimeLane369BTProfile : Set where
  constructor mkSSPPrimeLane369BTProfile
  field
    primeLane : SSP
    symmetryProfile : PrimeLaneSymmetryProfile
    symmetryMatchesPrime : PrimeLaneSymmetryProfile.primeIdentity symmetryProfile ≡ primeLane
    btValency : Nat
    btValencyMatches : btValency ≡ btValencyFromPrime primeLane

open SSPPrimeLane369BTProfile public

primeLane369BTProfile : SSP → SSPPrimeLane369BTProfile
primeLane369BTProfile p =
  mkSSPPrimeLane369BTProfile
    p
    (primeLaneSymmetryProfile p)
    refl
    (btValencyFromPrime p)
    refl

canonicalSSPPrimeLane369BTProfiles : List SSPPrimeLane369BTProfile
canonicalSSPPrimeLane369BTProfiles =
  primeLane369BTProfile p2
  ∷ primeLane369BTProfile p3
  ∷ primeLane369BTProfile p5
  ∷ primeLane369BTProfile p7
  ∷ primeLane369BTProfile p11
  ∷ primeLane369BTProfile p13
  ∷ primeLane369BTProfile p17
  ∷ primeLane369BTProfile p19
  ∷ primeLane369BTProfile p23
  ∷ primeLane369BTProfile p29
  ∷ primeLane369BTProfile p31
  ∷ primeLane369BTProfile p41
  ∷ primeLane369BTProfile p47
  ∷ primeLane369BTProfile p59
  ∷ primeLane369BTProfile p71
  ∷ []

p7BTValencyIs8 : btValency (primeLane369BTProfile p7) ≡ 8
p7BTValencyIs8 = refl

p71BTValencyIs72 : btValency (primeLane369BTProfile p71) ≡ 72
p71BTValencyIs72 = refl
