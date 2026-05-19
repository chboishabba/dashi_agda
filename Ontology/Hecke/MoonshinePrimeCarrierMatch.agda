module Ontology.Hecke.MoonshinePrimeCarrierMatch where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)

open import MonsterOntos using
  ( SSP
  ; toNat
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )
open import Ontology.GodelLattice using (Vec15; v15; FactorVec)
open import Ontology.Hecke.Scan as HS using (Sig15)

------------------------------------------------------------------------
-- Carrier-level match:
-- these are the 15 canonical SSP / Ogg / Monster primes in repo order.

sspPrimeCarrier : Vec15 Nat
sspPrimeCarrier =
  v15
    (toNat p2)
    (toNat p3)
    (toNat p5)
    (toNat p7)
    (toNat p11)
    (toNat p13)
    (toNat p17)
    (toNat p19)
    (toNat p23)
    (toNat p29)
    (toNat p31)
    (toNat p41)
    (toNat p47)
    (toNat p59)
    (toNat p71)

canonicalMonsterPrimeCarrier : Vec15 Nat
canonicalMonsterPrimeCarrier =
  v15
    2 3 5 7 11
    13 17 19 23 29
    31 41 47 59 71

sspPrimeCarrier≡canonicalMonsterPrimeCarrier :
  sspPrimeCarrier ≡ canonicalMonsterPrimeCarrier
sspPrimeCarrier≡canonicalMonsterPrimeCarrier = refl

------------------------------------------------------------------------
-- Boundary reading:
-- the prime-embedding codomain is already a 15-lane SSP carrier, so any
-- boundary-case prime mismatch must arise in later interpretation, not in the
-- carrier itself.

PrimeSupport = SSP

record CarrierBoundarySurface : Set where
  field
    supportPrime : PrimeSupport
    supportValue : Nat

factorVecSupportAt : FactorVec → SSP → CarrierBoundarySurface
factorVecSupportAt
  (v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) p with p
... | p2  = record { supportPrime = p2  ; supportValue = e2  }
... | p3  = record { supportPrime = p3  ; supportValue = e3  }
... | p5  = record { supportPrime = p5  ; supportValue = e5  }
... | p7  = record { supportPrime = p7  ; supportValue = e7  }
... | p11 = record { supportPrime = p11 ; supportValue = e11 }
... | p13 = record { supportPrime = p13 ; supportValue = e13 }
... | p17 = record { supportPrime = p17 ; supportValue = e17 }
... | p19 = record { supportPrime = p19 ; supportValue = e19 }
... | p23 = record { supportPrime = p23 ; supportValue = e23 }
... | p29 = record { supportPrime = p29 ; supportValue = e29 }
... | p31 = record { supportPrime = p31 ; supportValue = e31 }
... | p41 = record { supportPrime = p41 ; supportValue = e41 }
... | p47 = record { supportPrime = p47 ; supportValue = e47 }
... | p59 = record { supportPrime = p59 ; supportValue = e59 }
... | p71 = record { supportPrime = p71 ; supportValue = e71 }

------------------------------------------------------------------------
-- Signature-side equality is the legal next theorem target.
-- We record it explicitly here without claiming it is already discharged.

postulate
  ShiftState : Set
  shiftPrimeEmbedding : ShiftState → FactorVec
  shiftSignature : ShiftState → HS.Sig15
  monsterSignature : ShiftState → HS.Sig15

  shiftPrimeEmbedding-has-SSP-carrier :
    ∀ x p →
    CarrierBoundarySurface.supportPrime
      (factorVecSupportAt (shiftPrimeEmbedding x) p)
      ≡
    p

  shiftSignature≡monsterSignature-target :
    ∀ x →
    shiftSignature x ≡ monsterSignature x

record MoonshinePrimeCarrierMatch : Set₁ where
  field
    carrierEquality :
      sspPrimeCarrier ≡ canonicalMonsterPrimeCarrier
    signatureEqualityTarget :
      Set

moonshinePrimeCarrierMatch : MoonshinePrimeCarrierMatch
moonshinePrimeCarrierMatch = record
  { carrierEquality = sspPrimeCarrier≡canonicalMonsterPrimeCarrier
  ; signatureEqualityTarget = ∀ x → shiftSignature x ≡ monsterSignature x
  }
