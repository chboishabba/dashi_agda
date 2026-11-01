module Ontology.Hecke.FactorVecSignedTransport where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Maybe    using (Maybe; just; nothing)
open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
import Ontology.Hecke.QuotientRepresentation as HQ
import Ontology.Hecke.SignedTransport as HS

------------------------------------------------------------------------
-- Signed multi-lane transport on the 15-prime factor lattice:
-- decrement one selected lane when legal, increment the next lane.

nextPrime : SSP → SSP
nextPrime p2  = p3
nextPrime p3  = p5
nextPrime p5  = p7
nextPrime p7  = p11
nextPrime p11 = p13
nextPrime p13 = p17
nextPrime p17 = p19
nextPrime p19 = p23
nextPrime p23 = p29
nextPrime p29 = p31
nextPrime p31 = p41
nextPrime p41 = p47
nextPrime p47 = p59
nextPrime p59 = p71
nextPrime p71 = p2

legalTransfer : SSP → FactorVec → Bool
legalTransfer p2  (mkVec15 zero    _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false
legalTransfer p3  (mkVec15 _ zero    _ _ _ _ _ _ _ _ _ _ _ _ _) = false
legalTransfer p5  (mkVec15 _ _ zero    _ _ _ _ _ _ _ _ _ _ _ _) = false
legalTransfer p7  (mkVec15 _ _ _ zero    _ _ _ _ _ _ _ _ _ _ _) = false
legalTransfer p11 (mkVec15 _ _ _ _ zero    _ _ _ _ _ _ _ _ _ _) = false
legalTransfer p13 (mkVec15 _ _ _ _ _ zero    _ _ _ _ _ _ _ _ _) = false
legalTransfer p17 (mkVec15 _ _ _ _ _ _ zero    _ _ _ _ _ _ _ _) = false
legalTransfer p19 (mkVec15 _ _ _ _ _ _ _ zero    _ _ _ _ _ _ _) = false
legalTransfer p23 (mkVec15 _ _ _ _ _ _ _ _ zero    _ _ _ _ _ _) = false
legalTransfer p29 (mkVec15 _ _ _ _ _ _ _ _ _ zero    _ _ _ _ _) = false
legalTransfer p31 (mkVec15 _ _ _ _ _ _ _ _ _ _ zero    _ _ _ _) = false
legalTransfer p41 (mkVec15 _ _ _ _ _ _ _ _ _ _ _ zero    _ _ _) = false
legalTransfer p47 (mkVec15 _ _ _ _ _ _ _ _ _ _ _ _ zero    _ _) = false
legalTransfer p59 (mkVec15 _ _ _ _ _ _ _ _ _ _ _ _ _ zero    _) = false
legalTransfer p71 (mkVec15 _ _ _ _ _ _ _ _ _ _ _ _ _ _ zero   ) = false
legalTransfer _   _ = true

transferPrime : SSP → FactorVec → Maybe FactorVec
transferPrime p2  (mkVec15 zero    e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = nothing
transferPrime p2  (mkVec15 (suc e2) e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  just (mkVec15 e2 (suc e3) e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
transferPrime p3  (mkVec15 e2 zero    e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = nothing
transferPrime p3  (mkVec15 e2 (suc e3) e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  just (mkVec15 e2 e3 (suc e5) e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
transferPrime p5  (mkVec15 e2 e3 zero    e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = nothing
transferPrime p5  (mkVec15 e2 e3 (suc e5) e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  just (mkVec15 e2 e3 e5 (suc e7) e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
transferPrime p7  (mkVec15 e2 e3 e5 zero    e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = nothing
transferPrime p7  (mkVec15 e2 e3 e5 (suc e7) e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  just (mkVec15 e2 e3 e5 e7 (suc e11) e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
transferPrime p11 (mkVec15 e2 e3 e5 e7 zero    e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = nothing
transferPrime p11 (mkVec15 e2 e3 e5 e7 (suc e11) e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  just (mkVec15 e2 e3 e5 e7 e11 (suc e13) e17 e19 e23 e29 e31 e41 e47 e59 e71)
transferPrime p13 (mkVec15 e2 e3 e5 e7 e11 zero    e17 e19 e23 e29 e31 e41 e47 e59 e71) = nothing
transferPrime p13 (mkVec15 e2 e3 e5 e7 e11 (suc e13) e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  just (mkVec15 e2 e3 e5 e7 e11 e13 (suc e17) e19 e23 e29 e31 e41 e47 e59 e71)
transferPrime p17 (mkVec15 e2 e3 e5 e7 e11 e13 zero    e19 e23 e29 e31 e41 e47 e59 e71) = nothing
transferPrime p17 (mkVec15 e2 e3 e5 e7 e11 e13 (suc e17) e19 e23 e29 e31 e41 e47 e59 e71) =
  just (mkVec15 e2 e3 e5 e7 e11 e13 e17 (suc e19) e23 e29 e31 e41 e47 e59 e71)
transferPrime p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 zero    e23 e29 e31 e41 e47 e59 e71) = nothing
transferPrime p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 (suc e19) e23 e29 e31 e41 e47 e59 e71) =
  just (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 (suc e23) e29 e31 e41 e47 e59 e71)
transferPrime p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 zero    e29 e31 e41 e47 e59 e71) = nothing
transferPrime p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 (suc e23) e29 e31 e41 e47 e59 e71) =
  just (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 (suc e29) e31 e41 e47 e59 e71)
transferPrime p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 zero    e31 e41 e47 e59 e71) = nothing
transferPrime p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 (suc e29) e31 e41 e47 e59 e71) =
  just (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 (suc e31) e41 e47 e59 e71)
transferPrime p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 zero    e41 e47 e59 e71) = nothing
transferPrime p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 (suc e31) e41 e47 e59 e71) =
  just (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 (suc e41) e47 e59 e71)
transferPrime p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 zero    e47 e59 e71) = nothing
transferPrime p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 (suc e41) e47 e59 e71) =
  just (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 (suc e47) e59 e71)
transferPrime p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 zero    e59 e71) = nothing
transferPrime p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 (suc e47) e59 e71) =
  just (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 (suc e59) e71)
transferPrime p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 zero    e71) = nothing
transferPrime p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 (suc e59) e71) =
  just (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 (suc e71))
transferPrime p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 zero   ) = nothing
transferPrime p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 (suc e71)) =
  just (mkVec15 (suc e2) e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)

transferDiscrepancy : SSP → FactorVec → Nat
transferDiscrepancy p v with legalTransfer p v
... | true  = zero
... | false = suc zero

transportOrStay : SSP → FactorVec → FactorVec
transportOrStay p x with transferPrime p x
... | just y  = y
... | nothing = x

-- Any finite saturation quotient loses exact decrement information at some
-- boundary. The current signed transfer therefore descends honestly only on
-- the fine equality quotient.

factorVecSignedTransport : HS.SignedTransportOn FactorVec
factorVecSignedTransport = record
  { transport = transferPrime
  ; legal     = legalTransfer
  }

factorVecSignedReverseHecke : HS.SignedReverseHeckeOn FactorVec
factorVecSignedReverseHecke = record
  { address           = λ v → v
  ; transport         = transferPrime
  ; pullback          = transferPrime
  ; discrepancy       = transferDiscrepancy
  ; legal             = legalTransfer
  ; compatible-sound  = λ p s s' stepEq → cong (λ z → z) stepEq
  }

factorVecSignedQuotientHecke : HQ.QuotientHeckeActionOn FactorVec FactorVec
factorVecSignedQuotientHecke = record
  { quotient       = record
      { equiv          = record
          { _≈_   = _≡_
          ; refl  = λ x → refl
          ; sym   = λ eq → sym eq
          ; trans = λ eq₁ eq₂ → trans eq₁ eq₂
          }
      ; proj           = λ x → x
      ; respect-proj   = λ eq → eq
      ; representative = λ c → c
      ; section        = λ c → refl
      }
  ; transport      = transportOrStay
  ; classHecke     = transportOrStay
  ; respects-equiv = λ p eq → cong (transportOrStay p) eq
  ; class-sound    = λ p x → refl
  }
