module Ontology.Hecke.FactorVecInstances where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using
  (Vec15; FactorVec; updateVec15; updateVec15-commutes)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
import Ontology.Hecke.QuotientRepresentation as HQ
import Ontology.Hecke.ReverseRepresentation as HR

------------------------------------------------------------------------
-- First concrete prime-address family for the representation-layer Hecke
-- interfaces: the carrier is the factor vector itself.

bumpPrime : SSP → FactorVec → FactorVec
bumpPrime p2  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 (suc e2) e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
bumpPrime p3  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 (suc e3) e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
bumpPrime p5  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 (suc e5) e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
bumpPrime p7  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 (suc e7) e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
bumpPrime p11 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 (suc e11) e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
bumpPrime p13 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 (suc e13) e17 e19 e23 e29 e31 e41 e47 e59 e71
bumpPrime p17 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 (suc e17) e19 e23 e29 e31 e41 e47 e59 e71
bumpPrime p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 (suc e19) e23 e29 e31 e41 e47 e59 e71
bumpPrime p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 (suc e23) e29 e31 e41 e47 e59 e71
bumpPrime p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 (suc e29) e31 e41 e47 e59 e71
bumpPrime p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 (suc e31) e41 e47 e59 e71
bumpPrime p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 (suc e41) e47 e59 e71
bumpPrime p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 (suc e47) e59 e71
bumpPrime p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 (suc e59) e71
bumpPrime p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 (suc e71)

primeBump : SSP → FactorVec → FactorVec
primeBump p = updateVec15 p suc

bumpPrime≡primeBump : ∀ p v → bumpPrime p v ≡ primeBump p v
bumpPrime≡primeBump p2  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p3  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p5  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p7  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p11 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p13 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p17 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
bumpPrime≡primeBump p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl

primeBumpCommutes :
  ∀ p q v →
  primeBump p (primeBump q v) ≡ primeBump q (primeBump p v)
primeBumpCommutes p q v =
  updateVec15-commutes p q suc suc (λ _ → refl) v

by-abelian-factorvec :
  ∀ p q v →
  primeBump p (primeBump q v) ≡ primeBump q (primeBump p v)
by-abelian-factorvec = primeBumpCommutes

bumpPrimeCommutes :
  ∀ p q v →
  bumpPrime p (bumpPrime q v) ≡ bumpPrime q (bumpPrime p v)
bumpPrimeCommutes p q v
  rewrite bumpPrime≡primeBump q v
        | bumpPrime≡primeBump p v
        | bumpPrime≡primeBump p (primeBump q v)
        | bumpPrime≡primeBump q (primeBump p v)
  = primeBumpCommutes p q v

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

flowPrime : SSP → FactorVec → FactorVec
flowPrime p v = bumpPrime (nextPrime p) (bumpPrime p v)

nonZero : Nat → Bool
nonZero zero    = false
nonZero (suc n) = true

bit : Bool → Nat
bit false = zero
bit true  = suc zero

nonZero-bit : ∀ b → nonZero (bit b) ≡ b
nonZero-bit false = refl
nonZero-bit true  = refl

SupportMask : Set
SupportMask = Vec15 Bool

supportMask : FactorVec → SupportMask
supportMask (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 (nonZero e2) (nonZero e3) (nonZero e5) (nonZero e7) (nonZero e11)
          (nonZero e13) (nonZero e17) (nonZero e19) (nonZero e23) (nonZero e29)
          (nonZero e31) (nonZero e41) (nonZero e47) (nonZero e59) (nonZero e71)

markPrime : SSP → SupportMask → SupportMask
markPrime p2  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 true e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
markPrime p3  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 true e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
markPrime p5  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 true e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
markPrime p7  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 true e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
markPrime p11 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 true e13 e17 e19 e23 e29 e31 e41 e47 e59 e71
markPrime p13 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 true e17 e19 e23 e29 e31 e41 e47 e59 e71
markPrime p17 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 true e19 e23 e29 e31 e41 e47 e59 e71
markPrime p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 true e23 e29 e31 e41 e47 e59 e71
markPrime p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 true e29 e31 e41 e47 e59 e71
markPrime p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 true e31 e41 e47 e59 e71
markPrime p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 true e41 e47 e59 e71
markPrime p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 true e47 e59 e71
markPrime p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 true e59 e71
markPrime p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 true e71
markPrime p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 true

flowMask : SSP → SupportMask → SupportMask
flowMask p m = markPrime (nextPrime p) (markPrime p m)

supportMask-bumpPrime : ∀ p v → supportMask (bumpPrime p v) ≡ markPrime p (supportMask v)
supportMask-bumpPrime p2  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p3  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p5  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p7  (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p11 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p13 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p17 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl
supportMask-bumpPrime p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) = refl

supportMask-flowPrime : ∀ p v → supportMask (flowPrime p v) ≡ flowMask p (supportMask v)
supportMask-flowPrime p v =
  trans (supportMask-bumpPrime (nextPrime p) (bumpPrime p v))
        (cong (markPrime (nextPrime p)) (supportMask-bumpPrime p v))

factorVecEquivalence : HQ.EquivalenceOn FactorVec
factorVecEquivalence = record
  { _≈_   = _≡_
  ; refl  = λ x → refl
  ; sym   = sym
  ; trans = trans
  }

factorVecQuotient : HQ.QuotientInterfaceOn FactorVec FactorVec
factorVecQuotient = record
  { equiv         = factorVecEquivalence
  ; proj          = λ x → x
  ; respect-proj  = λ eq → eq
  ; representative = λ c → c
  ; section       = λ c → refl
  }

factorVecReverseHecke : HR.ReverseHeckeMetricOn FactorVec
factorVecReverseHecke = record
  { address            = λ v → v
  ; transport          = bumpPrime
  ; pullback           = bumpPrime
  ; discrepancy        = λ p v → zero
  ; compatible         = λ p v → true
  ; compatible-sound   = λ p v ok → refl
  }

factorVecQuotientHecke : HQ.QuotientHeckeActionOn FactorVec FactorVec
factorVecQuotientHecke = record
  { quotient       = factorVecQuotient
  ; transport      = bumpPrime
  ; classHecke     = bumpPrime
  ; respects-equiv = λ p eq → cong (bumpPrime p) eq
  ; class-sound    = λ p x → refl
  }

supportMaskEquivalence : HQ.EquivalenceOn FactorVec
supportMaskEquivalence = record
  { _≈_   = λ x y → supportMask x ≡ supportMask y
  ; refl  = λ x → refl
  ; sym   = sym
  ; trans = trans
  }

supportMaskRepresentative : SupportMask → FactorVec
supportMaskRepresentative (mkVec15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71) =
  mkVec15 (bit b2) (bit b3) (bit b5) (bit b7) (bit b11)
          (bit b13) (bit b17) (bit b19) (bit b23) (bit b29)
          (bit b31) (bit b41) (bit b47) (bit b59) (bit b71)

supportMaskRepresentative-section :
  ∀ m → supportMask (supportMaskRepresentative m) ≡ m
supportMaskRepresentative-section (mkVec15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71)
  rewrite nonZero-bit b2
        | nonZero-bit b3
        | nonZero-bit b5
        | nonZero-bit b7
        | nonZero-bit b11
        | nonZero-bit b13
        | nonZero-bit b17
        | nonZero-bit b19
        | nonZero-bit b23
        | nonZero-bit b29
        | nonZero-bit b31
        | nonZero-bit b41
        | nonZero-bit b47
        | nonZero-bit b59
        | nonZero-bit b71
  = refl

supportMaskQuotient : HQ.QuotientInterfaceOn FactorVec SupportMask
supportMaskQuotient = record
  { equiv          = supportMaskEquivalence
  ; proj           = supportMask
  ; respect-proj   = λ eq → eq
  ; representative = supportMaskRepresentative
  ; section        = supportMaskRepresentative-section
  }

supportMaskQuotientHecke : HQ.QuotientHeckeActionOn FactorVec SupportMask
supportMaskQuotientHecke = record
  { quotient       = supportMaskQuotient
  ; transport      = bumpPrime
  ; classHecke     = markPrime
  ; respects-equiv = λ p {x} {y} eq →
      trans (supportMask-bumpPrime p x)
            (trans (cong (markPrime p) eq)
                   (sym (supportMask-bumpPrime p y)))
  ; class-sound    = supportMask-bumpPrime
  }

factorVecReverseHeckeFlow : HR.ReverseHeckeMetricOn FactorVec
factorVecReverseHeckeFlow = record
  { address            = λ v → v
  ; transport          = flowPrime
  ; pullback           = flowPrime
  ; discrepancy        = λ p v → zero
  ; compatible         = λ p v → true
  ; compatible-sound   = λ p v ok → refl
  }

supportMaskQuotientHeckeFlow : HQ.QuotientHeckeActionOn FactorVec SupportMask
supportMaskQuotientHeckeFlow = record
  { quotient       = supportMaskQuotient
  ; transport      = flowPrime
  ; classHecke     = flowMask
  ; respects-equiv = λ p {x} {y} eq →
      trans (supportMask-flowPrime p x)
            (trans (cong (flowMask p) eq)
                   (sym (supportMask-flowPrime p y)))
  ; class-sound    = supportMask-flowPrime
  }
