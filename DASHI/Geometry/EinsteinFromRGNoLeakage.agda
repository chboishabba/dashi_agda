module DASHI.Geometry.EinsteinFromRGNoLeakage where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

postulate
  M : Set
  Point : Set
  Tensor2 : Set
  ℚ : Set
  0q : ℚ
  div : Tensor2 → Point → ℚ
  sym : Tensor2 → Set
  G : M → Tensor2
  T : M → Tensor2

  RGState : Set
  step : RGState → RGState
  geom : RGState → M
  Pτ : Tensor2 → Tensor2

Defect : RGState → Tensor2
Defect s = Pτ (T (geom (step s)))

record GR_NoLeakage : Set₁ where
  field
    bianchi : ∀ s x → div (G (geom s)) x ≡ 0q
    conserve : ∀ s x → div (T (geom s)) x ≡ 0q
    defect-law : ∀ s → G (geom s) ≡ Defect s
    symG : ∀ s → sym (G (geom s))
    symT : ∀ s → sym (T (geom s))

open GR_NoLeakage public

record EinsteinConsequences (A : GR_NoLeakage) : Set₁ where
  field
    divergenceFree : ∀ s x → div (G (geom s)) x ≡ 0q
    conservation : ∀ s x → div (T (geom s)) x ≡ 0q
    einsteinEq : ∀ s → G (geom s) ≡ Defect s

EinsteinFromRG :
  (A : GR_NoLeakage) →
  EinsteinConsequences A
EinsteinFromRG A =
  record
    { divergenceFree = bianchi A
    ; conservation = conserve A
    ; einsteinEq = defect-law A
    }
