module DASHI.Algebra.SMConformanceVectorsInstance where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)

open import DASHI.Algebra.SMConformanceVectors as SCV
open import DASHI.Algebra.PhysicsTable as PT
open import DASHI.Algebra.PhysicsSignature using (Sig15)

mapVec : ∀ {A B : Set} → (A → B) → List A → List B
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

conformsOn-refl :
  ∀ {State Sig} (f : State → Sig) (vs : SCV.Vectors State) →
  SCV.ConformsOn f f vs
conformsOn-refl f [] = tt
conformsOn-refl f (v ∷ vs) = (refl , conformsOn-refl f vs)

smConformanceAxioms : SCV.SMConformanceAxioms
smConformanceAxioms =
  record
    { State = PT.State
    ; Sig = Sig15
    ; specSig = PT.specSig
    ; implSig = PT.implSig
    ; vectors = mapVec SCV.vec PT.vectors
    ; physics-conformance = conformsOn-refl PT.implSig (mapVec SCV.vec PT.vectors)
    }
