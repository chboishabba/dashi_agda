module Ontology.Hecke.DefectCorrespondenceRepresentation where

open import Agda.Builtin.Nat using (Nat; _+_)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

------------------------------------------------------------------------
-- A state-indexed finite correspondence whose fibers land in a defect or
-- observable carrier. This is the right surface for scan/defect-derived
-- Hecke-style averaging.

sum15 : Vec15 Nat → Nat
sum15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  a2 + a3 + a5 + a7 + a11 + a13 + a17 + a19 + a23 + a29 + a31 + a41 + a47 + a59 + a71

map15 : ∀ {A B : Set} → (A → B) → Vec15 A → Vec15 B
map15 f (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  mkVec15
    (f a2) (f a3) (f a5) (f a7) (f a11)
    (f a13) (f a17) (f a19) (f a23) (f a29)
    (f a31) (f a41) (f a47) (f a59) (f a71)

record PrimeDefectHeckeOn (S D : Set) : Set₁ where
  field
    correspondence : SSP → S → Vec15 D

  operator : (D → Nat) → SSP → S → Nat
  operator f p x = sum15 (map15 f (correspondence p x))
