module DASHI.Geometry.DNAFourWayLiftOperators where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Geometry.DNAFourAdicSheetLift as Lift

record Triple (A : Set) : Set where
  constructor triple
  field r1 r2 r3 : A
open Triple public

record ExactQuadSplit (A : Set) : Set where
  constructor split
  field
    coarse : A
    detail : Triple A
open ExactQuadSplit public

project : ∀ {A : Set} → Lift.Quad A → A
project (Lift.quad a b c d) = a

residual : ∀ {A : Set} → Lift.Quad A → Triple A
residual (Lift.quad a b c d) = triple b c d

broadcast : ∀ {A : Set} → A → Lift.Quad A
broadcast a = Lift.quad a a a a

reconstruct : ∀ {A : Set} → A → Triple A → Lift.Quad A
reconstruct a (triple b c d) = Lift.quad a b c d

splitQuad : ∀ {A : Set} → Lift.Quad A → ExactQuadSplit A
splitQuad q = split (project q) (residual q)

reconstruction : ∀ {A : Set} (q : Lift.Quad A) → reconstruct (project q) (residual q) ≡ q
reconstruction (Lift.quad a b c d) = refl

project-broadcast : ∀ {A : Set} (a : A) → project (broadcast a) ≡ a
project-broadcast a = refl

mapTriple : ∀ {A B : Set} → (A → B) → Triple A → Triple B
mapTriple f (triple a b c) = triple (f a) (f b) (f c)

mapQuad-project :
  ∀ {A B : Set} (f : A → B) (q : Lift.Quad A) →
  project (Lift.mapQuad f q) ≡ f (project q)
mapQuad-project f (Lift.quad a b c d) = refl

mapQuad-residual :
  ∀ {A B : Set} (f : A → B) (q : Lift.Quad A) →
  residual (Lift.mapQuad f q) ≡ mapTriple f (residual q)
mapQuad-residual f (Lift.quad a b c d) = refl

complement-reconstruction-equivariant :
  ∀ q →
  Lift.mapQuad DNA.complement (reconstruct (project q) (residual q))
  ≡ reconstruct
      (DNA.complement (project q))
      (mapTriple DNA.complement (residual q))
complement-reconstruction-equivariant (Lift.quad a b c d) = refl

reverseQuad : ∀ {A : Set} → Lift.Quad A → Lift.Quad A
reverseQuad (Lift.quad a b c d) = Lift.quad d c b a

reverseComplementQuad : Lift.Quad DNA.DNABase → Lift.Quad DNA.DNABase
reverseComplementQuad q = Lift.mapQuad DNA.complement (reverseQuad q)

reverseQuad-involutive : ∀ {A : Set} (q : Lift.Quad A) → reverseQuad (reverseQuad q) ≡ q
reverseQuad-involutive (Lift.quad a b c d) = refl

reverseComplementQuad-involutive :
  ∀ q → reverseComplementQuad (reverseComplementQuad q) ≡ q
reverseComplementQuad-involutive (Lift.quad a b c d)
  rewrite DNA.complement-involutive a
        | DNA.complement-involutive b
        | DNA.complement-involutive c
        | DNA.complement-involutive d = refl

record ConcreteLiftReceipt : Set where
  constructor receipt
  field
    example : Lift.Quad DNA.DNABase
    reconstructionHolds : reconstruct (project example) (residual example) ≡ example
    complementEquivariant :
      Lift.mapQuad DNA.complement (reconstruct (project example) (residual example))
      ≡ reconstruct (DNA.complement (project example))
          (mapTriple DNA.complement (residual example))
open ConcreteLiftReceipt public

canonicalConcreteLiftReceipt : ConcreteLiftReceipt
canonicalConcreteLiftReceipt =
  receipt
    (Lift.quad DNA.A DNA.C DNA.G DNA.T)
    refl
    refl
