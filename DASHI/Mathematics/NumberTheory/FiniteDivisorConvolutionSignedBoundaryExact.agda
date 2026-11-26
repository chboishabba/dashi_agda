module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact where

-- SOURCE-WRITTEN, UNCOMPILED. The actual two grade-preserving list
-- permutations now imply the signed interior/boundary fold identity
-- for every positive grading, including the empty grade.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; map; filter)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as M
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Data.Integer.Base using (ℤ; +_; _+_)
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact
  using (Quad; a; b; x; y; left; right; leftBack; rightBack;
         leftInverse; rightInverse; weight1; weight2; weight3; weight4;
         weight1ShearSymmetry; weight2ShearSymmetry; weight3ShearSymmetry; weight4ShearSymmetry)
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact as G

foldZ : ∀ {A : Set} → (A → ℤ) → List A → ℤ
foldZ f [] = + 0
foldZ f (q ∷ qs) = f q + foldZ f qs

foldMap : ∀ {A B : Set} (f : B → ℤ) (g : A → B) (qs : List A) →
  foldZ f (map g qs) ≡ foldZ (λ q → f (g q)) qs
foldMap f g [] = refl
foldMap f g (q ∷ qs) = cong (f (g q) +_) (foldMap f g qs)

foldCongOn : ∀ {A : Set} (f g : A → ℤ) (qs : List A) →
  (∀ {q} → q ∈ qs → f q ≡ g q) → foldZ f qs ≡ foldZ g qs
foldCongOn f g [] h = refl
foldCongOn f g (q ∷ qs) h =
  trans (cong (_+ foldZ f qs) (h (Any.here refl)))
    (cong (g q +_) (foldCongOn f g qs (λ m → h (Any.there m))))

foldPerm : ∀ {A : Set} (f : A → ℤ) {qs rs : List A} →
  qs Perm.↭ rs → foldZ f qs ≡ foldZ f rs
foldPerm f Perm.refl = refl
foldPerm f (Perm.prep q p) = cong (f q +_) (foldPerm f p)
foldPerm f (Perm.swap {ys = ys} q r p) =
  trans (cong (λ s → f q + (f r + s)) (foldPerm f p))
    (solve 3 (λ a b c → a :+ (b :+ c) := b :+ (a :+ c))
      refl (f q) (f r) (foldZ f ys))
foldPerm f (Perm.trans p q) = trans (foldPerm f p) (foldPerm f q)

-- The two complementary strict charts plus equality give a partition.
-- Separate decisions are retained so the resulting filters are exactly
-- the already-owned chart source/target lists, not fresh scans.
lt gt eq : (Quad → Nat) → (Quad → Nat) → List Quad → List Quad
lt u v = filter (λ q → u q NP.<? v q)
gt u v = filter (λ q → v q NP.<? u q)
eq u v = filter (λ q → u q NP.≟ v q)

foldSplit : (f : Quad → ℤ) (u v : Quad → Nat) (qs : List Quad) →
  foldZ f qs ≡ (foldZ f (lt u v qs) + foldZ f (gt u v qs)) + foldZ f (eq u v qs)
foldSplit f u v [] = refl
foldSplit f u v (q ∷ qs)
  with u q NP.<? v q | v q NP.<? u q | u q NP.≟ v q
... | yes l | yes r | _ = ⊥-elim (NP.<-asym l r)
... | yes l | no _ | yes e = ⊥-elim (NP.<⇒≢ l e)
... | no _ | yes r | yes e = ⊥-elim (NP.<⇒≢ r (sym e))
... | yes l | no _ | no _ =
  trans (cong (f q +_) (foldSplit f u v qs))
    (solve 4 (λ a b c d → a :+ ((b :+ c) :+ d) := ((a :+ b) :+ c) :+ d)
      refl (f q) (foldZ f (lt u v qs)) (foldZ f (gt u v qs)) (foldZ f (eq u v qs)))
... | no _ | yes r | no _ =
  trans (cong (f q +_) (foldSplit f u v qs))
    (solve 4 (λ a b c d → a :+ ((b :+ c) :+ d) := (b :+ (a :+ c)) :+ d)
      refl (f q) (foldZ f (lt u v qs)) (foldZ f (gt u v qs)) (foldZ f (eq u v qs)))
... | no _ | no _ | yes e =
  trans (cong (f q +_) (foldSplit f u v qs))
    (solve 4 (λ a b c d → a :+ ((b :+ c) :+ d) := (b :+ c) :+ (a :+ d))
      refl (f q) (foldZ f (lt u v qs)) (foldZ f (gt u v qs)) (foldZ f (eq u v qs)))
... | no l | no r | no e with NP.<-cmp (u q) (v q)
...   | tri< h _ _ = ⊥-elim (l h)
...   | tri≈ _ h _ = ⊥-elim (e h)
...   | tri> _ _ h = ⊥-elim (r h)

Weight : Set
Weight = ℤ → ℤ → ℤ

F Gplus : Weight → Quad → ℤ
F f q = f (+ a q) (+ b q)
Gplus f q = f (+ (a q N.+ b q)) (+ b q)

ShearSymmetry : Weight → Set
ShearSymmetry f = ∀ a b → f (a + b) b ≡ f a (a + b)

rightWeight : (f : Weight) → ShearSymmetry f → (q : Quad) →
  F f (rightBack q) ≡ Gplus f q
rightWeight f h q =
  trans (cong (f (+ a q)) (ZP.pos-+ (a q) (b q)))
    (trans (sym (h (+ a q) (+ b q)))
      (cong (λ t → f t (+ b q)) (sym (ZP.pos-+ (a q) (b q)))))

leftFold : (f : Weight) (n : Nat) →
  foldZ (F f) (G.L.source n) ≡ foldZ (Gplus f) (G.L.target n)
leftFold f n =
  trans (foldCongOn (F f) (λ q → Gplus f (left q)) (G.L.source n)
      (λ {q} m → cong (F f) (sym (leftInverse q
        (proj₂ (M.∈-filter⁻ (λ q → b q NP.<? a q) m))))))
    (trans (sym (foldMap (Gplus f) left (G.L.source n)))
      (foldPerm (Gplus f) (G.leftPermutation n)))

rightFold : (f : Weight) → ShearSymmetry f → (n : Nat) →
  foldZ (F f) (G.R.source n) ≡ foldZ (Gplus f) (G.R.target n)
rightFold f h n =
  trans (foldCongOn (F f) (λ q → Gplus f (right q)) (G.R.source n)
      (λ {q} m → trans (cong (F f) (sym (rightInverse q
        (proj₂ (M.∈-filter⁻ (λ q → a q NP.<? b q) m)))))
        (rightWeight f h (right q))))
    (trans (sym (foldMap (Gplus f) right (G.R.source n)))
      (foldPerm (Gplus f) (G.rightPermutation n)))

-- Balanced signed boundary equation. No subtraction/truncation of
-- equality strata, no asserted universal fold supplied by caller.
boundary : (f : Weight) → ShearSymmetry f → (n : Nat) →
  foldZ (Gplus f) (G.omega n) + foldZ (F f) (eq a b (G.omega n))
  ≡ foldZ (F f) (G.omega n) + foldZ (Gplus f) (eq x y (G.omega n))
boundary f h n =
  let
    o = G.omega n
    l = foldZ (Gplus f) (G.L.target n)
    r = foldZ (Gplus f) (G.R.target n)
    A = foldZ (F f) (eq a b o)
    B = foldZ (Gplus f) (eq x y o)
  in trans (cong (_+ A) (foldSplit (Gplus f) x y o))
    (trans (solve 4 (λ l r a b → ((l :+ r) :+ b) :+ a := ((r :+ l) :+ a) :+ b)
      refl l r A B)
      (trans (cong (λ t → (t + A) + B)
        (trans (cong (_+ l) (sym (rightFold f h n)))
          (cong (foldZ (F f) (G.R.source n) +_) (sym (leftFold f n)))))
        (cong (_+ B) (sym (foldSplit (F f) a b o)))))

boundary1 = boundary weight1 weight1ShearSymmetry
boundary2 = boundary weight2 weight2ShearSymmetry
boundary3 = boundary weight3 weight3ShearSymmetry
boundary4 = boundary weight4 weight4ShearSymmetry
