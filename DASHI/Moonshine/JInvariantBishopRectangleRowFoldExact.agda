module DASHI.Moonshine.JInvariantBishopRectangleRowFoldExact where

-- Exact finite row grouping of the original filtered square list.
-- Reuses the original signed coordinate decoder and uniqueness/permutation
-- owner, then literal cartesianProductWith fold recursion.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_⊔_)
import Data.Nat.Properties as NP
open import Data.Fin.Base using (Fin)
open import Data.Bool.Base using (T)
open import Data.Bool.Properties using (T-∧)
open import Data.List.Base using (List; []; _∷_; map; allFin; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻; ∈-allFin; ∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym)
import Real as R
import RealProperties as P
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Cut
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopRectangleExhaustionExact as Rect

Code : Nat → Set
Code n = Fin (Cube.coordinateCodeBound n)

decode : ∀ n m → Code n × Code m → L.LatticePoint
decode n m (i , j) = L.lattice-point (Cube.decodeCoordinate n i) (Cube.decodeCoordinate m j)

codes : ∀ n m → List (Code n × Code m)
codes n m = cartesianProductWith _,_ (allFin (Cube.coordinateCodeBound n)) (allFin (Cube.coordinateCodeBound m))

points : Nat → Nat → List L.LatticePoint
points n m = map (decode n m) (codes n m)

injective : ∀ n m {a b} → decode n m a ≡ decode n m b → a ≡ b
injective n m {i , j} {i' , j'} h = cong₂ _,_
  (Cube.decodeCoordinateInjective n (cong L.horizontal h))
  (Cube.decodeCoordinateInjective m (cong L.vertical h))

unique : ∀ n m → Unique (points n m)
unique n m = UniqueP.map⁺ (injective n m)
  (UniqueP.cartesianProductWith⁺ _,_ S.pairConstructorInjective
    (UniqueP.allFin⁺ (Cube.coordinateCodeBound n))
    (UniqueP.allFin⁺ (Cube.coordinateCodeBound m)))

toRectangle : ∀ n m {p} → p ∈ points n (n ⊔ m) → p ∈ Rect.rectangle n m
toRectangle n m {p} h with ∈-map⁻ (decode n (n ⊔ m)) {xs = codes n (n ⊔ m)} h
... | (i , j) , _ , eq = subst (λ q → q ∈ Rect.rectangle n m) (sym eq)
  (∈-filter⁺ (T? ∘ Rect.horizontalOK n)
    (Re.squareMember (n ⊔ m) (decode n (n ⊔ m) (i , j))
      (Equivalence.from T-∧
        (Cut.coordinateInCutoffMonotone n (n ⊔ m) (NP.m≤m⊔n n m)
          (Cube.decodeCoordinate n i) (Cut.decodeCoordinateInCutoff n i) ,
         Cut.decodeCoordinateInCutoff (n ⊔ m) j)))
    (Cut.decodeCoordinateInCutoff n i))

fromRectangle : ∀ n m {p} → p ∈ Rect.rectangle n m → p ∈ points n (n ⊔ m)
fromRectangle n m {p} h
  with ∈-filter⁻ (T? ∘ Rect.horizontalOK n) {xs = S.squarePoints (n ⊔ m)} h
... | inSquare , horizontal
  with Cut.decodeCoordinateComplete n (L.horizontal p) horizontal
     | Cut.decodeCoordinateComplete (n ⊔ m) (L.vertical p)
         (proj₂ (Equivalence.to T-∧ (Re.squareSound (n ⊔ m) p inSquare)))
... | i , ie | j , je = subst (λ q → q ∈ points n (n ⊔ m))
  (L.lattice-ext ie je)
  (∈-map⁺ (decode n (n ⊔ m))
    (∈-cartesianProductWith⁺ _,_ (∈-allFin i) (∈-allFin j)))

permutation : ∀ n m → Rect.rectangle n m Perm.↭ points n (n ⊔ m)
permutation n m = W.uniqueMembershipEquivalenceToPermutation
  (Rect.rectUnique n m) (unique n (n ⊔ m)) (fromRectangle n m) (toRectangle n m)

sumProduct : ∀ {A B : Set} (f : A → B → R.ℝ) xs ys →
  R._≃_ (Re.sum (λ p → f (proj₁ p) (proj₂ p)) (cartesianProductWith _,_ xs ys))
    (Re.sum (λ x → Re.sum (f x) ys) xs)
sumProduct f [] ys = P.≃-refl
sumProduct f (x ∷ xs) ys =
  P.≃-trans (Ex.sumAppend (λ p → f (proj₁ p) (proj₂ p))
    (map (x ,_) ys) (cartesianProductWith _,_ xs ys))
    (P.+-cong (Re.sumMap (λ p → f (proj₁ p) (proj₂ p)) (x ,_) ys)
      (sumProduct f xs ys))

finiteRows : ∀ (f : L.LatticePoint → R.ℝ) n m →
  R._≃_ (Re.sum f (Rect.rectangle n m))
    (Re.sum (λ i → Re.sum (λ j → f (decode n (n ⊔ m) (i , j)))
      (allFin (Cube.coordinateCodeBound (n ⊔ m)))) (allFin (Cube.coordinateCodeBound n)))
finiteRows f n m =
  P.≃-trans (Re.sumPerm f (permutation n m))
    (P.≃-trans (Re.sumMap f (decode n (n ⊔ m)) (codes n (n ⊔ m)))
      (sumProduct (λ i j → f (decode n (n ⊔ m) (i , j)))
        (allFin (Cube.coordinateCodeBound n)) (allFin (Cube.coordinateCodeBound (n ⊔ m)))))
