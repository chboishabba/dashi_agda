module DASHI.Physics.YangMills.BalabanPeriodicLatticeEnumeration where

------------------------------------------------------------------------
-- Finite enumerations for the literal periodic lattice carrier.
--
-- The averaging and Gaussian operators are finite-dimensional at fixed
-- cutoff.  This module gives constructive lists of every periodic vertex and
-- every positively oriented bond, together with membership proofs.  No
-- cardinality estimate or analytic bound is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (List; []; _∷_; _++_; map)

open import DASHI.Physics.YangMills.GraphCombinatorics using
  ( _∈_
  ; here
  ; there
  )
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; cube4
  ; Axis4
  ; axis₀
  ; axis₁
  ; axis₂
  ; axis₃
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  ( DirectedBond4
  ; positiveBond
  )

mapMember :
  ∀ {A B : Set}
  (f : A → B) {x : A} {xs : List A} →
  x ∈ xs →
  f x ∈ map f xs
mapMember f here = here
mapMember f (there x∈) = there (mapMember f x∈)

inAppendLeft :
  ∀ {A : Set} {x : A} {xs ys : List A} →
  x ∈ xs →
  x ∈ xs ++ ys
inAppendLeft here = here
inAppendLeft (there x∈) = there (inAppendLeft x∈)

inAppendRight :
  ∀ {A : Set} {x : A}
  (xs : List A) {ys : List A} →
  x ∈ ys →
  x ∈ xs ++ ys
inAppendRight [] x∈ = x∈
inAppendRight (y ∷ ys) x∈ = there (inAppendRight ys x∈)

concatMap :
  ∀ {A B : Set} →
  (A → List B) →
  List A →
  List B
concatMap f [] = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

concatMapMember :
  ∀ {A B : Set}
  (f : A → List B)
  {x : A} {xs : List A}
  {y : B} →
  x ∈ xs →
  y ∈ f x →
  y ∈ concatMap f xs
concatMapMember f here y∈ = inAppendLeft y∈
concatMapMember f (there x∈) y∈ =
  inAppendRight _ (concatMapMember f x∈ y∈)

allFin :
  (N : Nat) →
  List (Fin N)
allFin zero = []
allFin (suc N) = fzero ∷ map fsuc (allFin N)

allFinComplete :
  ∀ {N : Nat} (i : Fin N) →
  i ∈ allFin N
allFinComplete {suc N} fzero = here
allFinComplete {suc N} (fsuc i) =
  there (mapMember fsuc (allFinComplete i))

allCube4 :
  (N : Nat) →
  List (Cube4 N)
allCube4 N =
  concatMap
    (λ a₀ →
      concatMap
        (λ a₁ →
          concatMap
            (λ a₂ →
              map
                (λ a₃ → cube4 a₀ a₁ a₂ a₃)
                (allFin N))
            (allFin N))
        (allFin N))
    (allFin N)

allCube4Complete :
  ∀ {N : Nat} (x : Cube4 N) →
  x ∈ allCube4 N
allCube4Complete (cube4 a₀ a₁ a₂ a₃) =
  concatMapMember _
    (allFinComplete a₀)
    (concatMapMember _
      (allFinComplete a₁)
      (concatMapMember _
        (allFinComplete a₂)
        (mapMember _ (allFinComplete a₃))))

allAxes : List Axis4
allAxes = axis₀ ∷ axis₁ ∷ axis₂ ∷ axis₃ ∷ []

axisMember :
  (a : Axis4) →
  a ∈ allAxes
axisMember axis₀ = here
axisMember axis₁ = there here
axisMember axis₂ = there (there here)
axisMember axis₃ = there (there (there here))

allPositiveBonds :
  (N : Nat) →
  List (DirectedBond4 N)
allPositiveBonds N =
  concatMap
    (λ x → map (positiveBond x) allAxes)
    (allCube4 N)

positiveBondMember :
  ∀ {N : Nat}
  (x : Cube4 N) (a : Axis4) →
  positiveBond x a ∈ allPositiveBonds N
positiveBondMember x a =
  concatMapMember _
    (allCube4Complete x)
    (mapMember (positiveBond x) (axisMember a))
