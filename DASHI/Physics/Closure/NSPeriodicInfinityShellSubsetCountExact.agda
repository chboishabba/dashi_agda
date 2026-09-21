module DASHI.Physics.Closure.NSPeriodicInfinityShellSubsetCountExact where

------------------------------------------------------------------------
-- PERIODIC B1 / LITERAL INFINITY-SHELL SUBSET CARDINALITY
--
-- NSPeriodicInfinityShellModeCount already owns the actual duplicate-free
-- max-coordinate outer cube.  This file proves the one generic finite fact
-- needed to consume it:
--
--   duplicate-free xs ⊆ ys  =>  length xs <= length ys.
--
-- The proof is structural on the repository's cutoff-cube membership carrier;
-- no decidable equality and no shell approximation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicInfinityShellModeCount as ShellCount

Subset : ∀ {A : Set} → List A → List A → Set
Subset xs ys = ∀ {x} → x Cube.∈ xs → x Cube.∈ ys

removeMember :
  ∀ {A : Set} {x : A} {xs : List A} →
  x Cube.∈ xs →
  List A
removeMember {xs = _ ∷ xs} (Cube.here refl) = xs
removeMember {xs = y ∷ xs} (Cube.there x∈xs) =
  y ∷ removeMember x∈xs

removeMemberLength :
  ∀ {A : Set} {x : A} {xs : List A} →
  (x∈xs : x Cube.∈ xs) →
  suc (Cube.length (removeMember x∈xs)) ≡ Cube.length xs
removeMemberLength {xs = _ ∷ _} (Cube.here refl) = refl
removeMemberLength {xs = _ ∷ _} (Cube.there x∈xs) =
  subst
    (λ n → suc (suc (Cube.length (removeMember x∈xs))) ≡ suc n)
    (removeMemberLength x∈xs)
    refl

removeMemberKeepsOther :
  ∀ {A : Set} {x y : A} {xs : List A} →
  (x∈xs : x Cube.∈ xs) →
  y Cube.∈ xs →
  (y ≡ x → ⊥) →
  y Cube.∈ removeMember x∈xs
removeMemberKeepsOther (Cube.here refl) (Cube.here refl) y≢x =
  ⊥-elim (y≢x refl)
removeMemberKeepsOther (Cube.here refl) (Cube.there y∈xs) y≢x =
  y∈xs
removeMemberKeepsOther (Cube.there x∈xs) (Cube.here refl) y≢x =
  Cube.here refl
removeMemberKeepsOther (Cube.there x∈xs) (Cube.there y∈xs) y≢x =
  Cube.there (removeMemberKeepsOther x∈xs y∈xs y≢x)

removeMemberSubset :
  ∀ {A : Set} {x : A} {xs : List A} →
  (x∈xs : x Cube.∈ xs) →
  Subset (removeMember x∈xs) xs
removeMemberSubset (Cube.here refl) y∈ =
  Cube.there y∈
removeMemberSubset (Cube.there x∈xs) (Cube.here refl) =
  Cube.here refl
removeMemberSubset (Cube.there x∈xs) (Cube.there y∈removed) =
  Cube.there (removeMemberSubset x∈xs y∈removed)

removeMemberNoDuplicates :
  ∀ {A : Set} {x : A} {xs : List A} →
  (x∈xs : x Cube.∈ xs) →
  Cube.NoDuplicates xs →
  Cube.NoDuplicates (removeMember x∈xs)
removeMemberNoDuplicates (Cube.here refl)
    (Cube.unique∷ fresh rest) =
  rest
removeMemberNoDuplicates {x = x} (Cube.there x∈xs)
    (Cube.unique∷ {x = y} {xs = ys} fresh rest) =
  Cube.unique∷ freshRemoved
    (removeMemberNoDuplicates x∈xs rest)
  where
  freshRemoved : y Cube.∉ removeMember x∈xs
  freshRemoved y∈removed =
    fresh (removeMemberSubset x∈xs y∈removed)

noDuplicateSubsetLengthBound :
  ∀ {A : Set} {xs ys : List A} →
  Cube.NoDuplicates xs →
  Subset xs ys →
  Cube.length xs Cube.≤ᴺ Cube.length ys
noDuplicateSubsetLengthBound Cube.unique[] subset =
  Cube.z≤n
noDuplicateSubsetLengthBound
    {xs = x ∷ xs} {ys = ys}
    (Cube.unique∷ x∉xs xsUnique)
    subset =
  let
    x∈ys : x Cube.∈ ys
    x∈ys = subset (Cube.here refl)

    xsSubsetRemoved : Subset xs (removeMember x∈ys)
    xsSubsetRemoved {x = y} y∈xs =
      removeMemberKeepsOther
        x∈ys
        (subset (Cube.there y∈xs))
        (λ y≡x →
          x∉xs
            (subst
              (λ z → z Cube.∈ xs)
              y≡x
              y∈xs))

    ih :
      Cube.length xs Cube.≤ᴺ
        Cube.length (removeMember x∈ys)
    ih =
      noDuplicateSubsetLengthBound
        xsUnique xsSubsetRemoved
  in
  Cube.≤ᴺ-substRight
    (removeMemberLength x∈ys)
    (Cube.s≤s ih)

literalInfinityShellLengthBound :
  (n : Nat) →
  (support : ShellCount.InfinityShellSupport n) →
  Cube.length (ShellCount.shellModes support)
    Cube.≤ᴺ ShellCount.infinityCubeModeCount n
literalInfinityShellLengthBound n support =
  Cube.≤ᴺ-substRight
    (ShellCount.literalInfinityCubeLength n)
    (noDuplicateSubsetLengthBound
      (ShellCount.shellNoDuplicates support)
      (ShellCount.shellContainedInOuterCube support))

literalInfinityShellSubsetCountClosed : Bool
literalInfinityShellSubsetCountClosed = true

literalInfinityShellSubsetCountIntroducesDecidableEquality : Bool
literalInfinityShellSubsetCountIntroducesDecidableEquality = false

literalInfinityShellSubsetCountIntroducesPostulate : Bool
literalInfinityShellSubsetCountIntroducesPostulate = false

literalInfinityShellSubsetCountClosedIsTrue :
  literalInfinityShellSubsetCountClosed ≡ true
literalInfinityShellSubsetCountClosedIsTrue = refl
