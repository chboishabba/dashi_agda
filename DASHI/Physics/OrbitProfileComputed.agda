module DASHI.Physics.OrbitProfileComputed where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Data.List.Base using (List; []; _∷_; map; filterᵇ; length)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (_≤?_)
open import Data.Vec using (Vec; []; _∷_; head; tail)
open import Data.Integer.Base using (ℤ; +_; -1ℤ)
open import Data.Integer using (_≟_; -_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.OrbitShellPredicate as OSP
open import DASHI.Physics.DimensionBoundAssumptions as DBA
open import DASHI.Physics.ShellOrbitProfileGenerator as SOPG

------------------------------------------------------------------------
-- Basic list utilities (kept local to avoid extra imports)

concat : ∀ {A : Set} → List (List A) → List A
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss
  where
    _++_ : ∀ {A : Set} → List A → List A → List A
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap f xs = concat (map f xs)

------------------------------------------------------------------------
-- Decidable equality for Trit and Vec

decEqTrit : (x y : Trit) → Dec (x ≡ y)
decEqTrit neg neg = yes refl
decEqTrit neg zer = no (λ ())
decEqTrit neg pos = no (λ ())
decEqTrit zer neg = no (λ ())
decEqTrit zer zer = yes refl
decEqTrit zer pos = no (λ ())
decEqTrit pos neg = no (λ ())
decEqTrit pos zer = no (λ ())
decEqTrit pos pos = yes refl

decEqVec : ∀ {n : Nat} → (x y : Vec Trit n) → Dec (x ≡ y)
decEqVec [] [] = yes refl
decEqVec (x ∷ xs) (y ∷ ys) with decEqTrit x y
... | no neq = no (λ eq → neq (cong head eq))
... | yes refl with decEqVec xs ys
... | no neq = no (λ eq → neq (cong tail eq))
... | yes refl = yes refl

------------------------------------------------------------------------
-- Membership / nub

member : ∀ {A : Set} → ((x y : A) → Dec (x ≡ y)) → A → List A → Bool
member dec x [] = false
member dec x (y ∷ ys) with dec x y
... | yes _ = true
... | no _  = member dec x ys

nub : ∀ {A : Set} → ((x y : A) → Dec (x ≡ y)) → List A → List A
nub dec [] = []
nub dec (x ∷ xs) with member dec x xs
... | true  = nub dec xs
... | false = x ∷ nub dec xs

------------------------------------------------------------------------
-- Enumerate all Vec Trit n

allTrit : List Trit
allTrit = neg ∷ zer ∷ pos ∷ []

allVecTrit : ∀ (n : Nat) → List (Vec Trit n)
allVecTrit zero = [] ∷ []
allVecTrit (suc n) =
  concatMap
    (λ t → map (λ v → t ∷ v) (allVecTrit n))
    allTrit

------------------------------------------------------------------------
-- Shell list from a mask

isShell : ∀ {m : Nat} → Nat → Vec IMQ.Sign m → Vec Trit m → Bool
isShell k σ x with IMQ.Qσ σ x ≟ (+ k)
... | yes _ = true
... | no _ with IMQ.Qσ σ x ≟ - (+ k)
... | yes _ = true
... | no _  = false

shellList : ∀ {m : Nat} → Nat → Vec IMQ.Sign m → List (Vec Trit m)
shellList {m} k σ = filterᵇ (isShell k σ) (allVecTrit m)

shell1List : ∀ {m : Nat} → Vec IMQ.Sign m → List (Vec Trit m)
shell1List σ = shellList 1 σ

------------------------------------------------------------------------
-- Orbit sizes under a finite action list

orbitSizes :
  ∀ {A X : Set} →
  (dec : (x y : X) → Dec (x ≡ y)) →
  (gs : List A) →
  (act : A → X → X) →
  List X →
  List Nat
{-# TERMINATING #-}
orbitSizes dec gs act [] = []
orbitSizes dec gs act (x ∷ xs) =
  let
    orb = nub dec (map (λ g → act g x) gs)
    rest = filterᵇ (λ z → not (member dec z orb)) xs
  in
  length orb ∷ orbitSizes dec gs act rest
  where
    not : Bool → Bool
    not true = false
    not false = true

------------------------------------------------------------------------
-- Simple descending sort for Nat lists

insertDesc : Nat → List Nat → List Nat
insertDesc x [] = x ∷ []
insertDesc x (y ∷ ys) with x NatP.≤? y
... | yes _ = y ∷ insertDesc x ys
... | no _  = x ∷ y ∷ ys

sortDesc : List Nat → List Nat
sortDesc [] = []
sortDesc (x ∷ xs) = insertDesc x (sortDesc xs)

------------------------------------------------------------------------
-- Concrete Bool action: invVec toggle

actBool : ∀ {m : Nat} → Bool → Vec Trit m → Vec Trit m
actBool true  x = RTC.invVec x
actBool false x = x

bools : List Bool
bools = false ∷ true ∷ []

------------------------------------------------------------------------
-- Computed profile for the Bool action on Shell1

orbitProfileBool :
  ∀ {m : Nat} →
  Vec IMQ.Sign m →
  DBA.ShellOrbitProfile m
orbitProfileBool σ =
  let
    shell = shell1List σ
    sizes = orbitSizes decEqVec bools actBool shell
    sizesSorted = sortDesc sizes
  in
  SOPG.profileFromSorted {m = _} sizesSorted
