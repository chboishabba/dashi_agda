module DASHI.Physics.OrbitProfileComputedTailPerm where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Bool using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; map; filterᵇ; length)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat.Properties as NatP using (_≤?_)
open import Data.Integer.Base using (ℤ; +_; -1ℤ)
open import Data.Integer using (_≟_; -_)
open import Data.Vec using (Vec; []; _∷_; head; tail)
open import Data.Fin as Fin using (Fin)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.OrbitShellPredicate as OSP
open import DASHI.Physics.DimensionBoundAssumptions as DBA
open import DASHI.Physics.ShellOrbitProfileGenerator as SOPG
open import DASHI.Physics.SignatureFromMask as SFM
open import DASHI.Geometry.ShiftIsotropyTailPerm as TP

------------------------------------------------------------------------
-- Enumerate all Vec Trit n (3^n)

concat : ∀ {A : Set} → List (List A) → List A
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss
  where
    _++_ : ∀ {A : Set} → List A → List A → List A
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap f xs = concat (map f xs)

allTrit : List Trit
allTrit = neg ∷ zer ∷ pos ∷ []

allVecTrit : ∀ (n : Nat) → List (Vec Trit n)
allVecTrit zero = [] ∷ []
allVecTrit (suc n) =
  concatMap
    (λ t → map (λ v → t ∷ v) (allVecTrit n))
    allTrit

------------------------------------------------------------------------
-- Decidable equality for Vec Trit (needed for orbit partitioning)

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
-- Shell list and orbit sizes

isShell : ∀ {m : Nat} → Nat → Vec IMQ.Sign m → Vec Trit m → Bool
isShell k σ x with IMQ.Qσ σ x ≟ (+ k)
... | yes _ = true
... | no _ with IMQ.Qσ σ x ≟ - (+ k)
... | yes _ = true
... | no _  = false

shellList : ∀ {m : Nat} → Nat → Vec IMQ.Sign m → List (Vec Trit m)
shellList {m} k σ = filterᵇ (isShell k σ) (allVecTrit m)

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

orbitSizes :
  ∀ {m k : Nat} →
  List (TP.Perm k) →
  List (Vec Trit (m + k)) →
  List Nat
orbitSizes {m} {k} ps xs =
  map (λ x → length (nub decEqVec (map (λ p → TP.actTailPerm {m} {k} p x) ps))) xs

------------------------------------------------------------------------
-- Sort sizes descending (simple insertion sort)

insertDesc : Nat → List Nat → List Nat
insertDesc x [] = x ∷ []
insertDesc x (y ∷ ys) with x NatP.≤? y
... | yes _ = y ∷ insertDesc x ys
... | no _  = x ∷ y ∷ ys

sortDesc : List Nat → List Nat
sortDesc [] = []
sortDesc (x ∷ xs) = insertDesc x (sortDesc xs)

------------------------------------------------------------------------
-- Computed profile under tail permutations

allPerms : (k : Nat) → List (TP.Perm k)
allPerms zero = [] ∷ []
allPerms (suc zero) =
  let f0 : Fin 1
      f0 = Fin.zero
  in (f0 ∷ []) ∷ []
allPerms (suc (suc (suc zero))) =
  let
    f0 : Fin 3
    f0 = Fin.zero
    f1 : Fin 3
    f1 = Fin.suc Fin.zero
    f2 : Fin 3
    f2 = Fin.suc (Fin.suc Fin.zero)

    p0 = f0 ∷ f1 ∷ f2 ∷ []
    p1 = f0 ∷ f2 ∷ f1 ∷ []
    p2 = f1 ∷ f0 ∷ f2 ∷ []
    p3 = f1 ∷ f2 ∷ f0 ∷ []
    p4 = f2 ∷ f0 ∷ f1 ∷ []
    p5 = f2 ∷ f1 ∷ f0 ∷ []
  in
  p0 ∷ p1 ∷ p2 ∷ p3 ∷ p4 ∷ p5 ∷ []
allPerms (suc (suc (suc (suc zero)))) =
  let
    f0 : Fin 4
    f0 = Fin.zero
    f1 : Fin 4
    f1 = Fin.suc Fin.zero
    f2 : Fin 4
    f2 = Fin.suc (Fin.suc Fin.zero)
    f3 : Fin 4
    f3 = Fin.suc (Fin.suc (Fin.suc Fin.zero))

    -- all 24 permutations of [f0,f1,f2,f3]
    p0  = f0 ∷ f1 ∷ f2 ∷ f3 ∷ []
    p1  = f0 ∷ f1 ∷ f3 ∷ f2 ∷ []
    p2  = f0 ∷ f2 ∷ f1 ∷ f3 ∷ []
    p3  = f0 ∷ f2 ∷ f3 ∷ f1 ∷ []
    p4  = f0 ∷ f3 ∷ f1 ∷ f2 ∷ []
    p5  = f0 ∷ f3 ∷ f2 ∷ f1 ∷ []

    p6  = f1 ∷ f0 ∷ f2 ∷ f3 ∷ []
    p7  = f1 ∷ f0 ∷ f3 ∷ f2 ∷ []
    p8  = f1 ∷ f2 ∷ f0 ∷ f3 ∷ []
    p9  = f1 ∷ f2 ∷ f3 ∷ f0 ∷ []
    p10 = f1 ∷ f3 ∷ f0 ∷ f2 ∷ []
    p11 = f1 ∷ f3 ∷ f2 ∷ f0 ∷ []

    p12 = f2 ∷ f0 ∷ f1 ∷ f3 ∷ []
    p13 = f2 ∷ f0 ∷ f3 ∷ f1 ∷ []
    p14 = f2 ∷ f1 ∷ f0 ∷ f3 ∷ []
    p15 = f2 ∷ f1 ∷ f3 ∷ f0 ∷ []
    p16 = f2 ∷ f3 ∷ f0 ∷ f1 ∷ []
    p17 = f2 ∷ f3 ∷ f1 ∷ f0 ∷ []

    p18 = f3 ∷ f0 ∷ f1 ∷ f2 ∷ []
    p19 = f3 ∷ f0 ∷ f2 ∷ f1 ∷ []
    p20 = f3 ∷ f1 ∷ f0 ∷ f2 ∷ []
    p21 = f3 ∷ f1 ∷ f2 ∷ f0 ∷ []
    p22 = f3 ∷ f2 ∷ f0 ∷ f1 ∷ []
    p23 = f3 ∷ f2 ∷ f1 ∷ f0 ∷ []
  in
  p0  ∷ p1  ∷ p2  ∷ p3  ∷ p4  ∷ p5  ∷
  p6  ∷ p7  ∷ p8  ∷ p9  ∷ p10 ∷ p11 ∷
  p12 ∷ p13 ∷ p14 ∷ p15 ∷ p16 ∷ p17 ∷
  p18 ∷ p19 ∷ p20 ∷ p21 ∷ p22 ∷ p23 ∷ []
allPerms _ = []

orbitProfileTailPerm :
  ∀ {m k : Nat} → Vec IMQ.Sign (m + k) → DBA.ShellOrbitProfile (m + k)
orbitProfileTailPerm {m} {k} σ =
  let
    shell = shellList 1 σ
    sizes = orbitSizes {m} {k} (allPerms k) shell
  in
  SOPG.profileFromSorted (sortDesc sizes)

mask31 : Vec IMQ.Sign 4
mask31 = SFM.oneMinusRestPlus {m = suc (suc (suc zero))}

shell1_p3_q1_tailperm_computed : List Nat
shell1_p3_q1_tailperm_computed =
  sortDesc (orbitSizes {m = 1} {k = 3} (allPerms 3) (shellList 1 mask31))

shell2_p3_q1_tailperm_computed : List Nat
shell2_p3_q1_tailperm_computed =
  sortDesc (orbitSizes {m = 1} {k = 3} (allPerms 3) (shellList 2 mask31))
