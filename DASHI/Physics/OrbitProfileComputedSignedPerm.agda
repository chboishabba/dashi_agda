module DASHI.Physics.OrbitProfileComputedSignedPerm where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Bool using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; map; filterᵇ; length)
open import Data.Nat.Properties as NatP using (_≤?_) 
open import Data.Integer.Base using (ℤ; +_)
open import Data.Integer using (_≟_; -_)
open import Data.Vec using (Vec; []; _∷_; head; tail)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.SignatureFromMask as SFM
open import DASHI.Physics.ShellOrbitProfileGenerator as SOPG
open import DASHI.Physics.SignedPerm4 as SP

------------------------------------------------------------------------
-- Basic list utilities

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
-- Shell predicates for |Q| = k

mask31 : Vec IMQ.Sign 4
mask31 = SFM.oneMinusRestPlus {m = suc (suc (suc zero))}

isShell : (k : Nat) → Vec Trit 4 → Bool
isShell k x with IMQ.Qσ mask31 x ≟ (+ k)
... | yes _ = true
... | no _ with IMQ.Qσ mask31 x ≟ (- (+ k))
... | yes _ = true
... | no _  = false

shellList : Nat → List (Vec Trit 4)
shellList k = filterᵇ (isShell k) (allVecTrit 4)

------------------------------------------------------------------------
-- Signed permutations: permute spatial coords + flip all coords

flipTrit : Bool → Trit → Trit
flipTrit true  t = t
flipTrit false t = inv t

flipBy3 : Vec Bool 3 → Vec Trit 3 → Vec Trit 3
flipBy3 (f1 ∷ f2 ∷ f3 ∷ []) (a ∷ b ∷ c ∷ []) =
  flipTrit f1 a ∷ flipTrit f2 b ∷ flipTrit f3 c ∷ []

actSigned4 : SP.SignedPerm4 → Vec Trit 4 → Vec Trit 4
actSigned4 sp (t ∷ s1 ∷ s2 ∷ s3 ∷ []) =
  flipTrit (SP.SignedPerm4.flipT sp) t ∷
  flipBy3 (SP.SignedPerm4.flipS sp)
    (SP.permute3 (SP.SignedPerm4.perm sp) (s1 ∷ s2 ∷ s3 ∷ []))

------------------------------------------------------------------------
-- All flips (2^4) and signed permutations

allBool : List Bool
allBool = false ∷ true ∷ []

allVecBool : ∀ (n : Nat) → List (Vec Bool n)
allVecBool zero = [] ∷ []
allVecBool (suc n) =
  concatMap
    (λ b → map (λ v → b ∷ v) (allVecBool n))
    allBool

allFlips3 : List (Vec Bool 3)
allFlips3 = allVecBool 3

allSignedPerm4 : List SP.SignedPerm4
allSignedPerm4 =
  concatMap
    (λ p →
      concatMap
        (λ ft → map (λ fs → record { perm = p ; flipT = ft ; flipS = fs }) allFlips3)
        allBool)
    SP.allPerm3

------------------------------------------------------------------------
-- Orbit sizes under the signed action list

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
  (xs : List (Vec Trit 4)) →
  List Nat
{-# TERMINATING #-}
orbitSizes [] = []
orbitSizes (x ∷ xs) =
  let
    orb = nub decEqVec (map (λ sp → actSigned4 sp x) allSignedPerm4)
    rest = filterᵇ (λ z → not (member decEqVec z orb)) xs
  in
  length orb ∷ orbitSizes rest
  where
    not : Bool → Bool
    not true = false
    not false = true

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
-- Computed profiles for (p,q) = (3,1)

shell1_p3_q1_computed : List Nat
shell1_p3_q1_computed =
  sortDesc (orbitSizes (shellList 1))

shell2_p3_q1_computed : List Nat
shell2_p3_q1_computed =
  sortDesc (orbitSizes (shellList 2))
