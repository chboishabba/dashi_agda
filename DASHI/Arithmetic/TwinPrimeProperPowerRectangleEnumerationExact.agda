module DASHI.Arithmetic.TwinPrimeProperPowerRectangleEnumerationExact where

------------------------------------------------------------------------
-- CT11, FINITE RECTANGULAR CANDIDATE ENUMERATOR AND EXACT CARDINALITY
--
-- ORIGINAL OWNERS (import, do not duplicate): 
--  * DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact.listLength
--  * DASHI.Analysis.RiemannPrimePowerArithmetic.natPow
--  * CT10 bound: TwinPrimeProperPowerRectangleBoundExact
--
-- The coordinate rectangle contains all positive bases 1..B, and
-- exponent-index candidates k=0..E-1 (actual exponent k+2).
-- It deliberately OVERCOUNTS composite bases and repeated values.
-- This makes it suitable for a later upper bound, not a claim of
-- unique prime-power representation or completed M15.
--
-- Source-written, Agda kernel pending. No postulate, no ESD edit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)\nopen import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)\nopen import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)\nopen import Data.Nat.Base using (_≤_; z≤n; s≤s)\nopen import Data.Empty using (⊥)\nopen import Data.Sum using (_⊎_; inj₁; inj₂)\nimport Data.Nat.Properties as NatP\nopen import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; subst; sym)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Data.List.Base using (_++_; map)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Analysis.RiemannPrimePowerArithmetic as Power
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Root
import DASHI.Arithmetic.TwinPrimeProperPowerFloorRootBoundExact as Bounds

-- All exponent indices 0..E-1 appear, in descending order.
powerRow : Nat → Nat → List (Nat × Nat)
powerRow base zero = []
powerRow base (suc e) = (base , e) ∷ powerRow base e

powerRowLength : (base e : Nat) →
  Reindex.listLength (powerRow base e) ≡ e
powerRowLength base zero = refl
powerRowLength base (suc e) =
  cong suc (powerRowLength base e)

-- All bases 1..B, each paired with all E exponent indices.
powerRectangle : Nat → Nat → List (Nat × Nat)
powerRectangle zero e = []
powerRectangle (suc b) e =
  powerRow (suc b) e ++ powerRectangle b e

appendLength :
  {A : Set} (xs ys : List A) →
  Reindex.listLength (xs ++ ys)
    ≡ Reindex.listLength xs + Reindex.listLength ys
appendLength [] ys = refl
appendLength (x ∷ xs) ys = cong suc (appendLength xs ys)

powerRectangleLength : (b e : Nat) →
  Reindex.listLength (powerRectangle b e) ≡ b * e
powerRectangleLength zero e = refl
powerRectangleLength (suc b) e =
  trans
    (appendLength (powerRow (suc b) e) (powerRectangle b e))
    (cong₂ _+_
      (powerRowLength (suc b) e)
      (powerRectangleLength b e))

powerValue : Nat × Nat → Nat
powerValue (base , exponentIndex) =
  Power.natPow base (suc (suc exponentIndex))

-- Enumerates the candidate powers without either deduplicating
-- or asserting they are prime powers (bases may be composite).
powerValueRectangle : Nat → Nat → List Nat
powerValueRectangle b e = map powerValue (powerRectangle b e)

mapLength :
  {A B : Set} (f : A → B) (xs : List A) →
  Reindex.listLength (map f xs) ≡ Reindex.listLength xs
mapLength f [] = refl
mapLength f (x ∷ xs) = cong suc (mapLength f xs)

powerValueRectangleLength : (b e : Nat) →
  Reindex.listLength (powerValueRectangle b e) ≡ b * e
powerValueRectangleLength b e =
  trans
    (mapLength powerValue (powerRectangle b e))
    (powerRectangleLength b e)

-- Independently filtered candidate lists cannot exceed the full
-- rectangle count. This is a pure finite fact, not analytic density.
filterCandidate : {A : Set} → (A → Bool) → List A → List A
filterCandidate predicate [] = []
filterCandidate predicate (x ∷ xs) with predicate x
... | true = x ∷ filterCandidate predicate xs
... | false = filterCandidate predicate xs

filteredLengthAtMost :
  {A : Set} (predicate : A → Bool) (xs : List A) →
  Reindex.listLength (filterCandidate predicate xs)
    ≤ Reindex.listLength xs
filteredLengthAtMost predicate [] = z≤n
filteredLengthAtMost predicate (x ∷ xs)
  with predicate x
... | true = s≤s (filteredLengthAtMost predicate xs)
... | false =
  NatP.≤-step (filteredLengthAtMost predicate xs)

filteredRectangleAtMost :
  (b e : Nat) (predicate : (Nat × Nat) → Bool) →
  Reindex.listLength (filterCandidate predicate (powerRectangle b e))
    ≤ b * e
filteredRectangleAtMost b e predicate =
  subst
    (λ n → Reindex.listLength
      (filterCandidate predicate (powerRectangle b e)) ≤ n)
    (powerRectangleLength b e)
    (filteredLengthAtMost predicate (powerRectangle b e))

------------------------------------------------------------------------
-- CT11 CONDITIONAL COMPLETE COORDINATE COVERAGE.
--
-- Each pair (base,k) in its exact rectangle is physically present
-- in the enumerator. This is the missing finite membership half
-- needed to move from a power bound to a cardinality inequality.
------------------------------------------------------------------------

data _member_ {A : Set} (x : A) : List A → Set where
  memberHead : ∀ {xs} → x member (x ∷ xs)
  memberTail : ∀ {y xs} → x member xs → x member (y ∷ xs)

memberAppendLeft :
  {A : Set} {x : A} (xs ys : List A) →
  x member xs → x member (xs ++ ys)
memberAppendLeft [] ys ()
memberAppendLeft (x ∷ xs) ys memberHead = memberHead
memberAppendLeft (y ∷ xs) ys (memberTail proof) =
  memberTail (memberAppendLeft xs ys proof)

memberAppendRight :
  {A : Set} {x : A} (xs ys : List A) →
  x member ys → x member (xs ++ ys)
memberAppendRight [] ys proof = proof
memberAppendRight (y ∷ xs) ys proof =
  memberTail (memberAppendRight xs ys proof)

rowContainsIndex :
  (base e k : Nat) → suc k ≤ e →
  (base , k) member powerRow base e
rowContainsIndex base zero k ()
rowContainsIndex base (suc e) k (s≤s k≤e)
  with k NatP.≟ e
... | yes equal =
  subst
    (λ i → (base , i) member powerRow base (suc e))
    (sym equal)
    memberHead
... | no different =
  memberTail
    (rowContainsIndex base e k
      (Root.strictFromLeDifferent k≤e different))

rectangleContainsIndex :
  (b e base k : Nat) →
  suc zero ≤ base → base ≤ b → suc k ≤ e →
  (base , k) member powerRectangle b e
rectangleContainsIndex zero e zero k () baseBound exponentBound
rectangleContainsIndex zero e (suc base) k positive () exponentBound
rectangleContainsIndex (suc b) e base k positive baseBound exponentBound
  with base NatP.≟ suc b
... | yes equal =
  subst
    (λ i → (i , k) member powerRectangle (suc b) e)
    (sym equal)
    (memberAppendLeft
      (powerRow (suc b) e) (powerRectangle b e)
      (rowContainsIndex (suc b) e k exponentBound))
... | no different =
  memberAppendRight
    (powerRow (suc b) e) (powerRectangle b e)
    (rectangleContainsIndex b e base k positive
      (Root.strictBelowSuccessorToLe
        (Root.strictFromLeDifferent baseBound different))
      exponentBound)

mapPreservesMember :
  {A B : Set} (f : A → B) {x : A} (xs : List A) →
  x member xs → f x member map f xs
mapPreservesMember f [] ()
mapPreservesMember f (x ∷ xs) memberHead = memberHead
mapPreservesMember f (y ∷ xs) (memberTail proof) =
  memberTail (mapPreservesMember f xs proof)

powerValueRectangleCovers :
  (b e base k : Nat) →
  suc zero ≤ base → base ≤ b → suc k ≤ e →
  Power.natPow base (suc (suc k))
    member powerValueRectangle b e
powerValueRectangleCovers b e base k positive baseBound exponentBound =
  mapPreservesMember powerValue (powerRectangle b e)
    (rectangleContainsIndex b e base k
      positive baseBound exponentBound)

------------------------------------------------------------------------
-- CT10 + CT11: every proper power with a supplied exponent cutoff
-- occurs in the precise rectangle whose length is root * cutoff.
-- The final *numerical* exponent cutoff (floor-log2) still needs
-- a separate proof. No uniqueness/cardinality of distinct values
-- is silently inferred from list membership alone.
------------------------------------------------------------------------

properPowerCoveredByRootRectangle :
  (basePredecessor k upper exponentCutoff : Nat) →
  Power.natPow (suc (suc basePredecessor)) (suc (suc k)) ≤ upper →
  suc k ≤ exponentCutoff →
  Power.natPow (suc (suc basePredecessor)) (suc (suc k))
    member powerValueRectangle
      (Root.floorSquareRoot upper) exponentCutoff
properPowerCoveredByRootRectangle basePredecessor k upper cutoff
    powerBound exponentBound =
  powerValueRectangleCovers
    (Root.floorSquareRoot upper) cutoff
    (suc (suc basePredecessor)) k
    (s≤s z≤n)
    (Bounds.properPowerBaseLeFloorRoot
      (suc basePredecessor) k upper powerBound)
    exponentBound

------------------------------------------------------------------------
-- CT11: executable duplicate-eliminating numeric image / length bound.
--
-- Selecting one representative of each repeated candidate value can
-- only DECREASE the candidate count. We prove this exact inequality
-- directly, not by importing an unverified analytic counting bound.
------------------------------------------------------------------------

-- Structurally recursive insertion: do NOT recurse on a filtered
-- argument. The original candidate implementation did so, which
-- is not acceptable to Agda's termination checker.
insertIfFresh : Nat → List Nat → List Nat
insertIfFresh x [] = x ∷ []
insertIfFresh x (y ∷ ys) with x NatP.≟ y
... | yes equal = y ∷ ys
... | no different = y ∷ insertIfFresh x ys

dedupPowerValues : List Nat → List Nat
dedupPowerValues [] = []
dedupPowerValues (x ∷ xs) =
  insertIfFresh x (dedupPowerValues xs)

insertIfFreshLengthAtMost :
  (x : Nat) (xs : List Nat) →
  Reindex.listLength (insertIfFresh x xs)
    ≤ suc (Reindex.listLength xs)
insertIfFreshLengthAtMost x [] = s≤s z≤n
insertIfFreshLengthAtMost x (y ∷ ys) with x NatP.≟ y
... | yes equal = NatP.n≤1+n (suc (Reindex.listLength ys))
... | no different =
  s≤s (insertIfFreshLengthAtMost x ys)

dedupLengthAtMost :
  (xs : List Nat) →
  Reindex.listLength (dedupPowerValues xs)
    ≤ Reindex.listLength xs
dedupLengthAtMost [] = z≤n
dedupLengthAtMost (x ∷ xs) =
  NatP.≤-trans
    (insertIfFreshLengthAtMost x (dedupPowerValues xs))
    (s≤s (dedupLengthAtMost xs))

properPowerCandidateDistinctCount : Nat → Nat → Nat
properPowerCandidateDistinctCount b e =
  Reindex.listLength (dedupPowerValues (powerValueRectangle b e))

properPowerCandidateDistinctCountBound :
  (b e : Nat) →
  properPowerCandidateDistinctCount b e ≤ b * e
properPowerCandidateDistinctCountBound b e =
  subst
    (λ n → properPowerCandidateDistinctCount b e ≤ n)
    (powerValueRectangleLength b e)
    (dedupLengthAtMost (powerValueRectangle b e))

------------------------------------------------------------------------
-- CT11 DEDUP EQUIVALENCE: true membership equivalence, plus no repeats.
-- Original list/number evidence is preserved; unlike a cardinality
-- analogy, these are actual finite proof terms for our source program.
------------------------------------------------------------------------

insertContainsNew :
  (x : Nat) (xs : List Nat) →
  x member insertIfFresh x xs
insertContainsNew x [] = memberHead
insertContainsNew x (y ∷ ys) with x NatP.≟ y
... | yes equal =
  subst
    (λ value → value member (y ∷ ys))
    (sym equal)
    memberHead
... | no different =
  memberTail (insertContainsNew x ys)

insertPreservesOld :
  (x : Nat) {value : Nat} (xs : List Nat) →
  value member xs → value member insertIfFresh x xs
insertPreservesOld x [] ()
insertPreservesOld x (y ∷ ys) proof with x NatP.≟ y
... | yes equal = proof
... | no different with proof
...   | memberHead = memberHead
...   | memberTail tailMember =
  memberTail (insertPreservesOld x ys tailMember)

insertMembershipBack :
  (x : Nat) {value : Nat} (xs : List Nat) →
  value member insertIfFresh x xs →
  (value ≡ x) ⊎ (value member xs)
insertMembershipBack x [] memberHead = inj₁ refl
insertMembershipBack x (y ∷ ys) proof with x NatP.≟ y
... | yes equal = inj₂ proof
... | no different with proof
...   | memberHead = inj₂ memberHead
...   | memberTail tailMember with
    insertMembershipBack x ys tailMember
...     | inj₁ sameNew = inj₁ sameNew
...     | inj₂ oldMember = inj₂ (memberTail oldMember)

dedupPreservesMember :
  {value : Nat} (xs : List Nat) →
  value member xs → value member dedupPowerValues xs
dedupPreservesMember [] ()
dedupPreservesMember (x ∷ xs) memberHead =
  insertContainsNew x (dedupPowerValues xs)
dedupPreservesMember (x ∷ xs) (memberTail original) =
  insertPreservesOld x (dedupPowerValues xs)
    (dedupPreservesMember xs original)

dedupMemberComesFromOriginal :
  {value : Nat} (xs : List Nat) →
  value member dedupPowerValues xs → value member xs
dedupMemberComesFromOriginal [] ()
dedupMemberComesFromOriginal (x ∷ xs) inImage
  with insertMembershipBack x (dedupPowerValues xs) inImage
... | inj₁ sameNew =
  subst
    (λ v → v member (x ∷ xs))
    (sym sameNew)
    memberHead
... | inj₂ oldImage =
  memberTail (dedupMemberComesFromOriginal xs oldImage)

data DistinctValues : List Nat → Set where
  distinctEmpty : DistinctValues []
  distinctCons :
    ∀ {x xs} →
    (x member xs → ⊥) →
    DistinctValues xs →
    DistinctValues (x ∷ xs)

insertPreservesDistinct :
  (x : Nat) (xs : List Nat) →
  DistinctValues xs → DistinctValues (insertIfFresh x xs)
insertPreservesDistinct x [] distinctEmpty =
  distinctCons (λ ()) distinctEmpty
insertPreservesDistinct x (y ∷ ys)
    (distinctCons yFresh tailDistinct)
  with x NatP.≟ y
... | yes equal = distinctCons yFresh tailDistinct
... | no different =
  distinctCons
    (λ inInserted →
      caseInsert (insertMembershipBack x ys inInserted))
    (insertPreservesDistinct x ys tailDistinct)
  where
    caseInsert :
      (y ≡ x) ⊎ (y member ys) → ⊥
    caseInsert (inj₁ yEqualsX) = different (sym yEqualsX)
    caseInsert (inj₂ yOld) = yFresh yOld

dedupValuesDistinct :
  (xs : List Nat) →
  DistinctValues (dedupPowerValues xs)
dedupValuesDistinct [] = distinctEmpty
dedupValuesDistinct (x ∷ xs) =
  insertPreservesDistinct x (dedupPowerValues xs)
    (dedupValuesDistinct xs)
