module DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact where

------------------------------------------------------------------------
-- REPO CROSS-POLLINATION
--
-- The Navier--Stokes Galerkin lane already uses proof-relevant list
-- permutations to justify exact finite reindexing before taking a fold; see
-- NSTriadKNPhysicalOutputFiberPermutationRound35Exact and
-- NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.
--
-- DASHI CONTRIBUTION
--
-- Extract the arithmetic-neutral core needed by the partition lane.  A finite
-- weighted count is invariant under an exact list permutation, and a mapped
-- enumeration may therefore be replaced by its target enumeration without
-- appealing to quotient cardinality, proof irrelevance, or analytic limits.
--
-- This is deliberately generic: the same kernel can be reused for partition
-- deletion fibres, finite spectral reindexings, incidence sums, and other
-- finite double-counting arguments.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
import Data.List.Relation.Unary.Unique.Propositional as Unique
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermP
open import Data.List.Relation.Unary.Any as Any using ()
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong; subst; sym; trans)

------------------------------------------------------------------------
-- Finite natural-valued folds.

foldNat : ∀ {A : Set} → (A → Nat) → List A → Nat
foldNat weight [] = 0
foldNat weight (x ∷ xs) = weight x + foldNat weight xs

foldMap :
  ∀ {A B : Set}
    (weight : B → Nat)
    (reindex : A → B)
    (items : List A) →
  foldNat weight (map reindex items)
  ≡ foldNat (λ item → weight (reindex item)) items
foldMap weight reindex [] = refl
foldMap weight reindex (x ∷ xs) =
  cong (weight (reindex x) +_) (foldMap weight reindex xs)

foldPointwise :
  ∀ {A : Set}
    (left right : A → Nat)
    (items : List A) →
  (∀ item → left item ≡ right item) →
  foldNat left items ≡ foldNat right items
foldPointwise left right [] agreement = refl
foldPointwise left right (x ∷ xs) agreement =
  cong₂ _+_
    (agreement x)
    (foldPointwise left right xs agreement)
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Exact fold invariance under the standard proof-relevant permutation type.

foldPermutationInvariant :
  ∀ {A : Set}
    (weight : A → Nat)
    {left right : List A} →
  left Perm.↭ right →
  foldNat weight left ≡ foldNat weight right
foldPermutationInvariant weight Perm.refl = refl
foldPermutationInvariant weight (Perm.prep x permutation) =
  cong (weight x +_) (foldPermutationInvariant weight permutation)
foldPermutationInvariant weight
    (Perm.swap {ys = ys} x y permutation) =
  trans
    (cong
      (λ tail → weight x + (weight y + tail))
      (foldPermutationInvariant weight permutation))
    (trans
      (sym (NatP.+-assoc (weight x) (weight y) (foldNat weight ys)))
      (trans
        (cong
          (λ pairSum → pairSum + foldNat weight ys)
          (NatP.+-comm (weight x) (weight y)))
        (NatP.+-assoc (weight y) (weight x) (foldNat weight ys))))
foldPermutationInvariant weight (Perm.trans first second) =
  trans
    (foldPermutationInvariant weight first)
    (foldPermutationInvariant weight second)

------------------------------------------------------------------------
-- Mapped reindexing theorem used by fibre-count arguments.

mappedPermutationPreservesFold :
  ∀ {A B : Set}
    (weight : B → Nat)
    (reindex : A → B)
    (source : List A)
    {target : List B} →
  map reindex source Perm.↭ target →
  foldNat (λ item → weight (reindex item)) source
  ≡ foldNat weight target
mappedPermutationPreservesFold weight reindex source permutation =
  trans
    (sym (foldMap weight reindex source))
    (foldPermutationInvariant weight permutation)

weightedMappedPermutationPreservesFold :
  ∀ {A B : Set}
    (sourceWeight : A → Nat)
    (targetWeight : B → Nat)
    (reindex : A → B)
    (source : List A)
    {target : List B} →
  (∀ item → sourceWeight item ≡ targetWeight (reindex item)) →
  map reindex source Perm.↭ target →
  foldNat sourceWeight source ≡ foldNat targetWeight target
weightedMappedPermutationPreservesFold
    sourceWeight targetWeight reindex source weightAgreement permutation =
  trans
    (foldPointwise sourceWeight
      (λ item → targetWeight (reindex item))
      source weightAgreement)
    (mappedPermutationPreservesFold targetWeight reindex source permutation)

------------------------------------------------------------------------
-- Constant-weight specialization: exact permutations preserve finite counts.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = 0
listLength (_ ∷ xs) = 1 + listLength xs

foldOneIsLength :
  ∀ {A : Set} (items : List A) →
  foldNat (λ _ → 1) items ≡ listLength items
foldOneIsLength [] = refl
foldOneIsLength (_ ∷ xs) = cong (1 +_) (foldOneIsLength xs)

permutationPreservesLength :
  ∀ {A : Set} {left right : List A} →
  left Perm.↭ right →
  listLength left ≡ listLength right
permutationPreservesLength {left = left} {right = right} permutation =
  trans
    (sym (foldOneIsLength left))
    (trans
      (foldPermutationInvariant (λ _ → 1) permutation)
      (foldOneIsLength right))

------------------------------------------------------------------------
-- Generic K-free promotion from unique membership equivalence to permutation.
-- This is extracted from the physical-output-fibre closure rather than
-- importing a fluid-specific module into number theory.

removeAt :
  ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → List A
removeAt {xs = _ ∷ xs} (Any.here refl) = xs
removeAt {xs = y ∷ ys} (Any.there member) = y ∷ removeAt member

removeAtPermutation :
  ∀ {A : Set} {x : A} {xs : List A}
    (selected : x ∈ xs) →
  xs Perm.↭ (x ∷ removeAt selected)
removeAtPermutation (Any.here refl) = Perm.refl
removeAtPermutation {x = x} {xs = y ∷ ys} (Any.there selected) =
  Perm.trans
    (Perm.prep y (removeAtPermutation selected))
    (Perm.swap y x Perm.refl)

removeAtMemberOriginal :
  ∀ {A : Set} {x z : A} {xs : List A}
    (selected : x ∈ xs) →
  z ∈ removeAt selected → z ∈ xs
removeAtMemberOriginal (Any.here refl) member = Any.there member
removeAtMemberOriginal (Any.there selected) (Any.here equality) =
  Any.here equality
removeAtMemberOriginal (Any.there selected) (Any.there member) =
  Any.there (removeAtMemberOriginal selected member)

otherMemberSurvivesRemoval :
  ∀ {A : Set} {x z : A} {xs : List A}
    (selected : x ∈ xs) →
  z ∈ xs → z ≢ x → z ∈ removeAt selected
otherMemberSurvivesRemoval (Any.here refl) (Any.here equality) different =
  ⊥-elim (different equality)
otherMemberSurvivesRemoval (Any.here refl) (Any.there member) different = member
otherMemberSurvivesRemoval
    (Any.there selected) (Any.here equality) different =
  Any.here equality
otherMemberSurvivesRemoval
    (Any.there selected) (Any.there member) different =
  Any.there (otherMemberSurvivesRemoval selected member different)

allRemoveAt :
  ∀ {A : Set} {P : A → Set} {x : A} {xs : List A} →
  All.All P xs →
  (selected : x ∈ xs) →
  All.All P (removeAt selected)
allRemoveAt (All._∷_ px pxs) (Any.here refl) = pxs
allRemoveAt (All._∷_ px pxs) (Any.there selected) =
  All._∷_ px (allRemoveAt pxs selected)

removeAtUnique :
  ∀ {A : Set} {x : A} {xs : List A} →
  Unique.Unique xs →
  (selected : x ∈ xs) →
  Unique.Unique (removeAt selected)
removeAtUnique (AllPairs._∷_ fresh rest) (Any.here refl) = rest
removeAtUnique (AllPairs._∷_ fresh rest) (Any.there selected) =
  AllPairs._∷_
    (allRemoveAt fresh selected)
    (removeAtUnique rest selected)

removedElementFresh :
  ∀ {A : Set} {x : A} {xs : List A} →
  Unique.Unique xs →
  (selected : x ∈ xs) →
  x ∉ removeAt selected
removedElementFresh (AllPairs._∷_ fresh rest) (Any.here refl) member =
  All.lookup fresh member refl
removedElementFresh
    (AllPairs._∷_ fresh rest) (Any.there selected) (Any.here equality) =
  All.lookup fresh selected (sym equality)
removedElementFresh
    (AllPairs._∷_ fresh rest) (Any.there selected) (Any.there member) =
  removedElementFresh rest selected member

remainderMemberDifferent :
  ∀ {A : Set} {x z : A} {xs : List A} →
  Unique.Unique xs →
  (selected : x ∈ xs) →
  z ∈ removeAt selected →
  z ≢ x
remainderMemberDifferent unique selected member equality =
  removedElementFresh unique selected
    (subst (λ chosen → chosen ∈ removeAt selected) equality member)

consMemberToTailWhenDifferent :
  ∀ {A : Set} {x z : A} {xs : List A} →
  z ∈ (x ∷ xs) → z ≢ x → z ∈ xs
consMemberToTailWhenDifferent (Any.here equality) different =
  ⊥-elim (different equality)
consMemberToTailWhenDifferent (Any.there member) different = member

uniqueMembershipEquivalenceToPermutation :
  ∀ {A : Set} {xs ys : List A} →
  Unique.Unique xs →
  Unique.Unique ys →
  (∀ {z} → z ∈ xs → z ∈ ys) →
  (∀ {z} → z ∈ ys → z ∈ xs) →
  xs Perm.↭ ys
uniqueMembershipEquivalenceToPermutation
    {xs = []} {ys = []} sourceUnique targetUnique forward backward =
  Perm.refl
uniqueMembershipEquivalenceToPermutation
    {xs = []} {ys = y ∷ ys} sourceUnique targetUnique forward backward
  with backward (Any.here refl)
... | ()
uniqueMembershipEquivalenceToPermutation
    {xs = x ∷ xs} {ys = []} sourceUnique targetUnique forward backward
  with forward (Any.here refl)
... | ()
uniqueMembershipEquivalenceToPermutation
    {xs = x ∷ xs} {ys = y ∷ ys}
    (AllPairs._∷_ sourceFresh sourceTailUnique)
    targetUnique forward backward =
  let
    selected : x ∈ (y ∷ ys)
    selected = forward (Any.here refl)

    targetRemainderUnique : Unique.Unique (removeAt selected)
    targetRemainderUnique = removeAtUnique targetUnique selected

    forwardTail :
      ∀ {z} → z ∈ xs → z ∈ removeAt selected
    forwardTail member =
      otherMemberSurvivesRemoval
        selected
        (forward (Any.there member))
        (λ equality → All.lookup sourceFresh member (sym equality))

    backwardTail :
      ∀ {z} → z ∈ removeAt selected → z ∈ xs
    backwardTail member =
      consMemberToTailWhenDifferent
        (backward (removeAtMemberOriginal selected member))
        (remainderMemberDifferent targetUnique selected member)

    tailPermutation : xs Perm.↭ removeAt selected
    tailPermutation =
      uniqueMembershipEquivalenceToPermutation
        sourceTailUnique targetRemainderUnique forwardTail backwardTail
  in
  Perm.trans
    (Perm.prep x tailPermutation)
    (PermP.↭-sym (removeAtPermutation selected))
