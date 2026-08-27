module DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact where

------------------------------------------------------------------------
-- FINITE DEPENDENT PAIR ENUMERATION
--
-- A unique finite base enumeration together with a unique finite enumeration
-- of each dependent fibre yields a unique finite enumeration of the Sigma
-- carrier.  This is the theorem needed for proof-free keys such as
--
--   (partition-vector , part-index , occurrence , unit).
--
-- The proof makes block disjointness explicit through the first coordinate;
-- no proof irrelevance or quotient cardinality is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product

------------------------------------------------------------------------
-- Generic membership helpers.

mapMember :
  ∀ {A B : Set} (f : A → B) {x : A} {xs : List A} →
  x ∈ xs → f x ∈ map f xs
mapMember f (Any.here equality) = Any.here equality
mapMember f (Any.there member) = Any.there (mapMember f member)

appendMemberLeft :
  ∀ {A : Set} {x : A} {xs ys : List A} →
  x ∈ xs → x ∈ xs ++ ys
appendMemberLeft {xs = []} ()
appendMemberLeft {xs = _ ∷ _} (Any.here equality) = Any.here equality
appendMemberLeft {xs = _ ∷ xs} (Any.there member) =
  Any.there (appendMemberLeft {xs = xs} member)

appendMemberRight :
  ∀ {A : Set} {x : A} (xs : List A) {ys : List A} →
  x ∈ ys → x ∈ xs ++ ys
appendMemberRight [] member = member
appendMemberRight (_ ∷ xs) member =
  Any.there (appendMemberRight xs member)

allAppend :
  ∀ {A : Set} {P : A → Set} {xs ys : List A} →
  All.All P xs → All.All P ys → All.All P (xs ++ ys)
allAppend All.[] right = right
allAppend (All._∷_ px pxs) right = All._∷_ px (allAppend pxs right)

------------------------------------------------------------------------
-- Unique append under explicit cross-block disjointness.

uniqueAppendDisjoint :
  ∀ {A : Set} {xs ys : List A} →
  Unique xs →
  Unique ys →
  (∀ {x y} → x ∈ xs → y ∈ ys → x ≢ y) →
  Unique (xs ++ ys)
uniqueAppendDisjoint {xs = []} leftUnique rightUnique cross = rightUnique
uniqueAppendDisjoint {xs = x ∷ xs}
    (AllPairs._∷_ fresh tailUnique) rightUnique cross =
  AllPairs._∷_ headFresh tailCombined
  where
  headFreshRight : All.All (λ y → x ≢ y) ys
  headFreshRight =
    All.tabulate
      (λ yMember → cross (Any.here refl) yMember)

  headFresh : All.All (λ y → x ≢ y) (xs ++ ys)
  headFresh = allAppend fresh headFreshRight

  tailCross :
    ∀ {left right} → left ∈ xs → right ∈ ys → left ≢ right
  tailCross leftMember rightMember =
    cross (Any.there leftMember) rightMember

  tailCombined : Unique (xs ++ ys)
  tailCombined =
    uniqueAppendDisjoint tailUnique rightUnique tailCross

------------------------------------------------------------------------
-- Dependent pair enumeration.

pairBlock :
  ∀ {A : Set} {B : A → Set} →
  (x : A) → List (B x) → List (Σ A B)
pairBlock x values = map (λ value → x , value) values

dependentPairs :
  ∀ {A : Set} {B : A → Set} →
  List A → ((x : A) → List (B x)) → List (Σ A B)
dependentPairs [] fibres = []
dependentPairs (x ∷ xs) fibres =
  pairBlock x (fibres x) ++ dependentPairs xs fibres

pairBlockFirst :
  ∀ {A : Set} {B : A → Set}
    (x : A) {pair : Σ A B} {values : List (B x)} →
  pair ∈ pairBlock x values → proj₁ pair ≡ x
pairBlockFirst x (Any.here refl) = refl
pairBlockFirst x (Any.there member) = pairBlockFirst x member

dependentPairsFirstMember :
  ∀ {A : Set} {B : A → Set}
    {xs : List A} {fibres : (x : A) → List (B x)}
    {pair : Σ A B} →
  pair ∈ dependentPairs xs fibres → proj₁ pair ∈ xs
dependentPairsFirstMember {xs = []} ()
dependentPairsFirstMember {xs = x ∷ xs} {fibres} member
  with ∈-++⁻ (pairBlock x (fibres x)) member
... | inj₁ blockMember =
  Any.here (pairBlockFirst x blockMember)
... | inj₂ tailMember =
  Any.there (dependentPairsFirstMember tailMember)

pairBlockUnique :
  ∀ {A : Set} {B : A → Set}
    (x : A) {values : List (B x)} →
  Unique values → Unique (pairBlock x values)
pairBlockUnique x unique =
  UniqueP.map⁺ pairInjective unique
  where
  pairInjective :
    ∀ {left right} → (x , left) ≡ (x , right) → left ≡ right
  pairInjective refl = refl

dependentPairsUnique :
  ∀ {A : Set} {B : A → Set}
    {xs : List A} (fibres : (x : A) → List (B x)) →
  Unique xs →
  ((x : A) → Unique (fibres x)) →
  Unique (dependentPairs xs fibres)
dependentPairsUnique {xs = []} fibres baseUnique fibreUnique = AllPairs.[]
dependentPairsUnique {xs = x ∷ xs} fibres
    (AllPairs._∷_ fresh tailUnique) fibreUnique =
  uniqueAppendDisjoint
    (pairBlockUnique x (fibreUnique x))
    (dependentPairsUnique fibres tailUnique fibreUnique)
    cross
  where
  cross :
    ∀ {left right} →
    left ∈ pairBlock x (fibres x) →
    right ∈ dependentPairs xs fibres →
    left ≢ right
  cross leftMember rightMember equality =
    All.lookup fresh
      (dependentPairsFirstMember rightMember)
      firstEqual
    where
    leftFirst : proj₁ left ≡ x
    leftFirst = pairBlockFirst x leftMember

    sameFirst : proj₁ left ≡ proj₁ right
    sameFirst = cong proj₁ equality

    firstEqual : x ≡ proj₁ right
    firstEqual = trans (sym leftFirst) sameFirst

------------------------------------------------------------------------
-- Membership completeness is compositional: a base member and a fibre member
-- produce a dependent-pair member.
------------------------------------------------------------------------

dependentPairsMember :
  ∀ {A : Set} {B : A → Set}
    {xs : List A} (fibres : (x : A) → List (B x))
    {x : A} {value : B x} →
  x ∈ xs → value ∈ fibres x → (x , value) ∈ dependentPairs xs fibres
dependentPairsMember fibres (Any.here refl) valueMember =
  appendMemberLeft (mapMember (λ value → _ , value) valueMember)
dependentPairsMember fibres (Any.there baseMember) valueMember =
  appendMemberRight _
    (dependentPairsMember fibres baseMember valueMember)

------------------------------------------------------------------------
-- Generic uniqueness for concatMap when an output equality recovers equality
-- of the source base coordinates.  This is the proof-erasing analogue of the
-- dependent-pair theorem above.
------------------------------------------------------------------------

concatMapUniqueRecoverable :
  ∀ {A B : Set}
    {xs : List A}
    (fibres : A → List B) →
  Unique xs →
  ((x : A) → Unique (fibres x)) →
  (∀ {leftSource rightSource : A}
      {leftOutput rightOutput : B} →
    leftOutput ∈ fibres leftSource →
    rightOutput ∈ fibres rightSource →
    leftOutput ≡ rightOutput →
    leftSource ≡ rightSource) →
  Unique (Product.concatMap fibres xs)
concatMapUniqueRecoverable {xs = []} fibres baseUnique fibreUnique recover =
  AllPairs.[]
concatMapUniqueRecoverable {xs = x ∷ xs} fibres
    (AllPairs._∷_ fresh tailUnique) fibreUnique recover =
  uniqueAppendDisjoint
    (fibreUnique x)
    (concatMapUniqueRecoverable fibres tailUnique fibreUnique recover)
    cross
  where
  cross :
    ∀ {left right} →
    left ∈ fibres x →
    right ∈ Product.concatMap fibres xs →
    left ≢ right
  cross leftMember rightMember equality
    with Product.concatMapMemberInverse fibres rightMember
... | source , sourceMember , sourceOutputMember =
  All.lookup fresh sourceMember
    (recover leftMember sourceOutputMember equality)

------------------------------------------------------------------------
-- This owner is finite/list-theoretic only.
------------------------------------------------------------------------
