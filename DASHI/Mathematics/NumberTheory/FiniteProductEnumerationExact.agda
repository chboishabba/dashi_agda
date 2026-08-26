module DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact where

------------------------------------------------------------------------
-- REPO CROSS-POLLINATION
--
-- BalabanPeriodicLatticeEnumeration already proves the constructive pattern
--
--   allFin -> concatMap -> nested finite products -> completeness,
--
-- while NSPeriodicConcreteCutoffCubeCarrier separately proves Cartesian
-- completeness/no-duplicates for finite cutoff carriers.
--
-- This owner extracts the domain-neutral completeness spine needed by the
-- partition multiplicity box.  It deliberately knows nothing about lattices,
-- Fourier modes, partitions, or asymptotics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.Vec.Base as Vec

------------------------------------------------------------------------
-- Generic finite-list membership transport.

mapMember :
  ∀ {A B : Set}
    (f : A → B) {x : A} {xs : List A} →
  x ∈ xs → f x ∈ map f xs
mapMember f (Any.here equality) = Any.here equality
mapMember f (Any.there member) = Any.there (mapMember f member)

appendMemberLeft :
  ∀ {A : Set} {x : A} {xs ys : List A} →
  x ∈ xs → x ∈ (xs ++ ys)
appendMemberLeft {xs = []} ()
appendMemberLeft {xs = _ ∷ _} (Any.here equality) = Any.here equality
appendMemberLeft {xs = _ ∷ xs} (Any.there member) =
  Any.there (appendMemberLeft {xs = xs} member)

appendMemberRight :
  ∀ {A : Set} {x : A} (xs : List A) {ys : List A} →
  x ∈ ys → x ∈ (xs ++ ys)
appendMemberRight [] member = member
appendMemberRight (_ ∷ xs) member =
  Any.there (appendMemberRight xs member)

concatMap :
  ∀ {A B : Set} → (A → List B) → List A → List B
concatMap f [] = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

concatMapMember :
  ∀ {A B : Set}
    (f : A → List B)
    {x : A} {xs : List A} {y : B} →
  x ∈ xs → y ∈ f x → y ∈ concatMap f xs
concatMapMember f (Any.here refl) yMember =
  appendMemberLeft yMember
concatMapMember f (Any.there xMember) yMember =
  appendMemberRight _ (concatMapMember f xMember yMember)

------------------------------------------------------------------------
-- Canonical enumeration of every Fin n coordinate.

allFin : (n : Nat) → List (Fin n)
allFin zero = []
allFin (suc n) = fzero ∷ map fsuc (allFin n)

allFinComplete :
  ∀ {n : Nat} (index : Fin n) → index ∈ allFin n
allFinComplete {suc n} fzero = Any.here refl
allFinComplete {suc n} (fsuc index) =
  Any.there (mapMember fsuc (allFinComplete index))

------------------------------------------------------------------------
-- Finite vector powers.
--
-- vectorPower coordinates d enumerates coordinates^d.  The proof below is
-- intentionally phrased using a pointwise membership witness, making it useful
-- for any finite coordinate alphabet, not only Fin n.

vectorPower :
  ∀ {A : Set} → List A → (dimension : Nat) → List (Vec.Vec A dimension)
vectorPower coordinates zero = Vec.[] ∷ []
vectorPower coordinates (suc dimension) =
  concatMap
    (λ coordinate → map (Vec._∷_ coordinate) (vectorPower coordinates dimension))
    coordinates

data CoordinatesFrom {A : Set} (coordinates : List A) :
    ∀ {dimension : Nat} → Vec.Vec A dimension → Set where
  coordinates[] : CoordinatesFrom coordinates Vec.[]
  coordinates∷ :
    ∀ {dimension} {head : A} {tail : Vec.Vec A dimension} →
    head ∈ coordinates →
    CoordinatesFrom coordinates tail →
    CoordinatesFrom coordinates (head Vec.∷ tail)

vectorPowerComplete :
  ∀ {A : Set} {coordinates : List A}
    {dimension : Nat} (vector : Vec.Vec A dimension) →
  CoordinatesFrom coordinates vector →
  vector ∈ vectorPower coordinates dimension
vectorPowerComplete Vec.[] coordinates[] = Any.here refl
vectorPowerComplete (head Vec.∷ tail)
    (coordinates∷ headMember tailMembers) =
  concatMapMember
    (λ coordinate → map (Vec._∷_ coordinate) (vectorPower _ _))
    headMember
    (mapMember (Vec._∷_ head)
      (vectorPowerComplete tail tailMembers))

------------------------------------------------------------------------
-- In particular every vector of Fin bound coordinates is enumerated.

allFinVectorPower :
  (bound dimension : Nat) → List (Vec.Vec (Fin bound) dimension)
allFinVectorPower bound dimension = vectorPower (allFin bound) dimension

allFinVectorPowerComplete :
  ∀ {bound dimension : Nat}
    (vector : Vec.Vec (Fin bound) dimension) →
  vector ∈ allFinVectorPower bound dimension
allFinVectorPowerComplete Vec.[] = Any.here refl
allFinVectorPowerComplete (head Vec.∷ tail) =
  concatMapMember
    (λ coordinate → map (Vec._∷_ coordinate) (vectorPower (allFin _) _))
    (allFinComplete head)
    (mapMember (Vec._∷_ head)
      (allFinVectorPowerComplete tail))

------------------------------------------------------------------------
-- No analysis enters this owner.  It is a reusable finite-product theorem.
------------------------------------------------------------------------
