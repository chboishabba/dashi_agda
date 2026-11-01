module DASHI.Mathematics.NumberTheory.PartitionErdosFactorKeyPermutationExact where

------------------------------------------------------------------------
-- EXACT RESIDUAL-MAJOR <-> K-MAJOR FACTOR-KEY PERMUTATION
--
-- Both finite presentations are mapped into the common proof-free key
--
--   (r,k,v).
--
-- Mutual membership plus duplicate-freedom then promotes the change of
-- summation order to a literal stdlib permutation.  This is the finite
-- reindexing receipt needed before the inner v*q^v bound and outer Basel sum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as OneTo
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionErdosFactorCoordinateKeyExact as Key
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact as KMajor
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateUniqueExact as KMajorUnique
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorPositiveFactorBridgeExact as Bridge
import DASHI.Mathematics.NumberTheory.PartitionErdosResidualMajorFactorKeyExact as ResidualMajor

------------------------------------------------------------------------
-- K-major mapped key list and its inherited uniqueness.

kMajorFactorKeys : (n : Nat) → List Key.FactorCoordinateKey
kMajorFactorKeys n =
  map Key.kMajorFactorKey (KMajor.kMajorFactorCoordinates n)

kMajorFactorKeysUnique :
  (n : Nat) → Unique (kMajorFactorKeys n)
kMajorFactorKeysUnique n =
  UniqueP.map⁺
    Key.kMajorFactorKeyInjective
    (KMajorUnique.kMajorFactorCoordinatesUnique n)

------------------------------------------------------------------------
-- Equality of common keys for the coordinate/factor pair selected by the
-- forward bridge.

positiveKeyMatchesKMajor :
  ∀ {n : Nat}
    (coordinate : KMajor.KMajorFactorCoordinate n)
    {pair : Factor.PositiveFactorPair (KMajor.residual coordinate)} →
  Factor.divisor pair ≡ KMajor.divisor coordinate →
  Factor.predecessor pair ≡ KMajor.copiesPredecessor coordinate →
  Key.positiveFactorKey pair ≡ Key.kMajorFactorKey coordinate
positiveKeyMatchesKMajor coordinate divisorExact predecessorExact =
  Key.factorCoordinateKeyExtensional
    refl
    (trans
      (cong suc predecessorExact)
      (sym (KMajor.copiesIsSuccessor coordinate)))
    divisorExact

------------------------------------------------------------------------
-- Transport membership between equal positivity proofs for one residual.

transportBlockPositive :
  ∀ {r : Nat}
    {leftPositive rightPositive : suc zero ≤ r}
    {key : Key.FactorCoordinateKey} →
  key ∈ ResidualMajor.residualFactorKeyBlock r leftPositive →
  key ∈ ResidualMajor.residualFactorKeyBlock r rightPositive
transportBlockPositive {r} {leftPositive} {rightPositive} {key} member =
  subst
    (λ positive → key ∈ ResidualMajor.residualFactorKeyBlock r positive)
    (NatP.≤-irrelevant leftPositive rightPositive)
    member

------------------------------------------------------------------------
-- Forward membership: a k-major coordinate lies in the residual-major key
-- list because its residual r=k*v occurs in oneTo n and the factor scan is
-- coordinate-complete.

kMajorCoordinateKeyInResidualFrom :
  (n : Nat) →
  (residuals : List Nat) →
  (bounds : All.All (λ r → (suc zero ≤ r) × (r ≤ n)) residuals) →
  (coordinate : KMajor.KMajorFactorCoordinate n) →
  KMajor.residual coordinate ∈ residuals →
  Key.kMajorFactorKey coordinate
    ∈ ResidualMajor.residualMajorFactorKeysFrom n residuals bounds
kMajorCoordinateKeyInResidualFrom n [] All.[] coordinate ()
kMajorCoordinateKeyInResidualFrom
    n (r ∷ rs) (All._∷_ rBounds rest) coordinate (Any.here equality)
  with equality
... | refl
  with Bridge.kMajorCoordinateToPositiveFactorScan coordinate
...   | pair , pairMember , divisorExact , predecessorExact =
  Product.appendMemberLeft
    (subst
      (λ key → key ∈ ResidualMajor.residualFactorKeyBlock
        (KMajor.residual coordinate) (proj₁ rBounds))
      (positiveKeyMatchesKMajor coordinate divisorExact predecessorExact)
      (transportBlockPositive
        (Product.mapMember Key.positiveFactorKey pairMember)))
kMajorCoordinateKeyInResidualFrom
    n (r ∷ rs) (All._∷_ rBounds rest) coordinate (Any.there residualMember) =
  Product.appendMemberRight
    (ResidualMajor.residualFactorKeyBlock r (proj₁ rBounds))
    (kMajorCoordinateKeyInResidualFrom
      n rs rest coordinate residualMember)

kMajorToResidualMajor :
  ∀ {n : Nat} {key : Key.FactorCoordinateKey} →
  key ∈ kMajorFactorKeys n →
  key ∈ ResidualMajor.residualMajorFactorKeys n
kMajorToResidualMajor {n} {key} member
  with ∈-map⁻ member
... | coordinate , coordinateMember , equality =
  subst
    (λ target → target ∈ ResidualMajor.residualMajorFactorKeys n)
    equality
    (kMajorCoordinateKeyInResidualFrom
      n
      (Hecke.oneTo n)
      (OneTo.oneToAllBounds n)
      coordinate
      (OneTo.oneToComplete
        (KMajor.residualPositive coordinate)
        (KMajor.productBound coordinate)))

------------------------------------------------------------------------
-- Reverse membership: decode the residual-major block member to an actual
-- positive factor pair, reconstruct its k-major coordinate, and transport the
-- common proof-free key equality.

residualMajorToKMajorFrom :
  (n : Nat) →
  (residuals : List Nat) →
  (bounds : All.All (λ r → (suc zero ≤ r) × (r ≤ n)) residuals) →
  ∀ {key : Key.FactorCoordinateKey} →
  key ∈ ResidualMajor.residualMajorFactorKeysFrom n residuals bounds →
  key ∈ kMajorFactorKeys n
residualMajorToKMajorFrom n [] All.[] ()
residualMajorToKMajorFrom
    n (r ∷ rs) (All._∷_ rBounds rest) {key} member
  with ∈-++⁻
    (ResidualMajor.residualFactorKeyBlock r (proj₁ rBounds)) member
... | inj₂ tailMember =
  residualMajorToKMajorFrom n rs rest tailMember
... | inj₁ blockMember
  with ∈-map⁻ blockMember
...   | pair , pairMember , blockEquality
  with Bridge.positiveFactorToKMajorCoordinate (proj₂ rBounds) pair
...     | coordinate , coordinateMember , copiesExact , divisorExact , residualExact =
  subst
    (λ target → target ∈ kMajorFactorKeys n)
    (trans keyAgreement blockEquality)
    (Product.mapMember Key.kMajorFactorKey coordinateMember)
  where
  keyAgreement : Key.kMajorFactorKey coordinate ≡ Key.positiveFactorKey pair
  keyAgreement =
    Key.factorCoordinateKeyExtensional
      residualExact
      copiesExact
      divisorExact

residualMajorToKMajor :
  ∀ {n : Nat} {key : Key.FactorCoordinateKey} →
  key ∈ ResidualMajor.residualMajorFactorKeys n →
  key ∈ kMajorFactorKeys n
residualMajorToKMajor {n} =
  residualMajorToKMajorFrom
    n
    (Hecke.oneTo n)
    (OneTo.oneToAllBounds n)

------------------------------------------------------------------------
-- Exact finite change of summation order.

residualMajorKMajorFactorKeyPermutation :
  (n : Nat) →
  ResidualMajor.residualMajorFactorKeys n
  Perm.↭
  kMajorFactorKeys n
residualMajorKMajorFactorKeyPermutation n =
  Reindex.uniqueMembershipEquivalenceToPermutation
    (ResidualMajor.residualMajorFactorKeysUnique n)
    (kMajorFactorKeysUnique n)
    residualMajorToKMajor
    kMajorToResidualMajor

kMajorResidualMajorFactorKeyPermutation :
  (n : Nat) →
  kMajorFactorKeys n
  Perm.↭
  ResidualMajor.residualMajorFactorKeys n
kMajorResidualMajorFactorKeyPermutation n =
  Reindex.uniqueMembershipEquivalenceToPermutation
    (kMajorFactorKeysUnique n)
    (ResidualMajor.residualMajorFactorKeysUnique n)
    kMajorToResidualMajor
    residualMajorToKMajor

------------------------------------------------------------------------
-- No analysis is used here.  The classical r-major factor sum may now be
-- rearranged exactly into k-major order before applying the cubic degree-one
-- kernel and the Basel reciprocal-square bound.
------------------------------------------------------------------------
