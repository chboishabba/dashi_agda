module DASHI.Mathematics.NumberTheory.PartitionErdosResidualMajorFactorKeyExact where

------------------------------------------------------------------------
-- RESIDUAL-MAJOR PROOF-FREE FACTOR KEYS
--
-- Map the existing positive factor-pair scans for r=1,...,n into the common
-- proof-free key (r,k,v).  The order is residual-major, matching the classical
-- recurrence carrier.  Duplicate-freedom is inherited from the unique divisor
-- scan inside each r-block plus distinct residual coordinates across blocks.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Nat.Base using (_≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as OneTo
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosFactorCoordinateKeyExact as Key

residualFactorKeyBlock :
  (r : Nat) → suc zero ≤ r → List Key.FactorCoordinateKey
residualFactorKeyBlock r positive =
  map Key.positiveFactorKey (Factor.positiveFactorPairs r positive)

residualMajorFactorKeysFrom :
  (n : Nat) →
  (residuals : List Nat) →
  All.All (λ r → (suc zero ≤ r) × (r ≤ n)) residuals →
  List Key.FactorCoordinateKey
residualMajorFactorKeysFrom n [] All.[] = []
residualMajorFactorKeysFrom n (r ∷ rs) (All._∷_ rBounds rest) =
  residualFactorKeyBlock r (proj₁ rBounds)
  ++ residualMajorFactorKeysFrom n rs rest

residualMajorFactorKeys : (n : Nat) → List Key.FactorCoordinateKey
residualMajorFactorKeys n =
  residualMajorFactorKeysFrom
    n (Hecke.oneTo n) (OneTo.oneToAllBounds n)

------------------------------------------------------------------------
-- Every key in one r-block has residual coordinate exactly r.

residualFactorKeyBlockResidual :
  ∀ {r : Nat} (positive : suc zero ≤ r)
    {key : Key.FactorCoordinateKey} →
  key ∈ residualFactorKeyBlock r positive →
  Key.residual key ≡ r
residualFactorKeyBlockResidual positive member
  with ∈-map⁻ member
... | pair , pairMember , refl = refl

residualMajorFactorKeysFromResidualMember :
  (n : Nat) →
  (residuals : List Nat) →
  (bounds : All.All (λ r → (suc zero ≤ r) × (r ≤ n)) residuals) →
  ∀ {key : Key.FactorCoordinateKey} →
  key ∈ residualMajorFactorKeysFrom n residuals bounds →
  Key.residual key ∈ residuals
residualMajorFactorKeysFromResidualMember n [] All.[] ()
residualMajorFactorKeysFromResidualMember
    n (r ∷ rs) (All._∷_ rBounds rest) member
  with ∈-++⁻ (residualFactorKeyBlock r (proj₁ rBounds)) member
... | inj₁ blockMember =
  Any.here (residualFactorKeyBlockResidual (proj₁ rBounds) blockMember)
... | inj₂ tailMember =
  Any.there
    (residualMajorFactorKeysFromResidualMember n rs rest tailMember)

------------------------------------------------------------------------
-- Duplicate-freedom.

residualFactorKeyBlockUnique :
  (r : Nat) (positive : suc zero ≤ r) →
  Unique (residualFactorKeyBlock r positive)
residualFactorKeyBlockUnique r positive =
  UniqueP.map⁺
    Key.positiveFactorKeyInjective
    (Factor.positiveFactorPairsUnique r positive)

residualMajorFactorKeysFromUnique :
  (n : Nat) →
  (residuals : List Nat) →
  (bounds : All.All (λ r → (suc zero ≤ r) × (r ≤ n)) residuals) →
  Unique residuals →
  Unique (residualMajorFactorKeysFrom n residuals bounds)
residualMajorFactorKeysFromUnique n [] All.[] AllPairs.[] = AllPairs.[]
residualMajorFactorKeysFromUnique
    n (r ∷ rs) (All._∷_ rBounds rest)
    (AllPairs._∷_ fresh tailUnique) =
  Dep.uniqueAppendDisjoint
    (residualFactorKeyBlockUnique r (proj₁ rBounds))
    (residualMajorFactorKeysFromUnique n rs rest tailUnique)
    cross
  where
  cross :
    ∀ {left right} →
    left ∈ residualFactorKeyBlock r (proj₁ rBounds) →
    right ∈ residualMajorFactorKeysFrom n rs rest →
    left ≢ right
  cross leftMember rightMember equality =
    All.lookup fresh
      (residualMajorFactorKeysFromResidualMember n rs rest rightMember)
      rEqualsRightResidual
    where
    leftResidual : Key.residual left ≡ r
    leftResidual =
      residualFactorKeyBlockResidual (proj₁ rBounds) leftMember

    outputResidual : Key.residual left ≡ Key.residual right
    outputResidual = cong Key.residual equality

    rEqualsRightResidual : r ≡ Key.residual right
    rEqualsRightResidual = trans (sym leftResidual) outputResidual

residualMajorFactorKeysUnique :
  (n : Nat) → Unique (residualMajorFactorKeys n)
residualMajorFactorKeysUnique n =
  residualMajorFactorKeysFromUnique
    n
    (Hecke.oneTo n)
    (OneTo.oneToAllBounds n)
    (OneTo.oneToUnique n)

------------------------------------------------------------------------
-- This owner is finite/reindexing only.  It exposes the residual-major side in
-- the same proof-free key type used by the k-major scan.
------------------------------------------------------------------------
