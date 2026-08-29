module DASHI.Mathematics.NumberTheory.PartitionErdosFactorCoordinateKeyExact where

------------------------------------------------------------------------
-- COMMON PROOF-FREE FACTOR KEY
--
-- Both residual-major PositiveFactorPair data and the Basel-friendly k-major
-- carrier map to the same ordinary key
--
--   (residual r, copies k, divisor v).
--
-- Proof evidence for positivity/bounds/product equations is intentionally not
-- part of key identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualUniqueExact as ClassicalUnique
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact as KMajor

record FactorCoordinateKey : Set where
  constructor factorCoordinateKey
  field
    residual : Nat
    copies : Nat
    divisor : Nat

open FactorCoordinateKey public

kMajorFactorKey :
  ∀ {n} → KMajor.KMajorFactorCoordinate n → FactorCoordinateKey
kMajorFactorKey coordinate =
  factorCoordinateKey
    (KMajor.residual coordinate)
    (KMajor.copies coordinate)
    (KMajor.divisor coordinate)

positiveFactorKey :
  ∀ {r} → Factor.PositiveFactorPair r → FactorCoordinateKey
positiveFactorKey {r} pair =
  factorCoordinateKey
    r
    (suc (Factor.predecessor pair))
    (Factor.divisor pair)

------------------------------------------------------------------------
-- PositiveFactorPair injectivity after erasing proof fields follows from the
-- extensionality theorem already proved by the classical residual uniqueness
-- owner.

positiveFactorKeyInjective :
  ∀ {r : Nat} {left right : Factor.PositiveFactorPair r} →
  positiveFactorKey left ≡ positiveFactorKey right →
  left ≡ right
positiveFactorKeyInjective {left = left} {right = right} equality =
  ClassicalUnique.factorPairCoordinatesExtensional
    (cong divisor equality)
    (NatP.suc-injective (cong copies equality))

------------------------------------------------------------------------
-- K-major record extensionality is likewise determined entirely by the two
-- ordinary coordinates.  The remaining fields are Nat-order proofs and are
-- discharged by proof irrelevance already used elsewhere in this lane.

kMajorCoordinatesExtensional :
  ∀ {n : Nat}
    {left right : KMajor.KMajorFactorCoordinate n} →
  KMajor.copies left ≡ KMajor.copies right →
  KMajor.divisor left ≡ KMajor.divisor right →
  left ≡ right
kMajorCoordinatesExtensional
    {left = KMajor.kMajorFactorCoordinate
      k v kPositive kBound vPositive vBound productBound}
    {right = KMajor.kMajorFactorCoordinate
      k' v' kPositive' kBound' vPositive' vBound' productBound'}
    copiesExact divisorExact
  with copiesExact | divisorExact
... | refl | refl =
  cong₅
    (λ kp kb vp vb pb →
      KMajor.kMajorFactorCoordinate k v kp kb vp vb pb)
    (NatP.≤-irrelevant kPositive kPositive')
    (NatP.≤-irrelevant kBound kBound')
    (NatP.≤-irrelevant vPositive vPositive')
    (NatP.≤-irrelevant vBound vBound')
    (NatP.≤-irrelevant productBound productBound')
  where
  cong₅ :
    ∀ {A B C D E F : Set}
      (f : A → B → C → D → E → F)
      {a a' : A} {b b' : B} {c c' : C}
      {d d' : D} {e e' : E} →
    a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' →
    f a b c d e ≡ f a' b' c' d' e'
  cong₅ f refl refl refl refl refl = refl

kMajorFactorKeyInjective :
  ∀ {n : Nat}
    {left right : KMajor.KMajorFactorCoordinate n} →
  kMajorFactorKey left ≡ kMajorFactorKey right →
  left ≡ right
kMajorFactorKeyInjective equality =
  kMajorCoordinatesExtensional
    (cong copies equality)
    (cong divisor equality)

------------------------------------------------------------------------
-- The common key can therefore be used with stdlib Unique.map and the generic
-- unique-membership-to-permutation theorem without retaining proof witnesses.
------------------------------------------------------------------------
