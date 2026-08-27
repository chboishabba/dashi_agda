module DASHI.Mathematics.NumberTheory.PartitionErdosIdentityPrefixExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- Erdos starts from the classical identity
--
--   n p(n) = sum_{v >= 1} sum_{k >= 1} v p(n - k v),
--
-- with p(0)=1 and p(negative)=0.  Hardy and Ramanujan had already noted this
-- identity as an elementary route to log p(n) ~ pi sqrt(2n/3).
--
-- DASHI CONTRIBUTION
--
-- The repo already owns p(0)..p(5) = 1,1,2,3,5,7 through independently
-- constructed partition-labelled Fock bases.  This module checks the Erdos
-- identity exactly on that entire available prefix.
--
-- The arbitrary-n boundary is no longer an opaque theorem field: the generic
-- finite identity is derived in PartitionErdosFiniteDoubleCountBridgeExact
-- from an explicit deletion-fibre system.  Identifying its residual fold with
-- the conventional written double sum is tracked separately.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)

import DASHI.Moonshine.RankOneFockPartitionGradingExact as Fock
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteDoubleCountBridgeExact as DoubleCount

------------------------------------------------------------------------
-- Exact partition values already certified by the Fock owner.

p0 p1 p2 p3 p4 p5 : Nat
p0 = Fock.listLength Fock.gradeZeroBasis
p1 = Fock.listLength Fock.gradeOneBasis
p2 = Fock.listLength Fock.gradeTwoBasis
p3 = Fock.listLength Fock.gradeThreeBasis
p4 = Fock.listLength Fock.gradeFourBasis
p5 = Fock.listLength Fock.gradeFiveBasis

p0Is1 : p0 ≡ 1
p0Is1 = Fock.gradeZeroDimension

p1Is1 : p1 ≡ 1
p1Is1 = Fock.gradeOneDimension

p2Is2 : p2 ≡ 2
p2Is2 = Fock.gradeTwoDimension

p3Is3 : p3 ≡ 3
p3Is3 = Fock.gradeThreeDimension

p4Is5 : p4 ≡ 5
p4Is5 = Fock.gradeFourDimension

p5Is7 : p5 ≡ 7
p5Is7 = Fock.gradeFiveDimension

------------------------------------------------------------------------
-- Finite expansions of the Erdos double sum for n = 1,...,5.
-- Terms with n-kv < 0 are absent.

erdosRhs1 : Nat
erdosRhs1 = p0

erdosRhs2 : Nat
erdosRhs2 = (p1 + p0) + (2 * p0)

erdosRhs3 : Nat
erdosRhs3 = (p2 + p1 + p0) + (2 * p1) + (3 * p0)

erdosRhs4 : Nat
erdosRhs4 =
  (p3 + p2 + p1 + p0)
  + (2 * (p2 + p0))
  + (3 * p1)
  + (4 * p0)

erdosRhs5 : Nat
erdosRhs5 =
  (p4 + p3 + p2 + p1 + p0)
  + (2 * (p3 + p1))
  + (3 * p2)
  + (4 * p1)
  + (5 * p0)

------------------------------------------------------------------------
-- Machine-checked prefix instances of n p(n) = RHS.

erdosIdentityAt1 : 1 * p1 ≡ erdosRhs1
erdosIdentityAt1 = refl

erdosIdentityAt2 : 2 * p2 ≡ erdosRhs2
erdosIdentityAt2 = refl

erdosIdentityAt3 : 3 * p3 ≡ erdosRhs3
erdosIdentityAt3 = refl

erdosIdentityAt4 : 4 * p4 ≡ erdosRhs4
erdosIdentityAt4 = refl

erdosIdentityAt5 : 5 * p5 ≡ erdosRhs5
erdosIdentityAt5 = refl

record ErdosIdentityPrefixCertificate : Set where
  field
    n1 : 1 * p1 ≡ erdosRhs1
    n2 : 2 * p2 ≡ erdosRhs2
    n3 : 3 * p3 ≡ erdosRhs3
    n4 : 4 * p4 ≡ erdosRhs4
    n5 : 5 * p5 ≡ erdosRhs5

canonicalErdosIdentityPrefixCertificate : ErdosIdentityPrefixCertificate
canonicalErdosIdentityPrefixCertificate = record
  { n1 = erdosIdentityAt1
  ; n2 = erdosIdentityAt2
  ; n3 = erdosIdentityAt3
  ; n4 = erdosIdentityAt4
  ; n5 = erdosIdentityAt5
  }

------------------------------------------------------------------------
-- Generic completion now demands the concrete finite combinatorics rather
-- than the conclusion itself.

record ErdosPartitionIdentityCompletion : Set₁ where
  field
    deletionFibreSystem : DoubleCount.ErdosDeletionFibreSystem
    partitionZero :
      DoubleCount.PartitionCount deletionFibreSystem zero ≡ 1

open ErdosPartitionIdentityCompletion public

arbitraryNResidualIdentity :
  (completion : ErdosPartitionIdentityCompletion) →
  (n : Nat) →
  n * DoubleCount.PartitionCount (deletionFibreSystem completion) n
  ≡ DoubleCount.ErdosResidualDoubleSum (deletionFibreSystem completion) n
arbitraryNResidualIdentity completion =
  DoubleCount.erdosIdentityFromDeletionFibre
    (deletionFibreSystem completion)
