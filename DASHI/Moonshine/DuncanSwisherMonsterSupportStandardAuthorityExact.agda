module DASHI.Moonshine.DuncanSwisherMonsterSupportStandardAuthorityExact where

------------------------------------------------------------------------
-- STANDARD 2026 MONSTER-EXPONENT / SUPERSINGULAR SUPPORT AUTHORITY
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Theorem 1.2 proves, for every prime p > 3, an exact formula for
-- v_p(|M|) in terms of the rational/non-rational supersingular j-locus and the
-- minimum supersingular automorphism order m_p.  In particular its support
-- consequence is
--
--   v_p(|M|) > 0  <=>  S_p^2 is empty,
--
-- where S_p^2 is the set of supersingular j-invariants in F_{p^2}\F_p.
--
-- DASHI CONTRIBUTION
--
-- The repository already has the ACTUAL coarse Frobenius normal form at the
-- same requested prime p.  If d_p is its paired-orbit count then the number of
-- non-rational supersingular j-points is exactly 2*d_p.  We therefore do not
-- introduce a second supersingular-count authority.
--
-- This module imports only the p-adic valuation/support consequence of Duncan--
-- Swisher Theorem 1.2 plus the standard valuation/divisibility semantics.  The
-- conversion
--
--   2*d_p = 0 <=> d_p = 0 <=> g(X_0^+(p)) = 0
--
-- is derived locally downstream.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _*_; suc)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

------------------------------------------------------------------------
-- Canonical count of non-rational supersingular geometric points from the same
-- coarse Frobenius normal form already consumed by the Fricke selector.
------------------------------------------------------------------------

quadraticSupersingularPointCount :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) → Nat
quadraticSupersingularPointCount p prime ge5 =
  2 * DR.pairedCount
        (Selector.supersingularFrobenius
          (Fricke.publishedAuthorityAt p prime ge5))

------------------------------------------------------------------------
-- Source-shaped valuation authority.  No MonsterPrimeLane index occurs here.
------------------------------------------------------------------------

record DuncanSwisherSupportAuthority
    (p : Nat) (prime : Prime p) (ge5 : 5 ≤ p) : Set where
  field
    monsterValuation : Nat

    -- Standard p-adic valuation support law for the actual Monster order.
    valuationPositiveIffPrimeDividesMonster :
      1 ≤ monsterValuation
      ↔ Monster.PrimeDividesMonsterOrder p

    -- Theorem 1.2 support consequence, expressed on the SAME geometric
    -- supersingular carrier used by the Fricke selector.
    theorem12Support :
      1 ≤ monsterValuation
      ↔ quadraticSupersingularPointCount p prime ge5 ≡ 0

open DuncanSwisherSupportAuthority public

postulate
  publishedDuncanSwisherSupportAuthority :
    (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
    DuncanSwisherSupportAuthority p prime ge5

------------------------------------------------------------------------
-- Locally derived support equivalence before any genus argument.
------------------------------------------------------------------------

monsterDividesIffNoQuadraticSupersingularPoints :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Monster.PrimeDividesMonsterOrder p
  ↔ quadraticSupersingularPointCount p prime ge5 ≡ 0
monsterDividesIffNoQuadraticSupersingularPoints p prime ge5 =
  let A = publishedDuncanSwisherSupportAuthority p prime ge5
  in
  (λ divides →
      proj₁ (theorem12Support A)
        (proj₂ (valuationPositiveIffPrimeDividesMonster A) divides))
  ,
  (λ noQuadratic →
      proj₁ (valuationPositiveIffPrimeDividesMonster A)
        (proj₂ (theorem12Support A) noQuadratic))

------------------------------------------------------------------------
-- Finite arithmetic: 2*d=0 iff d=0.
------------------------------------------------------------------------

twiceZeroFromZero : (d : Nat) → d ≡ 0 → 2 * d ≡ 0
twiceZeroFromZero .0 refl = refl

zeroFromTwiceZero : (d : Nat) → 2 * d ≡ 0 → d ≡ 0
zeroFromTwiceZero 0 equality = refl
zeroFromTwiceZero (suc d) ()

noQuadraticPointsIffNoFrobeniusPairs :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  quadraticSupersingularPointCount p prime ge5 ≡ 0
  ↔ DR.pairedCount
      (Selector.supersingularFrobenius
        (Fricke.publishedAuthorityAt p prime ge5)) ≡ 0
noQuadraticPointsIffNoFrobeniusPairs p prime ge5 =
  (λ twiceZero →
      zeroFromTwiceZero
        (DR.pairedCount
          (Selector.supersingularFrobenius
            (Fricke.publishedAuthorityAt p prime ge5)))
        twiceZero)
  ,
  (λ pairZero →
      twiceZeroFromZero
        (DR.pairedCount
          (Selector.supersingularFrobenius
            (Fricke.publishedAuthorityAt p prime ge5)))
        pairZero)

record DuncanSwisherMonsterSupportBoundary : Set where
  field
    arbitraryPrimeAboveThreeAuthority : Bool
    MonsterPrimeLaneEnumerationImported : Bool
    sameFrobeniusCarrierAsFrickeSelectorUsed : Bool
    theorem12SupportImported : Bool
    valuationSupportImported : Bool
    twoTimesPairCountReductionDerived : Bool
    frickeGenusUsedInsideAuthority : Bool

canonicalDuncanSwisherMonsterSupportBoundary :
  DuncanSwisherMonsterSupportBoundary
canonicalDuncanSwisherMonsterSupportBoundary = record
  { arbitraryPrimeAboveThreeAuthority = true
  ; MonsterPrimeLaneEnumerationImported = false
  ; sameFrobeniusCarrierAsFrickeSelectorUsed = true
  ; theorem12SupportImported = true
  ; valuationSupportImported = true
  ; twoTimesPairCountReductionDerived = true
  ; frickeGenusUsedInsideAuthority = false
  }
