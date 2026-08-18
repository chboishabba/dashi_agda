module DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Theorem 1.2 states, for every prime p > 3,
--
--   v_p(|M|) = 3 m_p / 2   if |S_p^1| = 1 and |S_p^2| = 0,
--              m_p / 2     if |S_p^1| > 1 and |S_p^2| = 0,
--              0           if |S_p^2| > 0,
--
-- where S_p^1 is the F_p-rational supersingular locus, S_p^2 the
-- non-rational F_{p^2}-locus, and m_p the minimum supersingular automorphism
-- order.  The paper also records m_p = 2 whenever S_p^2 is nonempty.
--
-- DASHI CONTRIBUTION
--
-- Lower the theorem from a support-only Boolean authority to its FULL exponent
-- depth on LITERALLY THE SAME coarse Frobenius carrier already consumed by the
-- Deligne--Rapoport/Fricke selector.  No second supersingular geometry object
-- exists in this interface.
--
-- We use the denominator-free doubled form
--
--   2 v_p(|M|) = 3 m_p,  m_p,  or 0,
--
-- so no division/parity side-condition is hidden in the formal carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _*_; suc; s≤s; z≤n)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

------------------------------------------------------------------------
-- The exact shared supersingular/Frobenius carrier at the requested prime.
------------------------------------------------------------------------

sharedGeometry :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  DR.PrimeLevelSupersingularFrobeniusData
sharedGeometry p prime ge5 =
  Selector.supersingularFrobenius (Fricke.publishedAuthorityAt p prime ge5)

------------------------------------------------------------------------
-- Source-shaped denominator-free cases of Duncan--Swisher Theorem 1.2.
------------------------------------------------------------------------

data DuncanSwisherExponentCase
    (fixed paired valuation minimumAut : Nat) : Set where

  singletonRational :
    fixed ≡ 1 →
    paired ≡ 0 →
    2 * valuation ≡ 3 * minimumAut →
    DuncanSwisherExponentCase fixed paired valuation minimumAut

  multipleRational :
    2 ≤ fixed →
    paired ≡ 0 →
    2 * valuation ≡ minimumAut →
    DuncanSwisherExponentCase fixed paired valuation minimumAut

  quadraticPresent :
    1 ≤ paired →
    valuation ≡ 0 →
    minimumAut ≡ 2 →
    DuncanSwisherExponentCase fixed paired valuation minimumAut

record DuncanSwisherExponentAuthority
    (p : Nat) (prime : Prime p) (ge5 : 5 ≤ p) : Set where
  field
    monsterValuation : Nat
    minimumAutomorphismOrder : Nat
    minimumAutomorphismPositive : 1 ≤ minimumAutomorphismOrder

    theorem12 : DuncanSwisherExponentCase
      (DR.fixedCount (sharedGeometry p prime ge5))
      (DR.pairedCount (sharedGeometry p prime ge5))
      monsterValuation
      minimumAutomorphismOrder

open DuncanSwisherExponentAuthority public

postulate
  publishedDuncanSwisherExponentAuthority :
    (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
    DuncanSwisherExponentAuthority p prime ge5

------------------------------------------------------------------------
-- The exact branch is a stronger observable than support alone.
------------------------------------------------------------------------

record ExponentDepthSummary : Set where
  constructor exponent-depth-summary
  field
    rationalSupersingularCount : Nat
    frobeniusPairCount : Nat
    minimumAutOrder : Nat
    valuation : Nat

open ExponentDepthSummary public

summary :
  {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  DuncanSwisherExponentAuthority p prime ge5 → ExponentDepthSummary
summary {p} {prime} {ge5} A = exponent-depth-summary
  (DR.fixedCount (sharedGeometry p prime ge5))
  (DR.pairedCount (sharedGeometry p prime ge5))
  (minimumAutomorphismOrder A)
  (monsterValuation A)

------------------------------------------------------------------------
-- Tiny structural positivity helpers.
------------------------------------------------------------------------

positiveNotZero :
  {n : Nat} → 1 ≤ n → n ≡ 0 → ⊥
positiveNotZero {0} () refl
positiveNotZero {suc n} positive ()

threeTimesPositive :
  {m : Nat} → 1 ≤ m → 1 ≤ 3 * m
threeTimesPositive {0} ()
threeTimesPositive {suc m} positive = s≤s z≤n

------------------------------------------------------------------------
-- Positive minimum automorphism order makes the two zero-pair branches have
-- positive valuation.  No Monster-prime enumeration occurs here.
------------------------------------------------------------------------

zeroPairBranchValuationCannotBeZero :
  {fixed paired valuation m : Nat} →
  1 ≤ m →
  DuncanSwisherExponentCase fixed paired valuation m →
  paired ≡ 0 →
  valuation ≡ 0 →
  ⊥
zeroPairBranchValuationCannotBeZero mPositive
  (singletonRational fixedOne pairedZero doubled) _ valuationZero
  rewrite valuationZero =
  positiveNotZero
    (threeTimesPositive mPositive)
    (sym doubled)
zeroPairBranchValuationCannotBeZero mPositive
  (multipleRational fixedMany pairedZero doubled) _ valuationZero
  rewrite valuationZero =
  positiveNotZero mPositive (sym doubled)
zeroPairBranchValuationCannotBeZero mPositive
  (quadraticPresent pairedPositive valuationZero minTwo)
  pairedZero _ =
  positiveNotZero pairedPositive pairedZero

pairPresentForcesZeroValuation :
  {fixed paired valuation m : Nat} →
  DuncanSwisherExponentCase fixed paired valuation m →
  1 ≤ paired →
  valuation ≡ 0
pairPresentForcesZeroValuation
  (singletonRational fixedOne pairedZero doubled) pairedPositive =
  ⊥-elim (positiveNotZero pairedPositive pairedZero)
pairPresentForcesZeroValuation
  (multipleRational fixedMany pairedZero doubled) pairedPositive =
  ⊥-elim (positiveNotZero pairedPositive pairedZero)
pairPresentForcesZeroValuation
  (quadraticPresent pairedPositive valuationZero minTwo) _ = valuationZero

zeroValuationForcesPairPresent :
  {fixed paired valuation m : Nat} →
  1 ≤ m →
  DuncanSwisherExponentCase fixed paired valuation m →
  valuation ≡ 0 →
  1 ≤ paired
zeroValuationForcesPairPresent mPositive
  case@(singletonRational fixedOne pairedZero doubled) valuationZero =
  ⊥-elim
    (zeroPairBranchValuationCannotBeZero
      mPositive case pairedZero valuationZero)
zeroValuationForcesPairPresent mPositive
  case@(multipleRational fixedMany pairedZero doubled) valuationZero =
  ⊥-elim
    (zeroPairBranchValuationCannotBeZero
      mPositive case pairedZero valuationZero)
zeroValuationForcesPairPresent mPositive
  (quadraticPresent pairedPositive valuationZero minTwo) _ = pairedPositive

------------------------------------------------------------------------
-- Zero valuation iff the exact shared Frobenius carrier has a nontrivial pair.
------------------------------------------------------------------------

valuationZeroIffPairPositive :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let A = publishedDuncanSwisherExponentAuthority p prime ge5
  in
  monsterValuation A ≡ 0
  ↔ 1 ≤ DR.pairedCount (sharedGeometry p prime ge5)
valuationZeroIffPairPositive p prime ge5 =
  let A = publishedDuncanSwisherExponentAuthority p prime ge5
  in
  (zeroValuationForcesPairPresent
      (minimumAutomorphismPositive A)
      (theorem12 A))
  ,
  (pairPresentForcesZeroValuation (theorem12 A))

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record DuncanSwisherExponentFormulaBoundary : Set where
  field
    theorem12FullDepthImported : Bool
    doubledFormulaAvoidsDivision : Bool
    exactFrickeFrobeniusCarrierReused : Bool
    duplicateSupersingularGeometryAuthorityIntroduced : Bool
    singletonVsMultipleRationalBranchesRetained : Bool
    supportRecoveredAsCorollary : Bool
    MonsterPrimeLaneEnumerationImported : Bool
    finiteMonsterExponentTableUsedAsProof : Bool
    frickeGenusUsedInsideExponentAuthority : Bool

canonicalDuncanSwisherExponentFormulaBoundary :
  DuncanSwisherExponentFormulaBoundary
canonicalDuncanSwisherExponentFormulaBoundary = record
  { theorem12FullDepthImported = true
  ; doubledFormulaAvoidsDivision = true
  ; exactFrickeFrobeniusCarrierReused = true
  ; duplicateSupersingularGeometryAuthorityIntroduced = false
  ; singletonVsMultipleRationalBranchesRetained = true
  ; supportRecoveredAsCorollary = true
  ; MonsterPrimeLaneEnumerationImported = false
  ; finiteMonsterExponentTableUsedAsProof = false
  ; frickeGenusUsedInsideExponentAuthority = false
  }
