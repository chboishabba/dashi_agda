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
-- depth, on the SAME coarse Frobenius normal form already consumed by the
-- Deligne--Rapoport/Fricke selector.
--
-- We use the denominator-free doubled form
--
--   2 v_p(|M|) = 3 m_p,  m_p,  or 0,
--
-- so no division/parity side-condition is hidden in the formal carrier.
-- The branch witness is proof-relevant: later consumers can distinguish the
-- singleton-rational and multiple-rational genus-zero mechanisms instead of
-- remembering only whether the exponent is nonzero.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _*_; suc)
open import Data.Nat.Primality using (Prime)
import Data.Nat.Properties as NatP

import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR
import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster

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
    geometry : DR.PrimeLevelSupersingularFrobeniusData
    geometryAtRequestedPrime : DR.prime geometry ≡ p

    monsterValuation : Nat
    minimumAutomorphismOrder : Nat
    minimumAutomorphismPositive : 1 ≤ minimumAutomorphismOrder

    theorem12 : DuncanSwisherExponentCase
      (DR.fixedCount geometry)
      (DR.pairedCount geometry)
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
summary A = exponent-depth-summary
  (DR.fixedCount (geometry A))
  (DR.pairedCount (geometry A))
  (minimumAutomorphismOrder A)
  (monsterValuation A)

------------------------------------------------------------------------
-- Positive minimum automorphism order makes the two zero-pair branches have
-- positive valuation.  We prove only what is needed by case analysis, avoiding
-- any Monster-prime enumeration.
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
  let
    threeMPositive : 1 ≤ 3 * _
    threeMPositive = NatP.m≤m*n 1 mPositive 3
  in
  NatP.1+n≰n 0
    (subst (λ n → 1 ≤ n) (sym doubled) threeMPositive)
zeroPairBranchValuationCannotBeZero mPositive
  (multipleRational fixedMany pairedZero doubled) _ valuationZero
  rewrite valuationZero =
  let
    impossible : 1 ≤ 0
    impossible = subst (λ n → 1 ≤ n) (sym doubled) mPositive
  in
  NatP.1+n≰n 0 impossible
zeroPairBranchValuationCannotBeZero mPositive
  (quadraticPresent pairedPositive valuationZero minTwo)
  pairedZero _ =
  let
    impossible : 1 ≤ 0
    impossible = subst (λ n → 1 ≤ n) pairedZero pairedPositive
  in
  NatP.1+n≰n 0 impossible

------------------------------------------------------------------------
-- Full theorem immediately recovers the older support statement, but now as a
-- corollary of exponent DEPTH rather than the imported endpoint.
------------------------------------------------------------------------

pairPresentForcesZeroValuation :
  {fixed paired valuation m : Nat} →
  DuncanSwisherExponentCase fixed paired valuation m →
  1 ≤ paired →
  valuation ≡ 0
pairPresentForcesZeroValuation
  (singletonRational fixedOne pairedZero doubled) pairedPositive =
  ⊥-elim
    (NatP.1+n≰n 0
      (subst (λ n → 1 ≤ n) pairedZero pairedPositive))
pairPresentForcesZeroValuation
  (multipleRational fixedMany pairedZero doubled) pairedPositive =
  ⊥-elim
    (NatP.1+n≰n 0
      (subst (λ n → 1 ≤ n) pairedZero pairedPositive))
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
-- A zero/nonzero pair-count formulation avoids choosing a decidable comparison
-- theorem here.  The exact branch object still retains the depth information.
------------------------------------------------------------------------

valuationZeroIffPairPositive :
  {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (A : DuncanSwisherExponentAuthority p prime ge5) →
  monsterValuation A ≡ 0
  ↔ 1 ≤ DR.pairedCount (geometry A)
valuationZeroIffPairPositive A =
  (zeroValuationForcesPairPresent
      (minimumAutomorphismPositive A)
      (theorem12 A))
  ,
  (pairPresentForcesZeroValuation (theorem12 A))

------------------------------------------------------------------------
-- Geometric refinement: positive Fricke pair defect is exactly the
-- zero-exponent branch on this source authority.  Genus transport itself stays
-- in the independent Deligne--Rapoport selector lane.
------------------------------------------------------------------------

record DuncanSwisherExponentFormulaBoundary : Set where
  field
    theorem12FullDepthImported : Bool
    doubledFormulaAvoidsDivision : Bool
    sameCoarseFrobeniusCarrierUsed : Bool
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
  ; sameCoarseFrobeniusCarrierUsed = true
  ; singletonVsMultipleRationalBranchesRetained = true
  ; supportRecoveredAsCorollary = true
  ; MonsterPrimeLaneEnumerationImported = false
  ; finiteMonsterExponentTableUsedAsProof = false
  ; frickeGenusUsedInsideExponentAuthority = false
  }
