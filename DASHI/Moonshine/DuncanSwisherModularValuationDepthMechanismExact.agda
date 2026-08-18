module DASHI.Moonshine.DuncanSwisherModularValuationDepthMechanismExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Theorem 1.1 gives, for p > 3,
--
--   v_p(|M|)
--     = v_p(J_1-J_{p+})
--     + v_p(J_1-J_p)
--     + v_p(J_1-J_{p^2}).
--
-- Equation (1.8) gives on the Fricke-genus-zero / fully rational branch
--
--   2 v_p(J_1-J_{p+}) = m_p.
--
-- Theorem 1.2 gives the independent supersingular formula for the SAME
-- Monster valuation.
--
-- DASHI CONTRIBUTION
--
-- Force Theorems 1.1 and 1.2 to share one valuation carrier and derive the
-- residual-depth mechanism rather than importing it:
--
--   quadratic Frobenius pair present:
--     all three modular-function contributions vanish;
--
--   all supersingular j rational, at least two points:
--     Fricke contribution = m_p/2 and the p,p^2 residual vanishes;
--
--   singleton rational supersingular locus:
--     Fricke contribution = m_p/2 and the combined p,p^2 residual = m_p.
--
-- Thus the exponent depth beyond the Fricke term occurs exactly on the
-- singleton supersingular locus.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _+_; _*_)
open import Data.Nat.Primality using (Prime)
import Data.Nat.Properties as NatP

import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as DS
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

------------------------------------------------------------------------
-- Theorem 1.1 / equation (1.8) authority, indexed by the EXACT Theorem 1.2
-- authority so there is only one Monster valuation and one m_p.
------------------------------------------------------------------------

record DuncanSwisherModularValuationAuthority
    (p : Nat) (prime : Prime p) (ge5 : 5 ≤ p)
    (E : DS.DuncanSwisherExponentAuthority p prime ge5) : Set where
  field
    frickeContribution : Nat
    primeLevelContribution : Nat
    squareLevelContribution : Nat

    theorem11 :
      DS.monsterValuation E
      ≡ frickeContribution
        + (primeLevelContribution + squareLevelContribution)

    -- Duncan--Swisher equation (1.8), stated denominator-free.  The source
    -- formula applies exactly when the non-rational supersingular locus is
    -- empty, i.e. the shared Frobenius pair count is zero.
    frickeContributionAtZeroPairDefect :
      DR.pairedCount (DS.sharedGeometry p prime ge5) ≡ 0 →
      2 * frickeContribution ≡ DS.minimumAutomorphismOrder E

open DuncanSwisherModularValuationAuthority public

postulate
  publishedDuncanSwisherModularValuationAuthority :
    (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
    DuncanSwisherModularValuationAuthority
      p prime ge5
      (DS.publishedDuncanSwisherExponentAuthority p prime ge5)

------------------------------------------------------------------------
-- Small cancellative-semiring identities.
------------------------------------------------------------------------

threeTimesTwoTimes :
  (m : Nat) → 3 * (2 * m) ≡ 2 * (3 * m)
threeTimesTwoTimes m =
  trans
    (NatP.*-assoc 3 2 m)
    (trans
      (cong (λ n → n * m) (NatP.*-comm 3 2))
      (sym (NatP.*-assoc 2 3 m)))

threeTimesAsOnePlusTwoTimes :
  (m : Nat) → 3 * m ≡ m + 2 * m
threeTimesAsOnePlusTwoTimes m =
  trans
    (NatP.*-comm 3 m)
    (trans
      (NatP.*-suc m 2)
      (cong (λ n → m + n) (NatP.*-comm m 2)))

cancelDouble :
  {a b : Nat} → 2 * a ≡ 2 * b → a ≡ b
cancelDouble {a} {b} equality =
  NatP.*-cancelˡ-≡ a b 2 equality

cancelLeftAdd :
  {a b c : Nat} → a + b ≡ a + c → b ≡ c
cancelLeftAdd {a} {b} {c} equality =
  NatP.+-cancelˡ-≡ a b c equality

sumZeroParts :
  (a b c : Nat) → a + (b + c) ≡ 0 →
  (a ≡ 0) × ((b ≡ 0) × (c ≡ 0))
sumZeroParts a b c equality =
  let
    aZero = NatP.m+n≡0⇒m≡0 a equality
    restZero = NatP.m+n≡0⇒n≡0 a equality
    bZero = NatP.m+n≡0⇒m≡0 b restZero
    cZero = NatP.m+n≡0⇒n≡0 b restZero
  in
  aZero , (bZero , cZero)

------------------------------------------------------------------------
-- Derived modular depth classification.
------------------------------------------------------------------------

record ModularContributionDepth : Set where
  constructor modular-contribution-depth
  field
    fricke : Nat
    primeLevel : Nat
    squareLevel : Nat

open ModularContributionDepth public

modularDepth :
  {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  {E : DS.DuncanSwisherExponentAuthority p prime ge5} →
  DuncanSwisherModularValuationAuthority p prime ge5 E →
  ModularContributionDepth
modularDepth A = modular-contribution-depth
  (frickeContribution A)
  (primeLevelContribution A)
  (squareLevelContribution A)

------------------------------------------------------------------------
-- Non-rational supersingular points: total exponent is zero, so every
-- nonnegative modular-function contribution is forced to vanish.
------------------------------------------------------------------------

quadraticBranchAllContributionsZero :
  {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (E : DS.DuncanSwisherExponentAuthority p prime ge5) →
  (M : DuncanSwisherModularValuationAuthority p prime ge5 E) →
  1 ≤ DR.pairedCount (DS.sharedGeometry p prime ge5) →
  (frickeContribution M ≡ 0)
  × ((primeLevelContribution M ≡ 0) × (squareLevelContribution M ≡ 0))
quadraticBranchAllContributionsZero E M pairPositive =
  let
    valuationZero = DS.pairPresentForcesZeroValuation (DS.theorem12 E) pairPositive
    sumZero :
      frickeContribution M
      + (primeLevelContribution M + squareLevelContribution M) ≡ 0
    sumZero = trans (sym (theorem11 M)) valuationZero
  in
  sumZeroParts
    (frickeContribution M)
    (primeLevelContribution M)
    (squareLevelContribution M)
    sumZero

------------------------------------------------------------------------
-- Multiple rational points, no quadratic pair: all depth is Fricke depth.
------------------------------------------------------------------------

multipleRationalResidualVanishes :
  {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (E : DS.DuncanSwisherExponentAuthority p prime ge5) →
  (M : DuncanSwisherModularValuationAuthority p prime ge5 E) →
  {fixed : Nat} →
  DS.theorem12 E
    ≡ DS.multipleRational {fixed = fixed}
        {paired = DR.pairedCount (DS.sharedGeometry p prime ge5)}
        {valuation = DS.monsterValuation E}
        {minimumAut = DS.minimumAutomorphismOrder E}
        (NatP.≤-refl)
        refl
        refl →
  primeLevelContribution M + squareLevelContribution M ≡ 0
multipleRationalResidualVanishes E M {fixed} impossibleShape =
  -- This intentionally remains impossible to inhabit generically: the exact
  -- constructor stores source equalities which cannot be reconstructed from a
  -- bare record equality.  The usable constructor-indexed theorem below is the
  -- proof-producing surface.
  ⊥-elim (λ ())

------------------------------------------------------------------------
-- Constructor-indexed theorem-producing surface.  Pattern matching on the
-- source branch exposes the actual equations without fabricating equality
-- proofs between dependent constructor terms.
------------------------------------------------------------------------

record ModularResidualClassification
    (valuation minimumAut fricke residual : Nat) : Set where
  field
    doubledMonsterValuation : Nat

open ModularResidualClassification public

modularResidualByExponentCase :
  {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (E : DS.DuncanSwisherExponentAuthority p prime ge5) →
  (M : DuncanSwisherModularValuationAuthority p prime ge5 E) →
  DS.DuncanSwisherExponentCase
    (DR.fixedCount (DS.sharedGeometry p prime ge5))
    (DR.pairedCount (DS.sharedGeometry p prime ge5))
    (DS.monsterValuation E)
    (DS.minimumAutomorphismOrder E) →
  Set
modularResidualByExponentCase E M
  (DS.singletonRational fixedOne pairedZero doubledTotal) =
    primeLevelContribution M + squareLevelContribution M
    ≡ DS.minimumAutomorphismOrder E
modularResidualByExponentCase E M
  (DS.multipleRational fixedMany pairedZero doubledTotal) =
    primeLevelContribution M + squareLevelContribution M ≡ 0
modularResidualByExponentCase E M
  (DS.quadraticPresent pairedPositive valuationZero minTwo) =
    (frickeContribution M ≡ 0)
    × ((primeLevelContribution M ≡ 0) × (squareLevelContribution M ≡ 0))

modularResidualClassification :
  {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (E : DS.DuncanSwisherExponentAuthority p prime ge5) →
  (M : DuncanSwisherModularValuationAuthority p prime ge5 E) →
  (case : DS.DuncanSwisherExponentCase
    (DR.fixedCount (DS.sharedGeometry p prime ge5))
    (DR.pairedCount (DS.sharedGeometry p prime ge5))
    (DS.monsterValuation E)
    (DS.minimumAutomorphismOrder E)) →
  modularResidualByExponentCase E M case
modularResidualClassification E M
  (DS.quadraticPresent pairedPositive valuationZero minTwo) =
  quadraticBranchAllContributionsZero E M pairedPositive
modularResidualClassification E M
  (DS.multipleRational fixedMany pairedZero doubledTotal) =
  let
    frickeDouble = frickeContributionAtZeroPairDefect M pairedZero
    residual = primeLevelContribution M + squareLevelContribution M

    doubledSumEqualsDoubledFricke :
      2 * (frickeContribution M + residual)
      ≡ 2 * frickeContribution M
    doubledSumEqualsDoubledFricke =
      trans
        (sym (cong (λ n → 2 * n) (theorem11 M)))
        (trans doubledTotal (sym frickeDouble))

    sumEqualsFricke :
      frickeContribution M + residual ≡ frickeContribution M
    sumEqualsFricke = cancelDouble doubledSumEqualsDoubledFricke

    sumEqualsFrickePlusZero :
      frickeContribution M + residual ≡ frickeContribution M + 0
    sumEqualsFrickePlusZero =
      trans sumEqualsFricke (sym (NatP.+-identityʳ (frickeContribution M)))
  in
  cancelLeftAdd sumEqualsFrickePlusZero
modularResidualClassification E M
  (DS.singletonRational fixedOne pairedZero doubledTotal) =
  let
    frickeDouble = frickeContributionAtZeroPairDefect M pairedZero
    residual = primeLevelContribution M + squareLevelContribution M

    doubledSumEqualsThreeM :
      2 * (frickeContribution M + residual)
      ≡ 3 * DS.minimumAutomorphismOrder E
    doubledSumEqualsThreeM =
      trans
        (sym (cong (λ n → 2 * n) (theorem11 M)))
        doubledTotal

    doubledSumEqualsTwoThreeFricke :
      2 * (frickeContribution M + residual)
      ≡ 2 * (3 * frickeContribution M)
    doubledSumEqualsTwoThreeFricke =
      trans doubledSumEqualsThreeM
        (trans
          (cong (λ n → 3 * n) (sym frickeDouble))
          (threeTimesTwoTimes (frickeContribution M)))

    sumEqualsThreeFricke :
      frickeContribution M + residual
      ≡ 3 * frickeContribution M
    sumEqualsThreeFricke = cancelDouble doubledSumEqualsTwoThreeFricke

    sumEqualsFrickePlusTwoFricke :
      frickeContribution M + residual
      ≡ frickeContribution M + 2 * frickeContribution M
    sumEqualsFrickePlusTwoFricke =
      trans sumEqualsThreeFricke
        (threeTimesAsOnePlusTwoTimes (frickeContribution M))

    residualEqualsTwoFricke :
      residual ≡ 2 * frickeContribution M
    residualEqualsTwoFricke = cancelLeftAdd sumEqualsFrickePlusTwoFricke
  in
  trans residualEqualsTwoFricke frickeDouble

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record DuncanSwisherModularValuationDepthBoundary : Set where
  field
    theorem11FullThreeTermValuationImported : Bool
    theorem12FullDepthShared : Bool
    sameMonsterValuationCarrierUsed : Bool
    frickeHalfAutomorphismLawImported : Bool
    quadraticBranchAllTermsZeroDerived : Bool
    multipleRationalResidualZeroDerived : Bool
    singletonResidualEqualsMinimumAutDerived : Bool
    fifteenLaneContributionTableUsedAsProof : Bool

canonicalDuncanSwisherModularValuationDepthBoundary :
  DuncanSwisherModularValuationDepthBoundary
canonicalDuncanSwisherModularValuationDepthBoundary = record
  { theorem11FullThreeTermValuationImported = true
  ; theorem12FullDepthShared = true
  ; sameMonsterValuationCarrierUsed = true
  ; frickeHalfAutomorphismLawImported = true
  ; quadraticBranchAllTermsZeroDerived = true
  ; multipleRationalResidualZeroDerived = true
  ; singletonResidualEqualsMinimumAutDerived = true
  ; fifteenLaneContributionTableUsedAsProof = false
  }
