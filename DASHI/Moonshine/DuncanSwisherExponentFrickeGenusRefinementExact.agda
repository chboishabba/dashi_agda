module DASHI.Moonshine.DuncanSwisherExponentFrickeGenusRefinementExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Pierre Deligne and Michael Rapoport,
-- "Les schemas de modules de courbes elliptiques",
-- Lecture Notes in Mathematics 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- DASHI CONTRIBUTION
--
-- Compose the FULL Duncan--Swisher exponent-depth theorem with the independent
-- Deligne--Rapoport/Fricke geometry on exactly the same Frobenius carrier.
--
-- The prime-set statement only sees
--
--   v_p(|M|) > 0  <=>  g(X_0^+(p)) = 0.
--
-- The stronger theorem proved here keeps the DEPTH on that genus-zero locus:
--
--   2 v_p(|M|) = 3 m_p  when the rational supersingular locus is a singleton,
--   2 v_p(|M|) =   m_p  when it has at least two points.
--
-- Thus the Monster exponent refines the Ogg/Fricke support coincidence by the
-- geometry of the rational supersingular locus and its minimum automorphism
-- order.  No MonsterPrimeLane enumeration or exponent lookup table is used.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _*_; suc)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as DS
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

------------------------------------------------------------------------
-- Positive genus is exactly the zero-valuation branch.
------------------------------------------------------------------------

valuationZeroIffFrickeGenusPositive :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let A = DS.publishedDuncanSwisherExponentAuthority p prime ge5
  in
  DS.monsterValuation A ≡ 0
  ↔ 1 ≤ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5)
valuationZeroIffFrickeGenusPositive p prime ge5 =
  let
    A = DS.publishedDuncanSwisherExponentAuthority p prime ge5
    genusPair = Fricke.publishedPairDefectEqualsFrickeGenus p prime ge5
    support = DS.valuationZeroIffPairPositive p prime ge5
  in
  (λ valuationZero →
      subst (λ n → 1 ≤ n) (sym genusPair)
        (proj₁ support valuationZero))
  ,
  (λ genusPositive →
      proj₂ support
        (subst (λ n → 1 ≤ n) genusPair genusPositive))

------------------------------------------------------------------------
-- On genus zero the quadratic branch is impossible, so Theorem 1.2 retains
-- exactly two depth mechanisms.
------------------------------------------------------------------------

data GenusZeroExponentDepth
    (fixed valuation minimumAut : Nat) : Set where

  singletonDepth :
    fixed ≡ 1 →
    2 * valuation ≡ 3 * minimumAut →
    GenusZeroExponentDepth fixed valuation minimumAut

  multipleDepth :
    2 ≤ fixed →
    2 * valuation ≡ minimumAut →
    GenusZeroExponentDepth fixed valuation minimumAut

------------------------------------------------------------------------
-- Genus zero means the SAME geometric pair count is zero.
------------------------------------------------------------------------

genusZeroForcesPairZero :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0 →
  DR.pairedCount (DS.sharedGeometry p prime ge5) ≡ 0
genusZeroForcesPairZero p prime ge5 genusZero =
  trans
    (sym (Fricke.publishedPairDefectEqualsFrickeGenus p prime ge5))
    genusZero

------------------------------------------------------------------------
-- Exact depth classification on the genus-zero locus.
------------------------------------------------------------------------

genusZeroExponentDepth :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0 →
  let A = DS.publishedDuncanSwisherExponentAuthority p prime ge5
  in
  GenusZeroExponentDepth
    (DR.fixedCount (DS.sharedGeometry p prime ge5))
    (DS.monsterValuation A)
    (DS.minimumAutomorphismOrder A)
genusZeroExponentDepth p prime ge5 genusZero
  with DS.theorem12 (DS.publishedDuncanSwisherExponentAuthority p prime ge5)
... | DS.singletonRational fixedOne pairedZero doubled =
  singletonDepth fixedOne doubled
... | DS.multipleRational fixedMany pairedZero doubled =
  multipleDepth fixedMany doubled
... | DS.quadraticPresent pairedPositive valuationZero minTwo =
  ⊥-elim
    (DS.positiveNotZero pairedPositive
      (genusZeroForcesPairZero p prime ge5 genusZero))

------------------------------------------------------------------------
-- Conversely, positive genus forces the exact third branch, including m_p=2.
------------------------------------------------------------------------

record PositiveGenusExponentCollapse
    (paired valuation minimumAut : Nat) : Set where
  constructor positive-genus-exponent-collapse
  field
    pairPositive : 1 ≤ paired
    valuationZero : valuation ≡ 0
    minimumAutIsTwo : minimumAut ≡ 2

open PositiveGenusExponentCollapse public

positiveGenusExponentCollapse :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  1 ≤ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) →
  let A = DS.publishedDuncanSwisherExponentAuthority p prime ge5
  in
  PositiveGenusExponentCollapse
    (DR.pairedCount (DS.sharedGeometry p prime ge5))
    (DS.monsterValuation A)
    (DS.minimumAutomorphismOrder A)
positiveGenusExponentCollapse p prime ge5 genusPositive
  with DS.theorem12 (DS.publishedDuncanSwisherExponentAuthority p prime ge5)
... | DS.singletonRational fixedOne pairedZero doubled =
  ⊥-elim
    (DS.positiveNotZero
      (subst (λ n → 1 ≤ n)
        (Fricke.publishedPairDefectEqualsFrickeGenus p prime ge5)
        genusPositive)
      pairedZero)
... | DS.multipleRational fixedMany pairedZero doubled =
  ⊥-elim
    (DS.positiveNotZero
      (subst (λ n → 1 ≤ n)
        (Fricke.publishedPairDefectEqualsFrickeGenus p prime ge5)
        genusPositive)
      pairedZero)
... | DS.quadraticPresent pairedPositive valuationZero minTwo =
  positive-genus-exponent-collapse pairedPositive valuationZero minTwo

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record DuncanSwisherExponentFrickeGenusRefinementBoundary : Set where
  field
    fullExponentDepthConsumed : Bool
    exactSameFrobeniusCarrierUsed : Bool
    positiveGenusIffZeroValuationDerived : Bool
    genusZeroDepthSplitDerived : Bool
    positiveGenusMinimumAutTwoDerived : Bool
    MonsterPrimeLaneEnumerationUsed : Bool
    finiteExponentTableUsedAsProof : Bool
    supportOnlyIsStrictlyCoarserThanDepth : Bool

canonicalDuncanSwisherExponentFrickeGenusRefinementBoundary :
  DuncanSwisherExponentFrickeGenusRefinementBoundary
canonicalDuncanSwisherExponentFrickeGenusRefinementBoundary = record
  { fullExponentDepthConsumed = true
  ; exactSameFrobeniusCarrierUsed = true
  ; positiveGenusIffZeroValuationDerived = true
  ; genusZeroDepthSplitDerived = true
  ; positiveGenusMinimumAutTwoDerived = true
  ; MonsterPrimeLaneEnumerationUsed = false
  ; finiteExponentTableUsedAsProof = false
  ; supportOnlyIsStrictlyCoarserThanDepth = true
  }
