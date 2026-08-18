module DASHI.Moonshine.DuncanSwisherExponentDepthHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused highest-alpha root for the post-support Monster exponent problem.
--
-- SOURCE:
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- This root deliberately sits ABOVE the already-closed prime-support theorem.
-- It asks what the EXPONENT v_p(|M|) remembers once
--
--   p | |M| <=> g(X_0^+(p)) = 0
--
-- is already known.
--
-- The answer now formalized is:
--
--   positive Fricke genus
--     -> valuation 0 and m_p = 2;
--
--   genus zero, multiple rational supersingular points
--     -> 2 valuation = m_p and no non-Fricke modular residual;
--
--   genus zero, singleton supersingular locus
--     -> 2 valuation = 3 m_p and the p,p^2 modular residual = m_p.
--
-- Thus support is only the first coarse projection of a richer geometric /
-- modular-function depth invariant.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as Exponent
import DASHI.Moonshine.DuncanSwisherExponentFrickeGenusRefinementExact as Genus
import DASHI.Moonshine.DuncanSwisherModularValuationDepthMechanismExact as Modular
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

------------------------------------------------------------------------
-- Full depth authority is same-carrier with the Fricke selector.
------------------------------------------------------------------------

exactFrickeCarrierReusedRegression :
  Exponent.exactFrickeFrobeniusCarrierReused
    Exponent.canonicalDuncanSwisherExponentFormulaBoundary ≡ true
exactFrickeCarrierReusedRegression = refl

duplicateGeometryAuthorityAbsentRegression :
  Exponent.duplicateSupersingularGeometryAuthorityIntroduced
    Exponent.canonicalDuncanSwisherExponentFormulaBoundary ≡ false
duplicateGeometryAuthorityAbsentRegression = refl

------------------------------------------------------------------------
-- Support is recovered from depth, not used as its premise.
------------------------------------------------------------------------

valuationZeroIffPositiveGenusRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let E = Exponent.publishedDuncanSwisherExponentAuthority p prime ge5
  in
  Exponent.monsterValuation E ≡ 0
  ↔ 1 ≤ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5)
valuationZeroIffPositiveGenusRegression = Genus.valuationZeroIffFrickeGenusPositive

------------------------------------------------------------------------
-- The exact Theorem 1.2 branch induces the full modular residual
-- classification from Theorem 1.1 + equation (1.8).
------------------------------------------------------------------------

modularResidualDepthRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let
    E = Exponent.publishedDuncanSwisherExponentAuthority p prime ge5
    M = Modular.publishedDuncanSwisherModularValuationAuthority p prime ge5
  in
  Modular.modularResidualByExponentCase E M (Exponent.theorem12 E)
modularResidualDepthRegression p prime ge5 =
  let
    E = Exponent.publishedDuncanSwisherExponentAuthority p prime ge5
    M = Modular.publishedDuncanSwisherModularValuationAuthority p prime ge5
  in
  Modular.modularResidualClassification E M (Exponent.theorem12 E)

------------------------------------------------------------------------
-- Positive genus gives the complete zero-exponent collapse, including m_p=2.
------------------------------------------------------------------------

positiveGenusDepthCollapseRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  1 ≤ Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) →
  let E = Exponent.publishedDuncanSwisherExponentAuthority p prime ge5
  in
  Genus.PositiveGenusExponentCollapse
    (DR.pairedCount (Exponent.sharedGeometry p prime ge5))
    (Exponent.monsterValuation E)
    (Exponent.minimumAutomorphismOrder E)
positiveGenusDepthCollapseRegression = Genus.positiveGenusExponentCollapse

------------------------------------------------------------------------
-- Boundary: the next explanatory frontier is BELOW the valuation formulas:
-- construct the modular functions / U_p level-lowering mechanism themselves,
-- rather than importing Theorems 1.1/1.2 only as numerical valuation laws.
------------------------------------------------------------------------

record DuncanSwisherExponentDepthHighestAlphaBoundary : Set where
  field
    supportTheoremAlreadyClosed : Bool
    fullExponentDepthNowRetained : Bool
    modularThreeTermDepthNowRetained : Bool
    singletonExtraResidualDerived : Bool
    positiveGenusZeroExponentDerived : Bool
    finiteMonsterPrimeLaneUsed : Bool
    nextFrontierIsExplicitModularFunctionOperators : Bool

canonicalDuncanSwisherExponentDepthHighestAlphaBoundary :
  DuncanSwisherExponentDepthHighestAlphaBoundary
canonicalDuncanSwisherExponentDepthHighestAlphaBoundary = record
  { supportTheoremAlreadyClosed = true
  ; fullExponentDepthNowRetained = true
  ; modularThreeTermDepthNowRetained = true
  ; singletonExtraResidualDerived = true
  ; positiveGenusZeroExponentDerived = true
  ; finiteMonsterPrimeLaneUsed = false
  ; nextFrontierIsExplicitModularFunctionOperators = true
  }
