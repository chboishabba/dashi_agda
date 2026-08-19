module DASHI.Moonshine.DuncanSwisherP11MonodromyExponentExact where

------------------------------------------------------------------------
-- TABLE-FREE p=11 MONSTER EXPONENT FROM THE OLD #567 STACK WEIGHT
--
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Theorem 1.2.
--
-- John Voight,
-- "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapters 41--42: supersingular / Brandt monodromy weights.
--
-- DASHI CONTRIBUTION
--
-- At p=11 the actual supersingular classes have Brandt monodromy weights
--
--   w(j=0)=3,  w(j=1728)=2.
--
-- Hence the minimum reduced/monodromy weight is 2 and the Duncan--Swisher full
-- automorphism minimum is
--
--   m_11 = 2 * min(w) = 4.
--
-- The p=11 Frobenius regime is the multiple-rational/no-quadratic branch, so
-- Theorem 1.2 gives division-free
--
--   2 * v_11(|M|) = m_11 = 2 * min(w).
--
-- Nat cancellation therefore derives
--
--   v_11(|M|) = min(w) = 2
--
-- WITHOUT reading the Monster exponent table.
--
-- By DuncanSwisherLegendreRamificationDepthExact the same minimum weight is the
-- minimum Deligne first-pole depth.  Reciprocal stack sheets are explicitly not
-- used in this exponent derivation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _*_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as DS
import DASHI.Moonshine.DuncanSwisherLegendreRamificationDepthExact as Ram
import DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact as Stack11
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo

------------------------------------------------------------------------
-- Exact minimum of the already-constructed p11 monodromy-weight carrier.
------------------------------------------------------------------------

p11MinimumMonodromyWeight : Nat
p11MinimumMonodromyWeight = 2

p11EveryMonodromyWeightAtLeastMinimum :
  (c : Geo.P11SupersingularJ) →
  p11MinimumMonodromyWeight ≤ Stack11.p11MonodromyWeight c
p11EveryMonodromyWeightAtLeastMinimum Geo.jZeroSS =
  s≤s (s≤s z≤n)
p11EveryMonodromyWeightAtLeastMinimum Geo.j1728SS =
  s≤s (s≤s z≤n)

p11MinimumMonodromyWeightAttained :
  Stack11.p11MonodromyWeight Geo.j1728SS ≡ p11MinimumMonodromyWeight
p11MinimumMonodromyWeightAttained = refl

p11FullAutMinimumFromMonodromy :
  2 * p11MinimumMonodromyWeight ≡ 4
p11FullAutMinimumFromMonodromy = refl

------------------------------------------------------------------------
-- Pure source-shaped theorem: the indexed p11 Theorem-1.2 case itself forces
-- valuation 2.  No MonsterPrimeLane / order table appears in this statement.
------------------------------------------------------------------------

p11ExponentCaseForcesValuationTwo :
  {valuation : Nat} →
  DS.DuncanSwisherExponentCase 2 0 valuation 4 →
  valuation ≡ 2
p11ExponentCaseForcesValuationTwo
  (DS.singletonRational () pairedZero doubled)
p11ExponentCaseForcesValuationTwo
  (DS.multipleRational fixedMany pairedZero doubled) =
  NatP.*-cancelˡ-≡ valuation 2 2 doubled
  where
    valuation : Nat
    valuation = _
p11ExponentCaseForcesValuationTwo
  (DS.quadraticPresent () valuationZero minTwo)

------------------------------------------------------------------------
-- A more compositional form: if the source case uses twice the actual minimum
-- monodromy weight as m_11, the exponent equals that minimum weight.
------------------------------------------------------------------------

p11ExponentCaseForcesMinimumMonodromyWeight :
  {valuation : Nat} →
  DS.DuncanSwisherExponentCase
    2 0 valuation (2 * p11MinimumMonodromyWeight) →
  valuation ≡ p11MinimumMonodromyWeight
p11ExponentCaseForcesMinimumMonodromyWeight
  (DS.singletonRational () pairedZero doubled)
p11ExponentCaseForcesMinimumMonodromyWeight
  (DS.multipleRational fixedMany pairedZero doubled) =
  NatP.*-cancelˡ-≡ valuation p11MinimumMonodromyWeight 2 doubled
  where
    valuation : Nat
    valuation = _
p11ExponentCaseForcesMinimumMonodromyWeight
  (DS.quadraticPresent () valuationZero minTwo)

------------------------------------------------------------------------
-- Same minimum as the p11 Deligne / Legendre ramification depth.
------------------------------------------------------------------------

p11J1728DepthIsMinimumMonodromyWeight :
  Ram.p11DeligneDepth Geo.j1728SS ≡ p11MinimumMonodromyWeight
p11J1728DepthIsMinimumMonodromyWeight = refl

p11EveryDeligneDepthAtLeastMinimum :
  (c : Geo.P11SupersingularJ) →
  p11MinimumMonodromyWeight ≤ Ram.p11DeligneDepth c
p11EveryDeligneDepthAtLeastMinimum Geo.jZeroSS =
  s≤s (s≤s z≤n)
p11EveryDeligneDepthAtLeastMinimum Geo.j1728SS =
  s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Explicit anti-collapse: the exponent is governed by the DIRECT monodromy /
-- ramification depth, not by reciprocal stack sheets.
------------------------------------------------------------------------

p11J1728SheetMultiplicityIsNotExponentDepth :
  Stack11.p11SheetMultiplicity Geo.j1728SS ≡ p11MinimumMonodromyWeight → ⊥
p11J1728SheetMultiplicityIsNotExponentDepth ()

record DuncanSwisherP11MonodromyExponentBoundary : Set where
  field
    minimumMonodromyWeightDerived : Bool
    fullAutMinimumIsTwiceMonodromyDerived : Bool
    theorem12CaseForcesExponentTwoWithoutMonsterTable : Bool
    exponentEqualsMinimumDeligneDepth : Bool
    reciprocalSheetMultiplicityUsedAsExponentDepth : Bool
    MonsterPrimeLaneTableUsed : Bool

canonicalDuncanSwisherP11MonodromyExponentBoundary :
  DuncanSwisherP11MonodromyExponentBoundary
canonicalDuncanSwisherP11MonodromyExponentBoundary = record
  { minimumMonodromyWeightDerived = true
  ; fullAutMinimumIsTwiceMonodromyDerived = true
  ; theorem12CaseForcesExponentTwoWithoutMonsterTable = true
  ; exponentEqualsMinimumDeligneDepth = true
  ; reciprocalSheetMultiplicityUsedAsExponentDepth = false
  ; MonsterPrimeLaneTableUsed = false
  }
