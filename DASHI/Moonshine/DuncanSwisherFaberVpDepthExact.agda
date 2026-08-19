module DASHI.Moonshine.DuncanSwisherFaberVpDepthExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Remark 1.4 states, for every prime p,
--
--   m_p = v_p(j | V_p - Phi_p(j)),
--
-- where Phi_p is the p-th Faber polynomial.  Theorem 1.2 then uses the SAME
-- m_p together with the rational/non-rational supersingular stratum to recover
-- v_p(|M|) for p>3.
--
-- DASHI CONTRIBUTION
--
-- Give the Faber discrepancy its own source-native Laurent-series observer,
-- but DO NOT introduce another owner for m_p.  The source equality identifies
-- the discrepancy valuation with `minimumAutomorphismOrder` from the canonical
-- DuncanSwisherMonsterExponentFormulaExact authority.
--
-- Consequently Theorem 1.2 can be restated directly in terms of Faber depth:
--
--   singleton rational:   2 v_p(|M|) = 3 d_Faber,
--   multiple rational:    2 v_p(|M|) = d_Faber,
--   quadratic locus:      v_p(|M|) = 0.
--
-- The module also exposes the exact bridge to the independently represented
-- Deligne first-pole scale:
--
--   d_Faber = m_p = 2 d_min.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)
open import Data.Nat using (_≤_; _*_; s≤s; z≤n)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.FormalLaurentFaberVpDiscrepancyExact as Faber
import DASHI.Moonshine.FormalLaurentQSeriesUNValuationSelectionExact as LaurentVal
import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as DS
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Deligne

------------------------------------------------------------------------
-- Source-native Faber discrepancy valuation.  The coefficient valuation itself
-- remains explicit because the repo has not introduced a global p-adic integer
-- valuation implementation on Z.
------------------------------------------------------------------------

record DuncanSwisherFaberVpAuthority (p : Nat) : Set₁ where
  field
    surface : Faber.FaberVpDiscrepancySurface p
    coefficientPadicValuation : ℤ → Nat
    discrepancyDepth : Nat

    valuationWitness :
      LaurentVal.LaurentSeriesValuationWitness
        coefficientPadicValuation
        (Faber.faberVpDiscrepancy surface)
        discrepancyDepth

open DuncanSwisherFaberVpAuthority public

postulate
  publishedDuncanSwisherFaberVpAuthority :
    (p : Nat) → Prime p → DuncanSwisherFaberVpAuthority p

------------------------------------------------------------------------
-- Remark 1.4: this is the ONLY bridge to m_p.  No duplicate minimum-aut field
-- is stored inside the Faber authority.
------------------------------------------------------------------------

postulate
  publishedFaberDepthEqualsMinimumAutomorphismOrder :
    (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
    discrepancyDepth (publishedDuncanSwisherFaberVpAuthority p prime)
    ≡ DS.minimumAutomorphismOrder
        (DS.publishedDuncanSwisherExponentAuthority p prime ge5)

------------------------------------------------------------------------
-- Constructor-indexed Theorem-1.2 conclusion expressed only in Faber depth.
------------------------------------------------------------------------

faberConclusionByExponentCase :
  {fixed paired valuation minimumAut faberDepth : Nat} →
  DS.DuncanSwisherExponentCase fixed paired valuation minimumAut →
  faberDepth ≡ minimumAut →
  Set
faberConclusionByExponentCase
  (DS.singletonRational fixedOne pairedZero doubled) depthEqualsMinimum =
  2 * valuation ≡ 3 * faberDepth
faberConclusionByExponentCase
  (DS.multipleRational fixedMany pairedZero doubled) depthEqualsMinimum =
  2 * valuation ≡ faberDepth
faberConclusionByExponentCase
  (DS.quadraticPresent pairedPositive valuationZero minTwo) depthEqualsMinimum =
  valuation ≡ 0

faberDepthExponentClassification :
  {fixed paired valuation minimumAut faberDepth : Nat} →
  (case : DS.DuncanSwisherExponentCase fixed paired valuation minimumAut) →
  (depthEqualsMinimum : faberDepth ≡ minimumAut) →
  faberConclusionByExponentCase case depthEqualsMinimum
faberDepthExponentClassification
  (DS.singletonRational fixedOne pairedZero doubled) depthEqualsMinimum =
  trans doubled
    (cong (λ n → 3 * n) (sym depthEqualsMinimum))
faberDepthExponentClassification
  (DS.multipleRational fixedMany pairedZero doubled) depthEqualsMinimum =
  trans doubled (sym depthEqualsMinimum)
faberDepthExponentClassification
  (DS.quadraticPresent pairedPositive valuationZero minTwo) depthEqualsMinimum =
  valuationZero

publishedFaberDepthExponentClassification :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  let
    E = DS.publishedDuncanSwisherExponentAuthority p prime ge5
    F = publishedDuncanSwisherFaberVpAuthority p prime
  in
  faberConclusionByExponentCase
    (DS.theorem12 E)
    (publishedFaberDepthEqualsMinimumAutomorphismOrder p prime ge5)
publishedFaberDepthExponentClassification p prime ge5 =
  faberDepthExponentClassification
    (DS.theorem12 (DS.publishedDuncanSwisherExponentAuthority p prime ge5))
    (publishedFaberDepthEqualsMinimumAutomorphismOrder p prime ge5)

------------------------------------------------------------------------
-- Generic Faber <-> Deligne scale weld.  This is deliberately parameterized by
-- a SAME-minimum witness rather than pretending Deligne's three finite
-- automorphism types already carry an arbitrary-prime supersingular family.
------------------------------------------------------------------------

record FaberDeligneSameMinimum (p : Nat) : Set₁ where
  field
    faberAuthority : DuncanSwisherFaberVpAuthority p
    deligneMinimum : Deligne.MinimumAutomorphismWitness
    sameMinimum :
      discrepancyDepth faberAuthority
      ≡ Deligne.minimumFullOrder deligneMinimum

open FaberDeligneSameMinimum public

faberDepthEqualsTwiceDeligneMinimum :
  {p : Nat} →
  (W : FaberDeligneSameMinimum p) →
  discrepancyDepth (faberAuthority W)
  ≡ 2 * Deligne.minimumFirstPoleDepth (deligneMinimum W)
faberDepthEqualsTwiceDeligneMinimum W =
  trans
    (sameMinimum W)
    (sym (Deligne.minimumDepthDoublesToMinimumFullOrder (deligneMinimum W)))

------------------------------------------------------------------------
-- A source equality at the declared consumer is not a carrier identity.
------------------------------------------------------------------------

record DuncanSwisherFaberVpDepthBoundary : Set where
  field
    signedLaurentFaberDiscrepancyConsumed : Bool
    coefficientMinimumWitnessCarried : Bool
    remark14DepthEqualsMpImported : Bool
    duplicateMpOwnerIntroduced : Bool
    theorem12RewrittenInFaberDepth : Bool
    deligneDepthScaleWeldDerived : Bool
    faberCarrierIdentifiedWithSupersingularCarrier : Bool
    faberCarrierIdentifiedWithThreeHauptmodulValuations : Bool
    theoremCoversTwoAndThreeThroughTheorem12 : Bool

canonicalDuncanSwisherFaberVpDepthBoundary :
  DuncanSwisherFaberVpDepthBoundary
canonicalDuncanSwisherFaberVpDepthBoundary = record
  { signedLaurentFaberDiscrepancyConsumed = true
  ; coefficientMinimumWitnessCarried = true
  ; remark14DepthEqualsMpImported = true
  ; duplicateMpOwnerIntroduced = false
  ; theorem12RewrittenInFaberDepth = true
  ; deligneDepthScaleWeldDerived = true
  ; faberCarrierIdentifiedWithSupersingularCarrier = false
  ; faberCarrierIdentifiedWithThreeHauptmodulValuations = false
  ; theoremCoversTwoAndThreeThroughTheorem12 = false
  }
