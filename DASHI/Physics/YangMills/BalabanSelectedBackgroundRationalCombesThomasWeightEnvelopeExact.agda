module DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightEnvelopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Complete the finite envelope for the explicit rational side-four
-- Combes--Thomas weight already used by the selected-background Green lane.
-- The existing theorem gives
--
--   d(x) g(x) = 1,   0 <= g(x),   d(x) <= 1,
--   g(x) <= 6561/4096.
--
-- Hence monotonicity gives
--
--   1 = g(x)d(x) <= g(x),
--
-- and therefore the literal growth weight satisfies
--
--   1 <= g(x) <= 6561/4096
--
-- pointwise on the complete side-four multiplier carrier.  This discharges
-- the finite weight-envelope part of the G2 weighted-to-ordinary-row adapter;
-- it does NOT manufacture the independent physical K+ weighted locality
-- estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact as Difference
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightExact as Weight

siteGrowthAboveOne : ∀ site → 1ℚ ≤ Weight.siteGrowthWeight site
siteGrowthAboveOne site =
  let
    growth = Weight.siteGrowthWeight site
    decay = Weight.siteDecayWeight site

    instance
      growthNN : NonNegative growth
      growthNN = ℚ.nonNegative (Weight.siteGrowthNonnegative site)

    scaled : growth * decay ≤ growth * 1ℚ
    scaled = ℚP.*-monoˡ-≤-nonNeg growth (Weight.siteDecayBelowOne site)

    inverseReordered : growth * decay ≡ 1ℚ
    inverseReordered = trans
      (ℚP.*-comm growth decay)
      (Weight.siteWeightInverseExact site)
  in
  subst
    (λ lower → lower ≤ growth)
    inverseReordered
    (subst
      (λ upper → growth * decay ≤ upper)
      (ℚP.*-identityʳ growth)
      scaled)

gaugeInverseWeightAboveOne : ∀ root row →
  1ℚ ≤ Weight.gaugeInverseWeight root row
gaugeInverseWeightAboveOne
    (pair rootCoordinate rootSite)
    (pair coordinate site) =
  siteGrowthAboveOne (Difference.subtractSite4 site rootSite)

gaugeInverseWeightEnvelope : ∀ root row →
  1ℚ ≤ Weight.gaugeInverseWeight root row
  × Weight.gaugeInverseWeight root row ≤ Weight.siteGrowthEnvelope
gaugeInverseWeightEnvelope root row =
  gaugeInverseWeightAboveOne root row
  , Weight.gaugeInverseWeightBelowEnvelope root row

selectedSide4CombesThomasWeightEnvelopeLevel : ProofLevel
selectedSide4CombesThomasWeightEnvelopeLevel = machineChecked
