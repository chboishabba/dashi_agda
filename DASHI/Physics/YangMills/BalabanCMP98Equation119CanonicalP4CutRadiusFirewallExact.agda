{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalP4CutRadiusFirewallExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): CANONICAL P4 CHART-RADIUS FIREWALL
--
-- Primary source context:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 605--636.
-- DOI: 10.1007/BF01229381.
--
-- R175 requires
--
--     1/24 <= selected Eq.(119) cut radius.
--
-- The repository's canonical P4 common-parameter tuple independently fixes
--
--     chartRadius = 1/64.
--
-- Since 1/64 < 1/24, the P4 radius cannot pay R175 IF the two radii are
-- identified.  Repository search found no theorem making that same-object
-- identification, so this file does not claim the selected Eq.(119) cut is the
-- P4 radius.  It proves only the exact conditional no-go and thereby prevents
-- accidental radius conflation.
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP4CommonParameterDomainExact as P4
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedExistingCutRound175Exact as R175

canonicalP4ChartRadiusStrictlyBelowCMP98SourceThreshold :
  P4.chartRadius P4.canonicalClayParameters < Chart.sourceDefectThreshold
canonicalP4ChartRadiusStrictlyBelowCMP98SourceThreshold =
  toWitness
    {a? =
      P4.chartRadius P4.canonicalClayParameters
      ℚP.<?
      Chart.sourceDefectThreshold}
    _

canonicalP4ChartRadiusCannotPayCMP98SourceThreshold :
  ¬ (Chart.sourceDefectThreshold ≤ P4.chartRadius P4.canonicalClayParameters)
canonicalP4ChartRadiusCannotPayCMP98SourceThreshold alleged =
  ℚP.<⇒≱ canonicalP4ChartRadiusStrictlyBelowCMP98SourceThreshold alleged

r175SelectedCutCannotBeCanonicalP4Radius :
  ∀ {C n Value group CoarseField FineField Lie}
    {source : R158.CanonicalL13Equation119Source C n Value group}
    {weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie}
      source} →
  (cutInputs : R175.SelectedExistingCutInputs source weld) →
  Path.chartRadius (Selected.cutData (R170.bridge weld))
    ≡ P4.chartRadius P4.canonicalClayParameters →
  ⊥
r175SelectedCutCannotBeCanonicalP4Radius cutInputs radiusIdentification =
  canonicalP4ChartRadiusCannotPayCMP98SourceThreshold
    (subst
      (λ radius → Chart.sourceDefectThreshold ≤ radius)
      radiusIdentification
      (R175.sourceThresholdBelowSelectedCut cutInputs))

-- Equivalently: any successful R175 selected-cut instantiation must keep its
-- radius distinct from the canonical P4 chart radius, unless the P4 parameter
-- tuple itself is changed.
record Eq119SelectedCutRadiusBoundary : Set where
  field
    canonicalP4RadiusCannotPayR175 :
      ¬ (Chart.sourceDefectThreshold ≤ P4.chartRadius P4.canonicalClayParameters)

canonicalEq119SelectedCutRadiusBoundary : Eq119SelectedCutRadiusBoundary
canonicalEq119SelectedCutRadiusBoundary = record
  { Eq119SelectedCutRadiusBoundary.canonicalP4RadiusCannotPayR175 =
      canonicalP4ChartRadiusCannotPayCMP98SourceThreshold
  }

cmp98Equation119CanonicalP4CutRadiusFirewallLevel : ProofLevel
cmp98Equation119CanonicalP4CutRadiusFirewallLevel = machineChecked
