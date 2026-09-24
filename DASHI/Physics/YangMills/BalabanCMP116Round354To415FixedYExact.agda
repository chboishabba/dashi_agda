{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116Round354To415FixedYExact where

------------------------------------------------------------------------
-- B / ROUND354 CHARGING -> R415 FIXED-Y R410 SUM
--
-- R415's fixed-Y field is not a new summation theorem.  On the exact R410
-- term list, it follows from:
--
--   canonical R410 majorant <= charged majorant
--   + sum charged majorant <= commonY shell.
--
-- Round354 already owns that finite positive-sum compiler.  This module binds
-- it to the literal R415 term list, so B's fixed-Y residue is exactly the
-- marked charging geometry plus the source CMP116 charged summability.
------------------------------------------------------------------------

open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanMarkedWalkChargingCutRound354Exact as R354
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410

record R415FixedYCharging
    {Domain Term Operator : Set}
    (termsWithCommonY : Domain → List Term)
    (selectedTerm :
      Domain → Term →
      R410.SelectedCMP116PathMarkedTerm Operator)
    (commonYShell : Domain → ℝ) : Set₁ where
  field
    chargedMajorant : Domain → Term → ℝ

    canonicalR410BelowCharged :
      ∀ domain term →
      R415.canonicalTermMajorant (selectedTerm domain term)
      ≤ℝ chargedMajorant domain term

    chargedCMP116Summability :
      ∀ domain →
      Resum.sumℝ
        (chargedMajorant domain)
        (termsWithCommonY domain)
      ≤ℝ commonYShell domain

open R415FixedYCharging public

chargingData :
  ∀ {Domain Term Operator}
    {termsWithCommonY : Domain → List Term}
    {selectedTerm :
      Domain → Term →
      R410.SelectedCMP116PathMarkedTerm Operator}
    {commonYShell : Domain → ℝ} →
  R415FixedYCharging termsWithCommonY selectedTerm commonYShell →
  ∀ domain →
  R354.MarkedWalkChargingData Term
chargingData {termsWithCommonY = termsWithCommonY}
    {selectedTerm = selectedTerm} {commonYShell = commonYShell}
    dataSet domain = record
  { R354.MarkedWalkChargingData.survivingWalks =
      termsWithCommonY domain
  ; R354.MarkedWalkChargingData.rawMarkedMajorant =
      λ term → R415.canonicalTermMajorant (selectedTerm domain term)
  ; R354.MarkedWalkChargingData.chargedMajorant =
      chargedMajorant dataSet domain
  ; R354.MarkedWalkChargingData.envelope =
      commonYShell domain
  ; R354.MarkedWalkChargingData.rawMarkedBelowCharged =
      canonicalR410BelowCharged dataSet domain
  ; R354.MarkedWalkChargingData.chargedSummability =
      chargedCMP116Summability dataSet domain
  }

selectedR410MajorantsBelowCommonYShell :
  ∀ {Domain Term Operator}
    {termsWithCommonY : Domain → List Term}
    {selectedTerm :
      Domain → Term →
      R410.SelectedCMP116PathMarkedTerm Operator}
    {commonYShell : Domain → ℝ}
    (dataSet : R415FixedYCharging termsWithCommonY selectedTerm commonYShell) →
  ∀ domain →
  Resum.sumℝ
    (λ term → R415.canonicalTermMajorant (selectedTerm domain term))
    (termsWithCommonY domain)
  ≤ℝ commonYShell domain
selectedR410MajorantsBelowCommonYShell dataSet domain =
  R354.rawMarkedSummabilityFromCharging (chargingData dataSet domain)

round354ToR415FixedYCompilerLevel : ProofLevel
round354ToR415FixedYCompilerLevel = machineChecked

literalR410MarkedChargingGeometryLevel : ProofLevel
literalR410MarkedChargingGeometryLevel = conditional

literalCMP116ChargedFixedYSummabilityLevel : ProofLevel
literalCMP116ChargedFixedYSummabilityLevel = conditional
