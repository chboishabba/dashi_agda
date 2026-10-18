{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact where

------------------------------------------------------------------------
-- B / PREFERRED SOURCE-NATIVE R415 CONSTRUCTOR
--
-- This is the least-privilege physical input for the marked-expansion route.
-- It does not ask for the R415 fixed-Y sum inequality: Round354 compiles that
-- from marked charging + charged CMP116 summability.
------------------------------------------------------------------------

open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116Round354To415FixedYExact as FixedY

record PreferredR415Source
    (Domain Term Operator : Set) : Set₁ where
  field
    localizedDomains : List Domain
    termsWithCommonY : Domain → List Term
    selectedTerm : Domain → Term → R410.SelectedCMP116PathMarkedTerm Operator

    commonYBoundaryIntegrand commonYShell : Domain → ℝ
    selectedBoundaryIntegrand : ℝ

    commonYBoundaryIsSelectedTermSum :
      ∀ domain →
      commonYBoundaryIntegrand domain
      ≡ Resum.sumℝ
          (λ term → R410.differentiatedTerm (selectedTerm domain term))
          (termsWithCommonY domain)

    selectedBoundaryIsCommonYSum :
      selectedBoundaryIntegrand
      ≡ Resum.sumℝ commonYBoundaryIntegrand localizedDomains

    fixedYCharging :
      FixedY.R415FixedYCharging
        termsWithCommonY selectedTerm commonYShell

    geometry : R411.SelectedSupportConnectionGeometry Domain Term
    decay : R414.AntitoneNonnegativeDecayWeight

    everyLocalizedDomainConnects :
      ∀ domain → R411.domainConnectsBothSupports geometry domain

    domainAmplitude : Domain → ℝ
    domainAmplitudeNonnegative : ∀ domain → 0ℝ ≤ℝ domainAmplitude domain

    commonYShellBelowDomainDecay :
      ∀ domain →
      commonYShell domain
      ≤ℝ domainAmplitude domain
        *ℝ R414.weight decay (R411.domainTreeDistance geometry domain)

    sourceAmplitude : ℝ

    amplitudeSumBelowSourceAmplitude :
      Resum.sumℝ domainAmplitude localizedDomains ≤ℝ sourceAmplitude

open PreferredR415Source public

compilePreferredR415 :
  ∀ {Domain Term Operator} →
  PreferredR415Source Domain Term Operator →
  R415.SelectedCMP116MarkedExpansion Domain Term Operator
compilePreferredR415 source = record
  { R415.SelectedCMP116MarkedExpansion.localizedDomains =
      localizedDomains source
  ; R415.SelectedCMP116MarkedExpansion.termsWithCommonY =
      termsWithCommonY source
  ; R415.SelectedCMP116MarkedExpansion.selectedTerm =
      selectedTerm source
  ; R415.SelectedCMP116MarkedExpansion.commonYBoundaryIntegrand =
      commonYBoundaryIntegrand source
  ; R415.SelectedCMP116MarkedExpansion.commonYShell =
      commonYShell source
  ; R415.SelectedCMP116MarkedExpansion.selectedBoundaryIntegrand =
      selectedBoundaryIntegrand source
  ; R415.SelectedCMP116MarkedExpansion.commonYBoundaryIsSelectedTermSum =
      commonYBoundaryIsSelectedTermSum source
  ; R415.SelectedCMP116MarkedExpansion.selectedBoundaryIsCommonYSum =
      selectedBoundaryIsCommonYSum source
  ; R415.SelectedCMP116MarkedExpansion.selectedR410MajorantsBelowCommonYShell =
      FixedY.selectedR410MajorantsBelowCommonYShell (fixedYCharging source)
  ; R415.SelectedCMP116MarkedExpansion.geometry =
      geometry source
  ; R415.SelectedCMP116MarkedExpansion.decay =
      decay source
  ; R415.SelectedCMP116MarkedExpansion.everyLocalizedDomainConnects =
      everyLocalizedDomainConnects source
  ; R415.SelectedCMP116MarkedExpansion.domainAmplitude =
      domainAmplitude source
  ; R415.SelectedCMP116MarkedExpansion.domainAmplitudeNonnegative =
      domainAmplitudeNonnegative source
  ; R415.SelectedCMP116MarkedExpansion.commonYShellBelowDomainDecay =
      commonYShellBelowDomainDecay source
  ; R415.SelectedCMP116MarkedExpansion.sourceAmplitude =
      sourceAmplitude source
  ; R415.SelectedCMP116MarkedExpansion.amplitudeSumBelowSourceAmplitude =
      amplitudeSumBelowSourceAmplitude source
  }

preferredR415SelectedBoundaryDecay :
  ∀ {Domain Term Operator}
    (source : PreferredR415Source Domain Term Operator) →
  absℝ (selectedBoundaryIntegrand source)
  ≤ℝ
  sourceAmplitude source
    *ℝ R414.weight (decay source)
      (R411.selectedConnectingDistance (geometry source))
preferredR415SelectedBoundaryDecay source =
  R415.selectedBoundaryBelowSourceDecay (compilePreferredR415 source)

preferredR415CompilerLevel : ProofLevel
preferredR415CompilerLevel = machineChecked

-- Exact remaining B physics in this source-native presentation:
--  1. enumerate literal differentiated CMP116 terms as exact R410 terms;
--  2. prove marked charging and charged fixed-Y summability;
--  3. prove selected-support connection;
--  4. prove the per-Y tree/localisation majorant and amplitude sum.
literalPreferredR415SourceLevel : ProofLevel
literalPreferredR415SourceLevel = conditional
