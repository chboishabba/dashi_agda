{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralMarkedChargingToR415Exact where

------------------------------------------------------------------------
-- ROUND417 / EXACT R410 CHARGING -> PREFERRED R415 FIXED-Y INPUT
--
-- Round416 owns one selected R410 term family at one localization domain.
-- This module quantifies it over domains and feeds the already-created
-- Round354->R415 compiler.  Consequently R415 no longer needs an independently
-- supplied fixed-Y majorant inequality.
------------------------------------------------------------------------

open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116LiteralMarkedChargingRound416Exact as R416
import DASHI.Physics.YangMills.BalabanCMP116Round354To415FixedYExact as FixedY

record LiteralR415FixedYCharging
    (Domain Term Operator : Set)
    (termsWithCommonY : Domain → List Term)
    (selectedTerm : Domain → Term → R410.SelectedCMP116PathMarkedTerm Operator)
    (commonYShell : Domain → ℝ)
    : Set₁ where
  field
    charging :
      ∀ domain →
      R416.LiteralR410MarkedCharging
        Term Operator
        (termsWithCommonY domain)
        (selectedTerm domain)
        (commonYShell domain)

open LiteralR415FixedYCharging public

asFixedYCharging :
  ∀ {Domain Term Operator termsWithCommonY selectedTerm commonYShell} →
  LiteralR415FixedYCharging
    Domain Term Operator termsWithCommonY selectedTerm commonYShell →
  FixedY.R415FixedYCharging termsWithCommonY selectedTerm commonYShell
asFixedYCharging dataSet = record
  { FixedY.R415FixedYCharging.chargedMajorant =
      λ domain → R416.chargedMajorant (charging dataSet domain)
  ; FixedY.R415FixedYCharging.canonicalR410BelowCharged =
      λ domain → R416.canonicalR410BelowCharged (charging dataSet domain)
  ; FixedY.R415FixedYCharging.chargedCMP116Summability =
      λ domain → R416.chargedSummability (charging dataSet domain)
  }

literalR415FixedYChargingCompilerLevel : ProofLevel
literalR415FixedYChargingCompilerLevel = machineChecked

-- The per-domain physical content is entirely Round416's source attachment;
-- no extra fixed-Y theorem remains here.
literalR415FixedYChargingAttachmentLevel : ProofLevel
literalR415FixedYChargingAttachmentLevel =
  R416.literalR410MarkedChargingAttachmentLevel
