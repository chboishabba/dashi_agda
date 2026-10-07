module DASHI.Moonshine.OggSSP2BCompletionAcquisitionFrontierExact where

------------------------------------------------------------------------
-- CANONICAL 2B COMPLETION ACQUISITION FRONTIER
--
-- This owner keeps the post-Brauer completion programme focused on the one
-- remaining same-object acquisition rather than reopening numeric discovery.
--
-- Paid:
--   * Tate-vs-duad 2-regular Brauer fingerprint / semisimplified ingress;
--   * M22 10a/10b finite composition-factor identification;
--   * M22:2 outer J2^5 Completion10 source;
--   * generic three-fibre Tate transport compiler;
--   * binary-tetrahedral defect invariant and 4 -> 2-bit D reduction.
--
-- Newly available acquisition routes:
--   * explicit MeatAxe N<=S chain screen on the finite duad-276 M22:2 module;
--   * source-native normal 2^10 in 2^10:M22:2 < Fi22:2;
--   * externally constructed 196882-dimensional Monster representation over F2.
--
-- Not paid:
--   * an actual M22:2-stable N<=S<=Hhat0(2B,V2) whose quotient is the selected
--     10d module and carries the sourced outer J2^5 action;
--   * the two external D provenance bits;
--   * downstream 30->31->279 same-object promotions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSP2BTate276M24BrauerRuntimeReceiptExact as Brauer
import DASHI.Moonshine.OggSSP2BPostBrauerSameObjectFrontierExact as Post
import DASHI.Moonshine.OggSSP2BFi22d2NaturalTenSourceExact as Fi22
import DASHI.Moonshine.OggSSP2BMonsterGF2RepresentationSourceExact as MonsterF2
import DASHI.Moonshine.OggSSP2BDefectProvenanceSearchNoGoExact as DNoGo

record CompletionAcquisitionStatus : Set where
  constructor completion-acquisition-status
  field
    semisimplifiedTateDuadIngressPaid : Bool
    finiteM22TenFactorsPaid : Bool
    finiteM22d2OuterJ2x5Paid : Bool
    finiteDuadExplicitStableSubquotientScreenImplemented : Bool
    finiteDuadExplicitStableSubquotientRuntimePaid : Bool
    fi22NaturalTenSourceDonorPaid : Bool
    fi22NaturalTenRuntimeIdentificationPaid : Bool
    monsterGF2RepresentationSourcePaid : Bool
    monsterGF2ActionProgramsPresentInRepo : Bool
    actualTateStableTenSubquotientPaid : Bool
    actualOuterJ2x5OnSameTateQuotientPaid : Bool
    remainingDefectSourceBits : Nat
    defectSourceSelectionPaid : Bool
    downstream31PromotionPaid : Bool
    downstream279PromotionPaid : Bool
    nextResidual : String

canonicalCompletionAcquisitionStatus : CompletionAcquisitionStatus
canonicalCompletionAcquisitionStatus =
  completion-acquisition-status
    true true true
    true false
    true false
    true false
    false false
    2 false
    false false
    "Execute and ingest the finite M22:2-on-duad stable-subquotient and Fi22:2 natural-2^10 screens; then acquire/reconstruct the Parker-Wilson Monster GF(2) vector-action implementation (mop2/vecsuz/vecT), or equivalent 2B-local restriction data, and construct the same N<=S chain inside Hhat0(2B,V2). Separately source the two remaining Mode5/2T orientation bits."

postBrauerSemisimplifiedIngressAlreadyPaid :
  Brauer.semisimplifiedIngressPaid Brauer.canonicalTate276M24BrauerRuntimeReceipt ≡ true
postBrauerSemisimplifiedIngressAlreadyPaid = Brauer.semisimplifiedIngressIsPaid

fi22NaturalTenRankIsTen : Fi22.normalKernelF2Rank ≡ 10
fi22NaturalTenRankIsTen = Fi22.normalKernelRankIsTen

monsterGF2DimensionIs196882 : MonsterF2.monsterGF2Dimension ≡ 196882
monsterGF2DimensionIs196882 = MonsterF2.monsterGF2DimensionExact

remainingDefectSourceBitsIsTwo : DNoGo.remainingSourceDecisionCount ≡ 2
remainingDefectSourceBitsIsTwo = DNoGo.remainingSourceDecisionCountIsTwo
