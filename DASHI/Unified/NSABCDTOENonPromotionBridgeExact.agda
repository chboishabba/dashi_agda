module DASHI.Unified.NSABCDTOENonPromotionBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSABCDMaxCut20261002Exact as MaxCut

------------------------------------------------------------------------
-- NAVIER-STOKES A/B/C/D -> DASHI TOE NON-PROMOTION BRIDGE
--
-- ZKP O/R/C/S/L/P/G/F.
--
-- O: Connect the current branch-local NS max-cut to the focused TOE graph.
-- R: Reuse the existing max-cut owner. Do not restate its PDE mathematics.
-- C: Export exact equality proofs for the current frontier and firewalls.
-- S: Keep A/B open theorem lanes and C/D source-audit lanes distinct.
-- L: This module owns only the NS-to-TOE normalization lane.
-- P: TOE consumers receive exact non-promotion and frontier-routing facts.
-- G: Original NS theorem owners retain mathematical and code ownership.
-- F: No Unifier placeholder axiom can discharge any theorem in this module.
--
-- Preconditions.
--   * NSABCDMaxCut20261002Exact is the branch-local max-cut owner.
--   * Its A, B, C, and D counts and audit facts are already theorem-owned.
--
-- Invariants.
--   * A finite compiler result is not a Clay proof.
--   * The R823 reserve route needs no extra reserve estimate after its two
--     physical decision leaves.
--   * Global rational helical projector laws do not gate the R829 decision.
--   * C/D source-coordinate audit does not equal independent reconstruction.
--
-- Postconditions.
--   * The TOE graph can import exact NS frontier facts.
--   * Clay promotion remains false.
------------------------------------------------------------------------

aMaxCutHasThreeIrreducibleLeaves :
  MaxCut.aIrreducibleLeafCount ≡ 3
aMaxCutHasThreeIrreducibleLeaves =
  MaxCut.aIrreducibleLeafCountIsThree

bDecisionHasTwoExternalLeaves :
  MaxCut.bDecisionExternalLeafCount ≡ 2
bDecisionHasTwoExternalLeaves =
  MaxCut.bDecisionExternalLeafCountIsTwo

bRealODEHasTwoInternalBridgeLeaves :
  MaxCut.bRealODEInternalBridgeLeafCount ≡ 2
bRealODEHasTwoInternalBridgeLeaves =
  MaxCut.bRealODEInternalBridgeLeafCountIsTwo

bPositiveFallbackHasSixLeaves :
  MaxCut.bPostReservePositiveRouteLeafCount ≡ 6
bPositiveFallbackHasSixLeaves =
  MaxCut.bPostReservePositiveRouteLeafCountIsSix

cOfficialSourceAuditIsClosed :
  MaxCut.cOfficialSourceAuditClosed ≡ true
cOfficialSourceAuditIsClosed =
  MaxCut.cOfficialSourceAuditClosedIsTrue

dOfficialSourceAuditIsClosed :
  MaxCut.dOfficialSourceAuditClosed ≡ true
dOfficialSourceAuditIsClosed =
  MaxCut.dOfficialSourceAuditClosedIsTrue

cdIndependentReconstructionDoesNotGateSourceAudit :
  MaxCut.cDIndependentDASHIReconstructionGatesSourceAudit ≡ false
cdIndependentReconstructionDoesNotGateSourceAudit =
  MaxCut.cDIndependentDASHIReconstructionGatesSourceAuditIsFalse

r823NeedsNoAdditionalReserveEstimateAfterDecisionLeaves :
  MaxCut.r823AdditionalReserveEstimateNeededAfterDecisionLeaves ≡ false
r823NeedsNoAdditionalReserveEstimateAfterDecisionLeaves =
  MaxCut.r823AdditionalReserveEstimateNeededAfterDecisionLeavesIsFalse

globalRationalHelicalProjectorLawsDoNotGateR829Decision :
  MaxCut.globalRationalHelicalProjectorLawsGateR829Decision ≡ false
globalRationalHelicalProjectorLawsDoNotGateR829Decision =
  MaxCut.globalRationalHelicalProjectorLawsGateR829DecisionIsFalse

nsClayPromotionRemainsFalse :
  MaxCut.clayPromotion ≡ false
nsClayPromotionRemainsFalse = refl

record NSABCDTOEConvergenceReceipt : Set where
  field
    preconditionAFrontierIsExplicit :
      MaxCut.aIrreducibleLeafCount ≡ 3

    preconditionBDecisionFrontierIsExplicit :
      MaxCut.bDecisionExternalLeafCount ≡ 2

    invariantRealODEBridgeIsExplicit :
      MaxCut.bRealODEInternalBridgeLeafCount ≡ 2

    invariantFallbackRouteIsExplicit :
      MaxCut.bPostReservePositiveRouteLeafCount ≡ 6

    invariantNoExtraR823ReserveEstimate :
      MaxCut.r823AdditionalReserveEstimateNeededAfterDecisionLeaves ≡ false

    invariantNoGlobalRationalHelicalGate :
      MaxCut.globalRationalHelicalProjectorLawsGateR829Decision ≡ false

    invariantCDSourceAuditDoesNotRequireIndependentReconstruction :
      MaxCut.cDIndependentDASHIReconstructionGatesSourceAudit ≡ false

    postconditionCSourceAuditClosed :
      MaxCut.cOfficialSourceAuditClosed ≡ true

    postconditionDSourceAuditClosed :
      MaxCut.dOfficialSourceAuditClosed ≡ true

    postconditionNoClayPromotion :
      MaxCut.clayPromotion ≡ false

canonicalNSABCDTOEConvergenceReceipt : NSABCDTOEConvergenceReceipt
canonicalNSABCDTOEConvergenceReceipt = record
  { preconditionAFrontierIsExplicit =
      aMaxCutHasThreeIrreducibleLeaves
  ; preconditionBDecisionFrontierIsExplicit =
      bDecisionHasTwoExternalLeaves
  ; invariantRealODEBridgeIsExplicit =
      bRealODEHasTwoInternalBridgeLeaves
  ; invariantFallbackRouteIsExplicit =
      bPositiveFallbackHasSixLeaves
  ; invariantNoExtraR823ReserveEstimate =
      r823NeedsNoAdditionalReserveEstimateAfterDecisionLeaves
  ; invariantNoGlobalRationalHelicalGate =
      globalRationalHelicalProjectorLawsDoNotGateR829Decision
  ; invariantCDSourceAuditDoesNotRequireIndependentReconstruction =
      cdIndependentReconstructionDoesNotGateSourceAudit
  ; postconditionCSourceAuditClosed =
      cOfficialSourceAuditIsClosed
  ; postconditionDSourceAuditClosed =
      dOfficialSourceAuditIsClosed
  ; postconditionNoClayPromotion =
      nsClayPromotionRemainsFalse
  }
