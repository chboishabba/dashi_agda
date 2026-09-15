module DASHI.Physics.Closure.NSTriadKNR571LeanGateAEnvelopeReceiptExact where

------------------------------------------------------------------------
-- R571 PERIODIC-B GATE-A: CROSS-PROVER RECEIPT
--
-- This is a receipt/status owner, not a second proof of the radial estimates.
-- The dedicated Aristotle/Lean tranche already contains theorem-bearing Lean
-- proofs for the periodic-B radial Gate-A leaves:
--
--   A1: |m_sigma(k+y) - m_sigma(k)| <= |y|       with constant 1
--   A2: centered radial defect <= |y|^2           with constant 1
--       on nonzero periodic lattice centres (|k| >= 1).
--
-- The source files are integrated in chboishabba/dashi_lean4 at commit
-- 7f60fa116f59a8f3f860fe53c13782ffc0d67ed6 from Aristotle task
-- 5fb665d1-24ad-4ca4-ae0b-9837e23d3bf0.
--
-- Firewalls:
-- * a Lean theorem receipt is not an Agda kernel receipt;
-- * the Lean radial theorem does not manufacture the exact Agda sample weld;
-- * neither radial receipt pays the state-side G2/G1 envelopes;
-- * none of these receipts pays R568 or the independent phase-production leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record R571LeanGateAEnvelopeReceipt : Set where
  constructor r571-lean-gate-a-envelope-receipt
  field
    lane : String
    repository : String
    integratedCommit : String
    aristotleTask : String
    radialSourcePath : String
    pairedSecondMomentSourcePath : String
    a1Theorem : String
    a2Theorem : String

    externalLeanKernelReceiptObserved : Bool
    localDashiLeanRebuildObservedByThisOwner : Bool

    leanGateAA1ReceiptObserved : Bool
    leanGateAA2ReceiptObserved : Bool

    agdaGateAA1SampleTransportObserved : Bool
    agdaGateAA2SampleTransportObserved : Bool

    g2PhysicalStateEnvelopePaid : Bool
    g1PhysicalStateEnvelopePaid : Bool
    r568Paid : Bool

open R571LeanGateAEnvelopeReceipt public

currentR571LeanGateAReceipt : R571LeanGateAEnvelopeReceipt
currentR571LeanGateAReceipt =
  r571-lean-gate-a-envelope-receipt
    "B — unforced periodic T^3"
    "chboishabba/dashi_lean4"
    "7f60fa116f59a8f3f860fe53c13782ffc0d67ed6"
    "5fb665d1-24ad-4ca4-ae0b-9837e23d3bf0"
    "ImportedLeans/aristotle-results/ns-5fb665d1-20260915/output-final_aristotle/RequestProject/NavierStokes/R571RadialCurvature.lean"
    "ImportedLeans/aristotle-results/ns-5fb665d1-20260915/output-final_aristotle/RequestProject/NavierStokes/R571PairedSecondMoment.lean"
    "RequestProject.NavierStokes.R571.abs_radialIncrement_le"
    "RequestProject.NavierStokes.R571.abs_centeredRadialDefect_le_of_one_le_norm"
    true
    false
    true
    true
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Compact status boundary for downstream archaeology/control surfaces.
------------------------------------------------------------------------

record R571GateACrossProverBoundary : Set where
  constructor r571-gate-a-cross-prover-boundary
  field
    radialMathematicsHasLeanReceipts : Bool
    radialLeanReceiptCreatesAgdaKernelReceipt : Bool
    radialLeanReceiptCreatesAgdaSampleTransport : Bool
    radialLeanReceiptPaysStateEnvelope : Bool
    radialLeanReceiptClosesR568 : Bool

canonicalR571GateACrossProverBoundary : R571GateACrossProverBoundary
canonicalR571GateACrossProverBoundary =
  r571-gate-a-cross-prover-boundary true false false false false
