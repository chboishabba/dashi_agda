module DASHI.Interop.NavierStokesFourLaneProofArchaeologyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Papers.NavierStokes.FourLaneProofProgramExact as Program
import DASHI.Physics.Closure.NSClayFourAlternativeReleasedProofBidiExact as Four
import DASHI.Physics.Closure.NSTriadKNFixedOutputSlotCollisionExact as Collision
import DASHI.Physics.Closure.NSTriadKNComparableConstantBandGramNoGoRound214Exact as R214

------------------------------------------------------------------------
-- NAVIER-STOKES FOUR-LANE ARCHAEOLOGY OVERLAY
--
-- Timestamp: 2026-09-15 09:32 AEST (UTC+10).
--
-- This is the NS-specific provenance companion to the canonical cross-lane
-- archaeology ledger. It does not replace the older round history. It freezes
-- the A/B/C/D lane names and records why the same-output Gram/P3 attempt was
-- retained historically but removed from the primary periodic-B producer path.
------------------------------------------------------------------------

record NSFourLaneArchaeology : Set where
  constructor ns-four-lane-archaeology
  field
    programme : Program.NSFourLaneProofProgram
    programmeIsCanonical : programme ≡ Program.canonicalNSFourLaneProofProgram

    sourceAlternativeA : Four.AlternativeStatusReceipt4
    sourceAlternativeB : Four.AlternativeStatusReceipt4
    sourceAlternativeC : Four.AlternativeStatusReceipt4
    sourceAlternativeD : Four.AlternativeStatusReceipt4

    periodicBPrimaryRoute : String
    wholeSpaceAIndependentRoute : String
    forcedCDVerificationRoute : String

    p3GramHistoryRetained : Bool
    p3GramNoLongerPrimary : Bool
    p3ExactCollisionLawConstructed : Bool
    p3ConcretePhysicalCollisionWitnessConstructed : Bool
    constantBandLocalizationAlonePaysDebt : Bool

    certificationFirewall : String

open NSFourLaneArchaeology public

canonicalNSFourLaneArchaeology : NSFourLaneArchaeology
canonicalNSFourLaneArchaeology =
  ns-four-lane-archaeology
    Program.canonicalNSFourLaneProofProgram
    refl
    Four.statusA4
    Four.statusB4
    Four.statusC4
    Four.statusD4
    "Periodic B active route: R571 signed helical carrier -> literal centered/Taylor realization -> paired second-order/second-moment -> six-three -> signed inner-fibre/full-square transport -> R568 -> R572 -> R503/R415."
    "Whole-space A remains an independent unforced R^3 obligation. Freeze its own producer/compiler/terminal cut before resuming named-field proof search; import B only through explicit typed transport."
    "Forced C/D are released-proof BIDI verification/provenance lanes. Preserve source snapshots, exact hypotheses, and DASHI same-object welds separately from mathematical discovery credit and prize/acceptance status."
    true
    true
    Collision.roundFixedOutputEqualAmplitudeCollisionLawClosed
    Collision.roundFixedOutputConcreteDistinctCCCollisionWitnessConstructed
    R214.round214ConstantShellBandAlonePaysGramDebt
    "MathematicalStatus, StatementStatus, and CertificationStatus are independent. A configured validation root or workflow target is not an observed commit-specific kernel receipt. External released-proof metadata is source evidence, not an independent DASHI rerun."

p3GramHistoryRetainedIsTrue :
  p3GramHistoryRetained canonicalNSFourLaneArchaeology ≡ true
p3GramHistoryRetainedIsTrue = refl

p3GramNoLongerPrimaryIsTrue :
  p3GramNoLongerPrimary canonicalNSFourLaneArchaeology ≡ true
p3GramNoLongerPrimaryIsTrue = refl

p3ExactCollisionLawConstructedIsTrue :
  p3ExactCollisionLawConstructed canonicalNSFourLaneArchaeology ≡ true
p3ExactCollisionLawConstructedIsTrue =
  Collision.roundFixedOutputEqualAmplitudeCollisionLawClosedIsTrue

p3ConcretePhysicalCollisionWitnessConstructedIsFalse :
  p3ConcretePhysicalCollisionWitnessConstructed canonicalNSFourLaneArchaeology
  ≡ false
p3ConcretePhysicalCollisionWitnessConstructedIsFalse =
  Collision.roundFixedOutputConcreteDistinctCCCollisionWitnessConstructedIsFalse

constantBandLocalizationAlonePaysDebtIsFalse :
  constantBandLocalizationAlonePaysDebt canonicalNSFourLaneArchaeology ≡ false
constantBandLocalizationAlonePaysDebtIsFalse =
  R214.round214ConstantShellBandAlonePaysGramDebtIsFalse
