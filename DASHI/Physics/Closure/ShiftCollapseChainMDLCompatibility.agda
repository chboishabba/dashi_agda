module DASHI.Physics.Closure.ShiftCollapseChainMDLCompatibility where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)
open import Data.Nat using (_<_)

open import DASHI.Physics.Closure.ExecutionContract as EC
open import DASHI.Physics.Closure.ExecutionContractLaws as ECL
open import DASHI.Physics.Closure.MDLLyapunovCompatibility as MDLC
open import DASHI.Physics.Closure.ShiftCollapseDepthMDLCompatibility as OneStep
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.Closure.ShiftObservableSignatureReceiptInstance as SRI
open import DASHI.Physics.PressureGradientFlowShiftInstance as PGFSI
open import DASHI.Physics.PressureGradientFlowTerminalityShiftInstance as PGFTSI

------------------------------------------------------------------------
-- Whole-chain compatibility for the current shift carrier.
--
-- Pressure-flow chain:
--
--   start -> next -> held
--   depth 2 -> 1 -> 0
--
-- Execution-contract refinement:
--
--   start -> next -> middle -> held.
--
-- Thus the first pressure step is represented by one execution receipt, while
-- the final pressure step is refined by two execution receipts.  This module
-- packages that exact finite relationship.  It does not identify the pressure
-- and execution carriers globally, nor claim that MDL equals depth/potential.

record ShiftCollapseChainMDLCompatibility : Setω where
  field
    oneStepCompatibility :
      OneStep.ShiftCollapseDepthMDLCompatibility

    startToNextDepthStrict :
      PGFTSI.shiftCollapseDepth SPTI.shiftNextPoint
        <
      PGFTSI.shiftCollapseDepth SPTI.shiftStartPoint

    nextToHeldDepthStrict :
      PGFTSI.shiftCollapseDepth SPTI.shiftHeldExitPoint
        <
      PGFTSI.shiftCollapseDepth SPTI.shiftNextPoint

    startToNextPotentialStrict :
      PGFSI.shiftFlowPotential SPTI.shiftNextPoint
        <
      PGFSI.shiftFlowPotential SPTI.shiftStartPoint

    nextToHeldPotentialStrict :
      PGFSI.shiftFlowPotential SPTI.shiftHeldExitPoint
        <
      PGFSI.shiftFlowPotential SPTI.shiftNextPoint

    startToNextLyapunovReceipt :
      ECL.ExecutionContractLyapunovReceipt
        SRI.shiftExecutionContract
        SRI.shiftReceiptStart
        SRI.shiftReceiptNext

    nextToMiddleLyapunovReceipt :
      ECL.ExecutionContractLyapunovReceipt
        SRI.shiftExecutionContract
        SRI.shiftReceiptNext
        SRI.shiftReceiptMiddle

    middleToHeldLyapunovReceipt :
      ECL.ExecutionContractLyapunovReceipt
        SRI.shiftExecutionContract
        SRI.shiftReceiptMiddle
        SRI.shiftReceiptHeld

    startToNextMDLDescent :
      EC.MDLAdmissible
        SRI.shiftExecutionContract
        SRI.shiftReceiptStart
        SRI.shiftReceiptNext

    nextToMiddleMDLDescent :
      EC.MDLAdmissible
        SRI.shiftExecutionContract
        SRI.shiftReceiptNext
        SRI.shiftReceiptMiddle

    middleToHeldMDLDescent :
      EC.MDLAdmissible
        SRI.shiftExecutionContract
        SRI.shiftReceiptMiddle
        SRI.shiftReceiptHeld

    nonClaimBoundary : List String

open ShiftCollapseChainMDLCompatibility public

shiftNextToHeldDepthStrict :
  PGFTSI.shiftCollapseDepth SPTI.shiftHeldExitPoint
    <
  PGFTSI.shiftCollapseDepth SPTI.shiftNextPoint
shiftNextToHeldDepthStrict =
  PGFTSI.shiftCollapseDepthStrictOffHeldWitness
    SPTI.shiftNextPoint
    (λ ())

shiftNextToHeldPotentialStrict :
  PGFSI.shiftFlowPotential SPTI.shiftHeldExitPoint
    <
  PGFSI.shiftFlowPotential SPTI.shiftNextPoint
shiftNextToHeldPotentialStrict =
  PGFTSI.shiftCollapseDepthStrictOffHeldWitness
    SPTI.shiftNextPoint
    (λ ())

canonicalShiftCollapseChainMDLCompatibility :
  ShiftCollapseChainMDLCompatibility
canonicalShiftCollapseChainMDLCompatibility =
  record
    { oneStepCompatibility =
        OneStep.shiftCollapseDepthMDLCompatibility
    ; startToNextDepthStrict =
        OneStep.shiftLiveStepDepthStrict
    ; nextToHeldDepthStrict =
        shiftNextToHeldDepthStrict
    ; startToNextPotentialStrict =
        OneStep.shiftLiveStepPotentialStrict
    ; nextToHeldPotentialStrict =
        shiftNextToHeldPotentialStrict
    ; startToNextLyapunovReceipt =
        MDLC.currentShiftLyapunovReceipt
    ; nextToMiddleLyapunovReceipt =
        MDLC.currentShiftLyapunovReceiptNextMiddle
    ; middleToHeldLyapunovReceipt =
        MDLC.currentShiftLyapunovReceiptMiddleHeld
    ; startToNextMDLDescent =
        MDLC.currentShiftLyapunovDescent
    ; nextToMiddleMDLDescent =
        MDLC.currentShiftLyapunovDescentNextMiddle
    ; middleToHeldMDLDescent =
        MDLC.currentShiftLyapunovDescentMiddleHeld
    ; nonClaimBoundary =
        "ShiftCollapseChainMDLCompatibility is a bounded finite-chain compatibility surface only"
        ∷ "The pressure chain is start -> next -> held with exact depth/potential values 2 -> 1 -> 0"
        ∷ "The execution chain refines the final pressure step as next -> middle -> held"
        ∷ "All three execution transitions carry explicit Lyapunov receipts and MDL descent witnesses"
        ∷ "No global equality between collapse depth, potential, and MDL is claimed"
        ∷ "No continuum time, entropy, energy, or physical arrow-of-time theorem is implied"
        ∷ OneStep.nonClaimBoundary OneStep.shiftCollapseDepthMDLCompatibility
    }
