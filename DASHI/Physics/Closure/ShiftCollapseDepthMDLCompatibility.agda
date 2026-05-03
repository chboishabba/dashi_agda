module DASHI.Physics.Closure.ShiftCollapseDepthMDLCompatibility where

open import Agda.Primitive using (Setω; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)
open import Data.Nat using (_<_; s≤s)

open import DASHI.Physics.Closure.ExecutionContract as EC
open import DASHI.Physics.Closure.ExecutionContractLaws as ECL
open import DASHI.Physics.Closure.MDLLyapunovCompatibility as MDLC
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.Closure.ShiftObservableSignatureReceiptInstance as SRI
open import DASHI.Physics.DynamicsCollapseDepthMonotone as DCDM
open import DASHI.Physics.DynamicsCollapseDepthPotentialBridge as DCDP
open import DASHI.Physics.PressureGradientFlowShiftInstance as PGFSI
open import DASHI.Physics.PressureGradientFlowTerminalityShiftInstance as PGFTSI

------------------------------------------------------------------------
-- Bounded compatibility surface between the current shift collapse-depth /
-- potential bridge and the live MDL Lyapunov receipt on the execution side.
--
-- This module does not claim a global identification between the finite
-- pressure carrier and the full execution-contract source/MDL spaces. It only
-- packages the one live start→next step where both surfaces are simultaneously
-- available.

record ShiftCollapseDepthMDLCompatibility : Setω where
  field
    collapseDepthMonotone :
      DCDM.DynamicsCollapseDepthMonotone
        {lzero} {lzero} {lzero} {lzero} {lzero} Nat

    collapseDepthPotentialBridge :
      DCDP.DynamicsCollapseDepthPotentialBridge
        {lzero} {lzero} {lzero} {lzero} {lzero} Nat

    lyapunovReceipt :
      ECL.ExecutionContractLyapunovReceipt
        SRI.shiftExecutionContract
        SRI.shiftReceiptStart
        SRI.shiftReceiptNext

    liveStepDepthStrict :
      PGFTSI.shiftCollapseDepth SPTI.shiftNextPoint
        <
      PGFTSI.shiftCollapseDepth SPTI.shiftStartPoint

    liveStepPotentialStrict :
      PGFSI.shiftFlowPotential SPTI.shiftNextPoint
        <
      PGFSI.shiftFlowPotential SPTI.shiftStartPoint

    liveStepMDLDescent :
      EC.MDLAdmissible
        SRI.shiftExecutionContract
        SRI.shiftReceiptStart
        SRI.shiftReceiptNext

    nonClaimBoundary : List String

open ShiftCollapseDepthMDLCompatibility public

shiftLiveStepDepthStrict :
  PGFTSI.shiftCollapseDepth SPTI.shiftNextPoint
    <
  PGFTSI.shiftCollapseDepth SPTI.shiftStartPoint
shiftLiveStepDepthStrict =
  PGFTSI.shiftCollapseDepthStrictOffHeldWitness
    SPTI.shiftStartPoint
    (λ ())

shiftLiveStepPotentialStrict :
  PGFSI.shiftFlowPotential SPTI.shiftNextPoint
    <
  PGFSI.shiftFlowPotential SPTI.shiftStartPoint
shiftLiveStepPotentialStrict
  rewrite sym
    (PGFTSI.shiftCollapseDepthPotentialAgreementWitness SPTI.shiftNextPoint)
        | sym
    (PGFTSI.shiftCollapseDepthPotentialAgreementWitness SPTI.shiftStartPoint)
  = shiftLiveStepDepthStrict

shiftCollapseDepthMDLCompatibility :
  ShiftCollapseDepthMDLCompatibility
shiftCollapseDepthMDLCompatibility =
  record
    { collapseDepthMonotone = PGFTSI.shiftDynamicsCollapseDepthMonotone
    ; collapseDepthPotentialBridge = PGFTSI.shiftDynamicsCollapseDepthPotentialBridge
    ; lyapunovReceipt = MDLC.currentShiftLyapunovReceipt
    ; liveStepDepthStrict = shiftLiveStepDepthStrict
    ; liveStepPotentialStrict = shiftLiveStepPotentialStrict
    ; liveStepMDLDescent = MDLC.currentShiftLyapunovDescent
    ; nonClaimBoundary =
        "ShiftCollapseDepthMDLCompatibility is a bounded one-step compatibility surface only"
        ∷ "liveStepDepthStrict and liveStepPotentialStrict live on the finite pressure carrier"
        ∷ "liveStepMDLDescent lives on the execution-contract state carrier"
        ∷ "No global equality between collapse depth, potential, and MDL is claimed"
        ∷ "No repo-wide entropy or energy theorem is implied"
        ∷ DCDM.nonClaimBoundary PGFTSI.shiftDynamicsCollapseDepthMonotone
    }
