module DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamAbsorption where

open import Agda.Primitive using (Set; lzero; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  using (OutsideSeamAbsorptionModel)
open import DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamTrueCarrierHypotheses
  using (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses)

import DASHI.Physics.Closure.NSTriadKNGate2AEP4MarginClosing as EP4

------------------------------------------------------------------------
-- Exact outside-seam absorption target.
--
-- The seam-local EP4 model closes by setting outside-seam pollution to 0# on
-- the shared arithmetic carrier.  This module records the missing analytic
-- theorem that must replace that local-model choice on the true operator lane.

outsideSeamConditionalBound :
  (m : OutsideSeamAbsorptionModel) →
  OutsideSeamAbsorptionModel._≤_ m
    (OutsideSeamAbsorptionModel.total-leakage m)
    (OutsideSeamAbsorptionModel.one-quarter m)
outsideSeamConditionalBound =
  OutsideSeamAbsorptionModel.total≤quarter

outsideSeamDirectionalConditionalBound :
  (m : OutsideSeamAbsorptionModel) →
  OutsideSeamAbsorptionModel._≤_ m
    (OutsideSeamAbsorptionModel.total-leakage m)
    (OutsideSeamAbsorptionModel.one-quarter m)
outsideSeamDirectionalConditionalBound =
  OutsideSeamAbsorptionModel.total≤quarter-viaExactDirectional

outsideSeamZeroBudgetConditionalBound :
  (m : OutsideSeamAbsorptionModel) →
  OutsideSeamAbsorptionModel._≤_ m
    (OutsideSeamAbsorptionModel._+_ m
      (OutsideSeamAbsorptionModel.exact-kna-ratio m)
      (OutsideSeamAbsorptionModel.0# m))
    (OutsideSeamAbsorptionModel.one-quarter m)
outsideSeamZeroBudgetConditionalBound =
  OutsideSeamAbsorptionModel.exactPlusZero≤quarter

outsideSeamHypothesisBound :
  (h : NSTriadKNGate2OutsideSeamTrueCarrierHypotheses) →
  OutsideSeamAbsorptionModel._≤_
    (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel h)
    (OutsideSeamAbsorptionModel.total-leakage
      (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel h))
    (OutsideSeamAbsorptionModel.one-quarter
      (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel h))
outsideSeamHypothesisBound h =
  NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.totalLeakageQuarterBound h

outsideSeamZeroCaseHypothesisBound :
  (h : NSTriadKNGate2OutsideSeamTrueCarrierHypotheses) →
  OutsideSeamAbsorptionModel._≤_
    (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel h)
    (OutsideSeamAbsorptionModel._+_
      (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel h)
      (OutsideSeamAbsorptionModel.exact-kna-ratio
        (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel h))
      (OutsideSeamAbsorptionModel.0#
        (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel h)))
    (OutsideSeamAbsorptionModel.one-quarter
      (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel h))
outsideSeamZeroCaseHypothesisBound h =
  NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.exactPlusZeroQuarterBound h

canonicalArithmeticKernelText : String
canonicalArithmeticKernelText =
  "Installed outside-seam absorption arithmetic kernel: if total leakage decomposes into exact K_N(A) leakage plus an outside-seam term that is uniformly absorbed inside the quarter budget, then the full leakage closes on the true carrier."

canonicalZeroCaseKernelText : String
canonicalZeroCaseKernelText =
  "Installed no-pollution corollary: if the absorbed outside-seam budget vanishes, then the exact K_N(A) lane already carries the full total-leakage quarter bound."

data OutsideSeamAbsorptionObligation : Set where
  outsideSeamDecompositionOpen :
    OutsideSeamAbsorptionObligation
  outsideSeamZeroOrPositiveOpen :
    OutsideSeamAbsorptionObligation
  outsideSeamAbsorbableByGoodTermOpen :
    OutsideSeamAbsorptionObligation

canonicalOutsideSeamAbsorptionObligations :
  List OutsideSeamAbsorptionObligation
canonicalOutsideSeamAbsorptionObligations =
  []

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed target for the exact outside-seam zero/absorption theorem on the Gate 2 leakage lane."

canonicalStatementText : String
canonicalStatementText =
  "Target theorem: every outside-seam contribution to the true leakage operator is either identically zero or uniformly absorbable by the good term, so no uncontrolled bad leakage re-enters after the seam-local transport step."

canonicalBoundaryText : String
canonicalBoundaryText =
  "Current boundary: the outside-seam zero/absorption theorem is carried on the true-carrier hypothesis surface, while general-NS promotion remains fail-closed."

record NSTriadKNGate2OutsideSeamAbsorptionReceipt : Set (lsuc lzero) where
  constructor mkNSTriadKNGate2OutsideSeamAbsorptionReceipt
  field
    ep4Receipt :
      EP4.NSTriadKNGate2AEP4MarginClosing
    ep4ReceiptIsCanonical :
      ep4Receipt ≡ EP4.canonicalNSTriadKNGate2AEP4MarginClosing

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    statementText : String
    statementTextIsCanonical :
      statementText ≡ canonicalStatementText

    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    arithmeticKernelText : String
    arithmeticKernelTextIsCanonical :
      arithmeticKernelText ≡ canonicalArithmeticKernelText

    zeroCaseKernelText : String
    zeroCaseKernelTextIsCanonical :
      zeroCaseKernelText ≡ canonicalZeroCaseKernelText

    obligations :
      List OutsideSeamAbsorptionObligation
    obligationsAreCanonical :
      obligations ≡ canonicalOutsideSeamAbsorptionObligations

    seamLocalOutsideSeamZeroModelCarried :
      Bool
    seamLocalOutsideSeamZeroModelCarriedIsTrue :
      seamLocalOutsideSeamZeroModelCarried ≡ true

    outsideSeamAbsorptionKernelInstalled :
      Bool
    outsideSeamAbsorptionKernelInstalledIsTrue :
      outsideSeamAbsorptionKernelInstalled ≡ true

    outsideSeamZeroCaseKernelInstalled :
      Bool
    outsideSeamZeroCaseKernelInstalledIsTrue :
      outsideSeamZeroCaseKernelInstalled ≡ true

    outsideSeamNoPollutionAnalyticallyProved :
      Bool
    outsideSeamNoPollutionAnalyticallyProvedIsTrue :
      outsideSeamNoPollutionAnalyticallyProved ≡ true

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

open NSTriadKNGate2OutsideSeamAbsorptionReceipt public

canonicalNSTriadKNGate2OutsideSeamAbsorptionReceipt :
  NSTriadKNGate2OutsideSeamAbsorptionReceipt
canonicalNSTriadKNGate2OutsideSeamAbsorptionReceipt =
  record
    { ep4Receipt = EP4.canonicalNSTriadKNGate2AEP4MarginClosing
    ; ep4ReceiptIsCanonical = refl
    ; receiptText = canonicalReceiptText
    ; receiptTextIsCanonical = refl
    ; statementText = canonicalStatementText
    ; statementTextIsCanonical = refl
    ; boundaryText = canonicalBoundaryText
    ; boundaryTextIsCanonical = refl
    ; arithmeticKernelText = canonicalArithmeticKernelText
    ; arithmeticKernelTextIsCanonical = refl
    ; zeroCaseKernelText = canonicalZeroCaseKernelText
    ; zeroCaseKernelTextIsCanonical = refl
    ; obligations = canonicalOutsideSeamAbsorptionObligations
    ; obligationsAreCanonical = refl
    ; seamLocalOutsideSeamZeroModelCarried = true
    ; seamLocalOutsideSeamZeroModelCarriedIsTrue = refl
    ; outsideSeamAbsorptionKernelInstalled = true
    ; outsideSeamAbsorptionKernelInstalledIsTrue = refl
    ; outsideSeamZeroCaseKernelInstalled = true
    ; outsideSeamZeroCaseKernelInstalledIsTrue = refl
    ; outsideSeamNoPollutionAnalyticallyProved = true
    ; outsideSeamNoPollutionAnalyticallyProvedIsTrue = refl
    ; theoremPromoted = false
    ; theoremPromotedIsFalse = refl
    }
