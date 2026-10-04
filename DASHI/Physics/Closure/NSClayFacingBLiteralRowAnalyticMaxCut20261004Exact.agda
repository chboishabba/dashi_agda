module DASHI.Physics.Closure.NSClayFacingBLiteralRowAnalyticMaxCut20261004Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / FINAL LITERAL-ROW ANALYTIC INTERFACE FOR B1--B4
--
-- All representation and receipt-construction layers can now be kept behind
-- the proof producers.  The downstream positive-B theorem needs exactly four
-- uniform estimates on the SAME literal row carriers extracted from the live
-- R236 pair graph:
--
--   B1: sum(DFL--DFL literal rows) <= c1 * ED_k
--   B2: sum(DFL--DHH literal rows) <= c2 * ED_k
--   B3: sum(DHH--DHH literal rows) <= c3 * ED_k
--   B4: sum(critical-touching literal rows)
--          <= theta * M_core(k) + c4 * ED_k,   0 <= theta < 1.
--
-- Exact same-object theorems compile these four row inequalities to the live
-- scalar blocks.  NSClayFacingBLocalEDCompilerMaxCut20261004Exact then sums the
-- common local-ED currency algebraically with C = c1+c2+c3+c4 and constructs
-- the existing uniform physical critical-region family.
--
-- Hence neither shell-receipt records nor B_localED are independent theorem
-- leaves at the final B interface.  Shell/Bernstein/null/L2 arguments remain
-- valid internal proof strategies for the four displayed inequalities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as DeepRows
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralRowsMaxCutExact as CriticalRows
import DASHI.Physics.Closure.NSClayFacingBLocalEDCompilerMaxCut20261004Exact as LocalED

F : C3.RealField _
F = Rational.rationalRealField

module LiteralRowAnalytic
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (theta c1 c2 c3 c4 : ℚ)
    (select : Z3.FourierMode → Z3.FourierMode → Bool) where

  module L = LocalED.Compile physicalSystem S theta c1 c2 c3 c4 select

  localED : Z3.FourierMode → ℚ
  localED = L.localED

  record LiteralRowAnalyticLeaves : Set₁ where
    constructor literal-row-analytic-leaves
    field
      coreCompanionMass : Z3.FourierMode → ℚ

      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1ℚ
      c1NN : 0ℚ ≤ c1
      c2NN : 0ℚ ≤ c2
      c3NN : 0ℚ ≤ c3
      c4NN : 0ℚ ≤ c4
      viscosityNN : 0ℚ ≤ Field30.viscosity physicalSystem

      b1LiteralRowsBound :
        (output : Z3.FourierMode) →
        let module E = DeepRows.LiveExtraction physicalSystem S output
        in
        DeepRows.sumRows E.Rate.inputMass (E.Live.work output) E.b1Rows
        ≤ c1 * localED output

      b2LiteralRowsBound :
        (output : Z3.FourierMode) →
        let module E = DeepRows.LiveExtraction physicalSystem S output
        in
        DeepRows.sumRows E.Rate.inputMass (E.Live.work output) E.b2Rows
        ≤ c2 * localED output

      b3LiteralRowsBound :
        (output : Z3.FourierMode) →
        let module E = DeepRows.LiveExtraction physicalSystem S output
        in
        DeepRows.sumRows E.Rate.inputMass (E.Live.work output) E.b3Rows
        ≤ c3 * localED output

      b4LiteralRowsBound :
        (output : Z3.FourierMode) →
        let module E = CriticalRows.LiveCriticalRows physicalSystem S output
        in
        E.rowSum
        ≤ theta * coreCompanionMass output + c4 * localED output

  open LiteralRowAnalyticLeaves public

  toCommonLocalEDAnalyticLeaves :
    LiteralRowAnalyticLeaves → L.CommonLocalEDAnalyticLeaves
  toCommonLocalEDAnalyticLeaves A = record
    { L.coreCompanionMass = coreCompanionMass A
    ; L.thetaNN = thetaNN A
    ; L.thetaStrictlyBelowOne = thetaStrictlyBelowOne A
    ; L.c1NN = c1NN A
    ; L.c2NN = c2NN A
    ; L.c3NN = c3NN A
    ; L.c4NN = c4NN A
    ; L.viscosityNN = viscosityNN A
    ; L.b1PaidBySameLocalED = λ output →
        let module E = DeepRows.LiveExtraction physicalSystem S output
        in
        subst
          (λ lower → lower ≤ c1 * localED output)
          (sym E.b1LiveBlockIsLiteralRows)
          (b1LiteralRowsBound A output)
    ; L.b2PaidBySameLocalED = λ output →
        let module E = DeepRows.LiveExtraction physicalSystem S output
        in
        subst
          (λ lower → lower ≤ c2 * localED output)
          (sym E.b2LiveBlockIsLiteralRows)
          (b2LiteralRowsBound A output)
    ; L.b3PaidBySameLocalED = λ output →
        let module E = DeepRows.LiveExtraction physicalSystem S output
        in
        subst
          (λ lower → lower ≤ c3 * localED output)
          (sym E.b3LiveBlockIsLiteralRows)
          (b3LiteralRowsBound A output)
    ; L.b4PaidBySameLocalED = λ output →
        let module E = CriticalRows.LiveCriticalRows physicalSystem S output
        in
        subst
          (λ lower →
            lower ≤ theta * coreCompanionMass A output + c4 * localED output)
          (sym E.liveCriticalTouchingIsLiteralRows)
          (b4LiteralRowsBound A output)
    }

  literalRowsBuildPhysicalFamily :
    LiteralRowAnalyticLeaves → L.D.U.U.UniformPhysicalCriticalRegionFamily
  literalRowsBuildPhysicalFamily A =
    L.commonLocalEDLeavesBuildPhysicalFamily
      (toCommonLocalEDAnalyticLeaves A)

------------------------------------------------------------------------
-- Status / exact frontier.
------------------------------------------------------------------------

bLiteralRowAnalyticCompilerClosed : Bool
bLiteralRowAnalyticCompilerClosed = true

bLegacyReceiptFrontierStillRequired : Bool
bLegacyReceiptFrontierStillRequired = false

bLocalEDIndependentLeafRemaining : Bool
bLocalEDIndependentLeafRemaining = false

bLiteralRowAnalyticEstimatesClosedHere : Bool
bLiteralRowAnalyticEstimatesClosedHere = false

clayPromotion : Bool
clayPromotion = false

bLiteralRowAnalyticCompilerClosedIsTrue :
  bLiteralRowAnalyticCompilerClosed ≡ true
bLiteralRowAnalyticCompilerClosedIsTrue = refl

bLegacyReceiptFrontierStillRequiredIsFalse :
  bLegacyReceiptFrontierStillRequired ≡ false
bLegacyReceiptFrontierStillRequiredIsFalse = refl

bLocalEDIndependentLeafRemainingIsFalse :
  bLocalEDIndependentLeafRemaining ≡ false
bLocalEDIndependentLeafRemainingIsFalse = refl

bLiteralRowAnalyticEstimatesClosedHereIsFalse :
  bLiteralRowAnalyticEstimatesClosedHere ≡ false
bLiteralRowAnalyticEstimatesClosedHereIsFalse = refl
