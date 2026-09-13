module DASHI.Physics.Closure.NSTriadKNModernNestedSchurToCommutatorBidiRound577Exact where

------------------------------------------------------------------------
-- ROUND577 / BIDI: HISTORICAL NESTED SCHUR RECEIPTS -> MODERN R568 CONSUMER
--
-- R328 already owns the finite row/column Schur compiler.  R329/R330/R334
-- identify the literal nested physical carrier and refine the two numerical
-- obligations to the weighted row-shell and numerical column-envelope budgets.
-- R568, much later, freezes the modern direct leaf-A analytic consumer as
--
--   4 * integral(globalForcingFull) <= cutoffIndependentBound.
--
-- The dangerous shortcut is to identify these merely because both are called
-- "Schur/commutator" bounds.  R328 returns a NONNEGATIVE squared majorant;
-- R568 asks for a SIGNED spacetime upper bound.  Therefore the bridge has four
-- independent receipts:
--
--   1. literal nested row receipt;
--   2. literal nested column receipt on the same weighted input;
--   3. signed modern R568 response <= the exact R328 Schur output mass;
--   4. the resulting Schur envelope is cutoff-uniform in time.
--
-- Given those receipts this file constructs the EXISTING
-- CommutatorOnlySpacetimeBudget568.  It introduces no replacement leaf-A
-- consumer and no new analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNStrongLowNestedSchurMeetingRound328Exact as R328
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNStrongLowRowColumnFrontierRound334Exact as R334
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNDirectLeafACompilerRound572Exact as R572

F : C3.RealField _
F = Rational.rationalRealField

module Bidi577
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Comm = R568.LiveCommutatorOnly
    Time initialTime integrateTo DerivativeOf integration

  record ModernNestedSchurBridge577
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      -- These are the EXACT two receipts consumed by R328.
      row577 : (cutoff : Nat) (terminal : Time) → R328.StrongLowNestedRowReceipt
      column577 : (cutoff : Nat) (terminal : Time) → R328.StrongLowNestedColumnReceipt
      weightedInputAgrees577 :
        (cutoff : Nat) (terminal : Time) →
        R328.rowWeightedInput (row577 cutoff terminal)
        ≡ R328.rowWeightedInput (column577 cutoff terminal)

      -- R328's outputMass is a nonnegative/operator majorant.  This is the
      -- required BIDI receipt from the MODERN SIGNED R568 scalar into it.
      signedResponseBelowSchurOutput577 :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 * Comm.integratedGlobalForcingFull T R cutoff terminal
        ≤ R328.outputMass (row577 cutoff terminal)

      cutoffIndependentSchurBound577 : Time → ℚ

      -- Do not hide cutoff-uniformity inside the finite Schur compiler.
      schurEnvelopeUniform577 :
        (cutoff : Nat) (terminal : Time) →
        (R328.rowBudget (row577 cutoff terminal)
          * R328.columnBudget (column577 cutoff terminal))
          * R328.inputMass (column577 cutoff terminal)
        ≤ cutoffIndependentSchurBound577 terminal

  open ModernNestedSchurBridge577 public

  schurData577 :
    ∀ {T R} →
    (B : ModernNestedSchurBridge577 T R) →
    (cutoff : Nat) (terminal : Time) →
    R328.StrongLowNestedSchurData
  schurData577 B cutoff terminal =
    R328.strong-low-nested-schur-data
      (row577 B cutoff terminal)
      (column577 B cutoff terminal)
      (weightedInputAgrees577 B cutoff terminal)

  modernSignedResponseBelowUniformSchur577 :
    ∀ {T R} →
    (B : ModernNestedSchurBridge577 T R) →
    (cutoff : Nat) (terminal : Time) →
    R567.four567 * Comm.integratedGlobalForcingFull T R cutoff terminal
    ≤ cutoffIndependentSchurBound577 B terminal
  modernSignedResponseBelowUniformSchur577 B cutoff terminal =
    let
      D = schurData577 B cutoff terminal
      signedToOutput = signedResponseBelowSchurOutput577 B cutoff terminal
      outputToSchur = R328.strongLowNestedSchurSquaredBound D
      schurToUniform = schurEnvelopeUniform577 B cutoff terminal
    in
    ℚP.≤-trans signedToOutput (ℚP.≤-trans outputToSchur schurToUniform)

  nestedSchurBuildsModernCommutatorBudget577 :
    ∀ {T R} →
    ModernNestedSchurBridge577 T R →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  nestedSchurBuildsModernCommutatorBudget577 B = record
    { Comm.cutoffIndependentCommutatorBound568 = cutoffIndependentSchurBound577 B
    ; Comm.liveCommutatorOnlyBudget568 =
        modernSignedResponseBelowUniformSchur577 B
    }

------------------------------------------------------------------------
-- Proof-search/frontier reconciliation.
------------------------------------------------------------------------

round577R328FiniteSchurCompilerReused : Bool
round577R328FiniteSchurCompilerReused = true

round577R329LiteralNestedPhysicalCarrierReused : Bool
round577R329LiteralNestedPhysicalCarrierReused =
  R329.round329LiteralNestedPhysicalCarrierClosed

round577R334RowEnumerationAndColumnGeometryReused : Bool
round577R334RowEnumerationAndColumnGeometryReused = true

round577RowReceiptClosed : Bool
round577RowReceiptClosed = R334.round334WeightedRowShellBudgetClosed

round577ColumnReceiptClosed : Bool
round577ColumnReceiptClosed = R334.round334NumericalColumnEnvelopeBudgetClosed

round577SignedResponseMajorizationClosed : Bool
round577SignedResponseMajorizationClosed = false

round577CutoffUniformSchurEnvelopeClosed : Bool
round577CutoffUniformSchurEnvelopeClosed = false

round577ModernR568CompilerClosedGivenReceipts : Bool
round577ModernR568CompilerClosedGivenReceipts = true

round577IntroducesParallelLeafAConsumer : Bool
round577IntroducesParallelLeafAConsumer = false

round577DirectLeafACompilerAlreadyOwned : Bool
round577DirectLeafACompilerAlreadyOwned = R572.round572R503DirectBudgetCompilerClosedGivenReceipts

round577ClayPromotion : Bool
round577ClayPromotion = false

round577ModernR568CompilerClosedGivenReceiptsIsTrue :
  round577ModernR568CompilerClosedGivenReceipts ≡ true
round577ModernR568CompilerClosedGivenReceiptsIsTrue = refl

round577ClayPromotionIsFalse : round577ClayPromotion ≡ false
round577ClayPromotionIsFalse = refl
