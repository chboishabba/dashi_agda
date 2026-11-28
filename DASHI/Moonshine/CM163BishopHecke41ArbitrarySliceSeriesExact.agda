module DASHI.Moonshine.CM163BishopHecke41ArbitrarySliceSeriesExact where

-- SOURCE-WRITTEN, kernel pending. General real specialization of the original normalized correspondence.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin as Fin using (Fin; toℕ)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (sym)
import Real as R
import RealProperties as P
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.CM163BishopHecke41ActualSeriesEvaluationExact as Prior
import DASHI.Moonshine.CM163BishopHecke41ReducedNormFlowExact as Reduced
import DASHI.Moonshine.CM163BishopHecke41CuspResidualExact as Res
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as Bound
open import Data.Nat.Base using (_≤_)
open import Data.List.Base using (List)
open import Data.Rational.Unnormalised using (ℚᵘ)
open R using (_⋆)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopRamanujanComplexReadoutExact as Read
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Shift
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41NormalizedProductExact as Actual
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Coeff
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _-C_; powC)
open Comp using (complexTrans; complexSym)

-- h_Y and g_Y are the SAME original streams with only the
-- specialization parameter varied; their unit mode is unchanged.
hY gY : R.ℝ → G.Series
hY y = G._⊖s_ D.Junit (Coeff.delay 1 (G.constant y))
gY y = G._⊖s_ (Coeff.expand (Coeff.expand D.Junit)) (Coeff.delay 1681 (G.constant y))

hY0 : ∀ y → R._≃_ (hY y zero) R.1ℝ
hY0 y = P.≃-trans (P.+-cong D.Junit0 P.≃-refl) (P.+-identityʳ R.1ℝ)

module At (inputs : Round11.BishopCutset) where
  module V = Prior.At inputs
  module A0 = V.A0
  module Rm = V.Rm
  module Norm = V.Norm
  module Red = Reduced.At inputs
  module P0 = Poly.At inputs
  open A0 using (q; t; junit; Jvalue)
  open V using (normRead; normValue; qqRead)

  module For (y : R.ℝ) where
    Y = C.complex y R.0ℝ
    h = hY y
    g = gY y
    module Flow = Red.For h (hY0 y)

    series = N._⊗c_ (E.lift g) (Norm.norm (E.lift h))

    sH : ∀ p k → Read.Readout (q (Chart.finitePoint k p)) h
    sH p k = Read.subtract (junit (Chart.finitePoint k p))
      (Eval.delayRead 1 (Read.constantRead _ y))

    sFactor : ∀ p k → BishopComplex
    sFactor p k = Jvalue (Chart.finitePoint k p) -C (q (Chart.finitePoint k p) *C Y)

    sHValue : ∀ p k → Read.value (sH p k) ≈C sFactor p k
    sHValue p k = A.subCCongruent (C.≈C-refl _)
      (complexTrans (Eval.delayValue 1 (Read.constantRead _ y))
        (A.mulCCongruent (Power.powOne _) (C.≈C-refl Y)))

    sRead : ∀ p k → Eval.Eval (t p) (Norm.factor (E.lift h) k)
    sRead p k = Eval.phase (Rm.finiteQ k p) (Eval.fromReal (sH p k))

    sliceNorm : ∀ p → Eval.Eval (t p) (Norm.norm (E.lift h))
    sliceNorm p = normRead (t p) (E.lift h) (sRead p) zero 41

    sliceNormValue : ∀ p → Eval.value (sliceNorm p) ≈C Prod.product (A0.sFinite p Y)
    sliceNormValue p = normValue (t p) (E.lift h) (sRead p) (sFactor p) (sHValue p) zero 41

    sG : ∀ p → Read.Readout (t p) g
    sG p = Read.subtract (qqRead p) (Eval.delayRead 1681 (Read.constantRead _ y))

    sGValue : ∀ p → Read.value (sG p) ≈C A0.sInfinity p Y
    sGValue p = A.subCCongruent (C.≈C-refl _)
      (complexTrans (Eval.delayValue 1681 (Read.constantRead _ y))
        (A.mulCCongruent
          (complexTrans (complexSym (Ram.powPow (t p) 41 41))
            (complexTrans (A.powCCongruent (Rm.tPower p) 41) (complexSym (Rm.infinityQ p))))
          (C.≈C-refl Y)))

    slice : ∀ p → Eval.Eval (t p) (Norm.norm (E.lift h))alized
    slice p = Eval.product (Eval.fromReal (sG p)) (sliceNorm p)

    sliceValue : ∀ p → Eval.value (slice p) ≈C A0.sliceNormalized p Y
    sliceValue p = complexTrans (A.mulCCongruent (sGValue p) (sliceNormValue p))
      (L.complexMultiplyCommutative _ _)

    -- The convergent series now denotes the actual normalized analytic
    -- product. No equality with the integer polynomial is claimed here.
    actualSlice : ∀ p →
      (powC (t p) 1722 *C A0.G.product p Y) ≈C Eval.value (slice p)
    actualSlice p = complexTrans (A0.sliceT p Y) (complexSym (sliceValue p))

    -- Residual for an arbitrary degree-42 descending integer column.
    -- The next gate is precisely a finite prefix of this SAME stream.
    residual : List ℚᵘ → N.SeriesC
    residual cs n = series n -C E.lift (Coeff.column cs) n

    evaluateResidual : ∀ p cs → Eval.Eval (t p) (residual cs)
    evaluateResidual p cs = Res.subtract (slice p) (Eval.fromReal (P0.columnRead p cs))

    -- No all-point analytic equality follows just from this prefix.
    tailFactor : ∀ p cs → (∀ n → n ≤ 1722 → residual cs n ≈C A.zeroC) →
      Eval.value (evaluateResidual p cs) ≈C
      (powC (t p) 1723 *C Eval.value (Tail.tailRead (Rm.tNZ p) 1723 (evaluateResidual p cs)))
    tailFactor p cs gate = Tail.factor (Rm.tNZ p) 1722 (evaluateResidual p cs) gate
