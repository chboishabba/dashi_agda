module DASHI.Moonshine.CM163BishopHecke41ActualSeriesEvaluationExact where

-- SOURCE-WRITTEN, kernel pending. Evaluate the original formal
-- normalized products on the actual ramified phase. All 41 factors
-- use their original chart J readout, not an arbitrary root stream.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin as Fin using (Fin; toℕ)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (sym)
import Real as R
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

module At (inputs : Round11.BishopCutset) where
  module A0 = Actual.At inputs
  module Rm = Ram.At inputs
  module Norm = N.At inputs
  module O = Coeff.At inputs
  open A0 using (q; t; junit; Jvalue)

  K : BishopComplex
  K = C.complex (Shift.Kq ⋆) R.0ℝ

  dH : ∀ p k → Read.Readout (q (Chart.finitePoint k p)) Coeff.hDiag
  dH p k =
    Read.subtract (Eval.expandRead (Rm.finitePower k p) (junit p))
      (Eval.delayRead 40 (junit (Chart.finitePoint k p)))

  sH : ∀ p k → Read.Readout (q (Chart.finitePoint k p)) Coeff.hSlice
  sH p k = Read.subtract (junit (Chart.finitePoint k p))
    (Eval.delayRead 1 (Read.constantRead _ (Shift.Kq ⋆)))

  dFactor : ∀ p k → BishopComplex
  dFactor p k = Jvalue p -C
    (powC (q (Chart.finitePoint k p)) 40 *C Jvalue (Chart.finitePoint k p))

  sFactor : ∀ p k → BishopComplex
  sFactor p k = Jvalue (Chart.finitePoint k p) -C (q (Chart.finitePoint k p) *C K)

  dHValue : ∀ p k → Read.value (dH p k) ≈C dFactor p k
  dHValue p k = A.subCCongruent (C.≈C-refl _)
    (Eval.delayValue 40 (junit (Chart.finitePoint k p)))

  sHValue : ∀ p k → Read.value (sH p k) ≈C sFactor p k
  sHValue p k = A.subCCongruent (C.≈C-refl _)
    (complexTrans (Eval.delayValue 1 (Read.constantRead _ (Shift.Kq ⋆)))
      (A.mulCCongruent (Power.powOne _) (C.≈C-refl K)))

  dRead : ∀ p k → Eval.Eval (t p) (Norm.factor (E.lift Coeff.hDiag) k)
  dRead p k = Eval.phase (Rm.finiteQ k p) (Eval.fromReal (dH p k))

  sRead : ∀ p k → Eval.Eval (t p) (Norm.factor (E.lift Coeff.hSlice) k)
  sRead p k = Eval.phase (Rm.finiteQ k p) (Eval.fromReal (sH p k))

  normRead : ∀ t0 f → (∀ k → Eval.Eval t0 (Norm.factor f k)) →
    ∀ k n → Eval.Eval t0 (Norm.normFrom f k n)
  normRead t0 f ev k zero = Eval.unit t0
  normRead t0 f ev k (suc n) = Eval.product (ev k) (normRead t0 f ev (suc k) n)

  normValue : ∀ t0 f (ev : ∀ k → Eval.Eval t0 (Norm.factor f k)) (v : Nat → BishopComplex) →
    (∀ k → Eval.value (ev k) ≈C v k) → ∀ k n →
    Eval.value (normRead t0 f ev k n) ≈C Prod.product {n} (λ i → v (k + toℕ i))
  normValue t0 f ev v hv k zero = C.≈C-refl _
  normValue t0 f ev v hv k (suc n) =
    A.mulCCongruent
      (complexTrans (hv k) (Actual.eqValue v (sym (NP.+-identityʳ k))))
      (complexTrans (normValue t0 f ev v hv (suc k) n)
        (Prod.productCong _ _ (λ i → Actual.eqValue v (sym (NP.+-suc k (toℕ i))))))

  diagNorm : ∀ p → Eval.Eval (t p) O.diagNorm
  diagNorm p = normRead (t p) (E.lift Coeff.hDiag) (dRead p) zero 41

  sliceNorm : ∀ p → Eval.Eval (t p) O.sliceNorm
  sliceNorm p = normRead (t p) (E.lift Coeff.hSlice) (sRead p) zero 41

  diagNormValue : ∀ p → Eval.value (diagNorm p) ≈C Prod.product (A0.dFinite p)
  diagNormValue p = normValue (t p) (E.lift Coeff.hDiag) (dRead p) (dFactor p) (dHValue p) zero 41

  sliceNormValue : ∀ p → Eval.value (sliceNorm p) ≈C Prod.product (A0.sFinite p K)
  sliceNormValue p = normValue (t p) (E.lift Coeff.hSlice) (sRead p) (sFactor p) (sHValue p) zero 41

  qtRead : ∀ p → Read.Readout (t p) (Coeff.expand D.Junit)
  qtRead p = Eval.expandRead (Rm.tPower p) (junit p)

  qqRead : ∀ p → Read.Readout (t p) (Coeff.expand (Coeff.expand D.Junit))
  qqRead p = Eval.expandRead (Rm.tPower p)
    (Eval.expandRead (complexSym (Rm.infinityQ p)) (junit (Chart.infinityPoint p)))

  dG : ∀ p → Read.Readout (t p) Coeff.gDiag
  dG p = Read.subtract (Eval.delayRead 1640 (qtRead p)) (qqRead p)

  sG : ∀ p → Read.Readout (t p) Coeff.gSlice
  sG p = Read.subtract (qqRead p) (Eval.delayRead 1681 (Read.constantRead _ (Shift.Kq ⋆)))

  dGValue : ∀ p → Read.value (dG p) ≈C A0.dInfinity p
  dGValue p = A.subCCongruent
    (complexTrans (Eval.delayValue 1640 (qtRead p))
      (A.mulCCongruent
        (complexTrans (complexSym (Ram.powPow (t p) 41 40)) (A.powCCongruent (Rm.tPower p) 40))
        (C.≈C-refl _))) (C.≈C-refl _)

  sGValue : ∀ p → Read.value (sG p) ≈C A0.sInfinity p K
  sGValue p = A.subCCongruent (C.≈C-refl _)
    (complexTrans (Eval.delayValue 1681 (Read.constantRead _ (Shift.Kq ⋆)))
      (A.mulCCongruent
        (complexTrans (complexSym (Ram.powPow (t p) 41 41))
          (complexTrans (A.powCCongruent (Rm.tPower p) 41) (complexSym (Rm.infinityQ p))))
        (C.≈C-refl K)))

  diagonal : ∀ p → Eval.Eval (t p) O.diagonalNormalized
  diagonal p = Eval.product (Eval.fromReal (dG p)) (diagNorm p)

  slice : ∀ p → Eval.Eval (t p) O.sliceNormalized
  slice p = Eval.product (Eval.fromReal (sG p)) (sliceNorm p)

  diagonalValue : ∀ p → Eval.value (diagonal p) ≈C A0.diagonalNormalized p
  diagonalValue p = complexTrans (A.mulCCongruent (dGValue p) (diagNormValue p))
    (L.complexMultiplyCommutative _ _)

  sliceValue : ∀ p → Eval.value (slice p) ≈C A0.sliceNormalized p K
  sliceValue p = complexTrans (A.mulCCongruent (sGValue p) (sliceNormValue p))
    (L.complexMultiplyCommutative _ _)

  -- The convergent series now denotes the actual normalized analytic
  -- product. No equality with the integer polynomial is claimed here.
  actualDiagonal : ∀ p →
    (powC (t p) 3362 *C A0.G.diagonal p) ≈C Eval.value (diagonal p)
  actualDiagonal p = complexTrans (A0.diagonalT p) (complexSym (diagonalValue p))

  actualSlice : ∀ p →
    (powC (t p) 1722 *C A0.G.product p K) ≈C Eval.value (slice p)
  actualSlice p = complexTrans (A0.sliceT p K) (complexSym (sliceValue p))
