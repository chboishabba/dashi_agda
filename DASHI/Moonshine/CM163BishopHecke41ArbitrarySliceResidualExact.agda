module DASHI.Moonshine.CM163BishopHecke41ArbitrarySliceResidualExact where

-- SOURCE-WRITTEN, kernel pending. Generalize the existing literal
-- fixed-slice pole removal to the original arbitrary real target Y.
-- Reuses actual cyclic norm, degree-42 column and S/T invariance.
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.List.Base using (List)
open import Data.Rational.Unnormalised using (ℚᵘ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)
import Real as R
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopRamanujanComplexReadoutExact as Read
import DASHI.Moonshine.CM163BishopHecke41ArbitrarySliceSeriesExact as Arbitrary
import DASHI.Moonshine.CM163BishopHecke41CuspResidualExact as Residual
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41SectorFilterExact as Filter
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)

module At (inputs : Round11.BishopCutset) where
  module A0 = Arbitrary.At inputs
  module R0 = Residual.At inputs
  module G = A0.A0.G
  open A0.A0 using (q; t)

  module For (y : R.ℝ) (cs : List ℚᵘ) (degree : Poly.degree cs ≡ 42) where
    module Y = A0.For y

    residual p = G.product p Y.Y -C Poly.poly (G.j p) cs

    columnT : ∀ p → (powC (t p) 1722 *C Poly.poly (G.j p) cs) ≈C
      Read.value (A0.P0.columnRead p cs)
    columnT p = complexTrans (A.mulCCongruent
      (complexTrans (complexSym (Ram.powPow (t p) 41 42))
        (complexTrans (A.powCCongruent (A0.Rm.tPower p) 42)
          (Filter.powIndex (q p) (sym degree)))) (C.≈C-refl _))
      (A0.P0.columnQ p cs)

    clear : ∀ p → (powC (t p) 1722 *C residual p) ≈C Eval.value (Y.evaluateResidual p cs)
    clear p = complexTrans (Alg.mulSub (powC (t p) 1722) _ _)
      (A.subCCongruent (Y.actualSlice p) (columnT p))

    tail p = Tail.tailRead (A0.Rm.tNZ p) 1723 (Y.evaluateResidual p cs)

    PrefixGate : Set
    PrefixGate = ∀ n → n ≤ 1722 → Y.residual cs n ≈C A.zeroC

    poleRemoved : PrefixGate → ∀ p → residual p ≈C (t p *C Eval.value (tail p))
    poleRemoved gate p = R0.cancelPole p 1722 _ _
      (complexTrans (clear p) (Y.tailFactor p cs gate))

    invariantS : ∀ p → residual (Gen.actS p) ≈C residual p
    invariantS p = A.subCCongruent (G.productS p Y.Y) (Poly.polyCong (R0.jS p) cs)

    invariantT : ∀ p → residual (Gen.actT p) ≈C residual p
    invariantT p = A.subCCongruent (G.productT p Y.Y) (Poly.polyCong (R0.jT p) cs)
