module DASHI.Moonshine.CM163BishopHecke41GlobalMatrixRigidityExact where

-- SOURCE-WRITTEN / KERNEL PENDING. Same constructive rigidity
-- for all 43 integer nodes, then existing exact polynomial
-- unisolvence and matrix transposition. No new analytic premise.
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Integer.Base using (ℤ)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.CM163BishopHecke41ActualOrbitCoverExact as Cover
import DASHI.Moonshine.CM163BishopHecke41UnramifiedResidualExact as Desc
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41LiteralResidualReflectionExact as Lit
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Coeff
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41IntegerSpecializationReflectionExact as Reflect
import DASHI.Moonshine.CM163BishopHecke41IntegerSpecializationExact as Special
import DASHI.Moonshine.CM163BishopHecke41AllIntegerNodesExact as Nodes
import DASHI.Moonshine.CM163BishopHecke41FullIdentityFromNodesExact as Full
import DASHI.Moonshine.CM163BishopHecke41MatrixSymmetryExact as Mat
import DASHI.Moonshine.CM163Hecke41FullIntegerMatrixExact as Matrix
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (_≈C_)
open Comp using (complexTrans; complexSym)

module At (inputs : Round11.BishopCutset) where
  module O = Cover.At inputs
  module N = Nodes.At inputs
  module F0 = Full.At inputs
  module M = Mat.At inputs
  module D = Desc.At inputs

  module For (c : Mat.Coefficient) (y : ℤ) where
    module F = N.R.For c y
    module Y = F.Y
    module S = F.S.S

    -- The actual g_Y and cyclic norm are both stride-41 sector
    -- supported in every degree, not only in the certified prefix.
    sector : R41.SectorC (Y.residual F.cs)
    sector = Desc.subSector Y.series (E.lift (Coeff.column F.cs))
      (Lit.complexSectorProduct (E.lift Y.g) (F.B.A.raw)
        (Lit.liftSector Y.g (Reflect.gSector y)) F.B.A.sectorNorm)
      (Lit.liftSector (Coeff.column F.cs) (Lit.columnSector F.cs))

    evaluation p = Desc.contractEval (N.R.A0.Rm.tPower p) sector
      (Y.evaluateResidual p F.cs)

    series (hu : N.R.L.W.UnitGate) (hg : F.Gate) p =
      Desc.Remove.result 41 (O.q p) (S.residual p) (O.nz p)
        (R41.restrictC (Y.residual F.cs)) (evaluation p)
        (complexTrans (A.mulCCongruent (D.powerRead p 42) (C.≈C-refl _)) (S.clear p))
        (λ n hn → F.zeroPrefix hu hg (R41.stride n) (Desc.strideMono hn))

    module Close (hu : N.R.L.W.UnitGate) (hg : F.Gate) where
      referenceSeries = series hu hg Cover.reference
      module End = O.R0.For Cover.reference O.cover
        (Tail.drop 42 (R41.restrictC (Y.residual F.cs)))
        (Desc.ZeroConstantSeries.zeroConstant referenceSeries)
        (λ p → Desc.ZeroConstantSeries.evaluated (series hu hg p))
        S.residual (λ p → Desc.ZeroConstantSeries.actual (series hu hg p))
        S.invariantS S.invariantT

      zeroResidual : ∀ p → S.residual p ≈C A.zeroC
      zeroResidual = End.zeroEverywhere

      identity : ∀ p → N.R.A0.A0.G.product p (Y.Y) ≈C
        Mat.matrix c (N.R.A0.A0.G.j p) Y.Y
      identity p = F.S.actualIdentity p (zeroResidual p)

  nodeZero : N.R.L.W.UnitGate → N.NodeGates → N.NodeZero
  nodeZero hu gates n hn = For.Close.zeroResidual Nodes.candidate (Nodes.node n)
    hu (N.nodeAt gates n hn)

  fullComplex hu gates = F0.fullComplex (nodeZero hu gates)

  fullIdentity : N.R.L.W.UnitGate → N.NodeGates → M.FullIdentity Nodes.candidate
  fullIdentity hu gates = F0.fullIdentity (nodeZero hu gates)

  twoPointSymmetry : N.R.L.W.UnitGate → N.NodeGates →
    Matrix.SymmetryGate Nodes.candidate → M.TwoPointSymmetry
  twoPointSymmetry hu gates sym p q =
    complexTrans (fullComplex hu gates p (M.H.G.j q))
      (complexTrans (Mat.symmetric Nodes.candidate (Mat.fromSymmetryGate Nodes.candidate sym)
        (M.H.G.j p) (M.H.G.j q))
        (complexSym (fullComplex hu gates q (M.H.G.j p))))
