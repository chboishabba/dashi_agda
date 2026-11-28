module DASHI.Moonshine.CM163BishopHecke41NodeMatrixDifferenceExact where

-- Paper 9 G3 exact finite-data bridge, SOURCE-WRITTEN KERNEL PENDING.
-- Read back ALL 43 genuine Hecke-product minus original-matrix
-- samples into the finite-difference certificate triangle. This is
-- intentionally not an assumption that 43 samples imply a global
-- analytic identity: first prove both functions are degree<=42 in Y.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.CM163BishopHecke41AllIntegerNodesExact as Nodes
import DASHI.Moonshine.CM163BishopHecke41NodeDifferenceExact as Diff
import DASHI.Moonshine.CM163BishopHecke41MatrixSymmetryExact as Mat
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as Jet
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_-C_)
open Comp using (complexTrans)

module At (inputs : Round11.BishopCutset) where
  module N = Nodes.At inputs
  module M = Mat.At inputs

  difference : ∀ p → Nat → BishopComplex
  difference p n = M.H.G.product p (Poly.realC (I.embed (Nodes.node n))) -C
    Mat.matrix Nodes.candidate (M.H.G.j p) (Poly.realC (I.embed (Nodes.node n)))

  nodeDifferenceZero : N.NodeZero → ∀ n → n ≤ 42 → ∀ p →
    difference p n ≈C A.zeroC
  nodeDifferenceZero zeros n hn p =
    complexTrans (A.subCCongruent (N.nodeIdentity zeros n hn p) (C.≈C-refl _))
      (Jet.sameSub _)

  samples p : Diff.Row 43
  samples p = Diff.tabulate 43 (difference p)

  sampleZero : N.NodeZero → ∀ p → Diff.zeroRow (samples p)
  sampleZero zeros p = Diff.tabulateZero 43 (difference p)
    (λ n hn → nodeDifferenceZero zeros n (NP.≤-pred hn) p)

  -- Forty-three difference orders, each derived from the SAME
  -- original Hecke product and the SAME integer candidate matrix.
  certificate p : Diff.Row 43
  certificate p = Diff.triangle (samples p)

  certificateZero : N.NodeZero → ∀ p →
    Diff.zeroRow (certificate p)
  certificateZero zeros p = Diff.triangleZero (samples p) (sampleZero zeros p)

-- Remaining G3 theorem, not silently assumed here:
-- prove that both full Y evaluations are of degree <=42 and that
-- zero finite-difference coefficients imply equality for all real Y,
-- using Newton's interpolation identity over the Bishop-complex
-- carrier. Then this certificate composes with MatrixSymmetry.FullIdentity.
