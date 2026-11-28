module DASHI.Moonshine.CM163BishopHecke41FullIdentityFromNodesExact where

-- G3: actual degree-42 polynomial uniqueness, not a new axiom.
-- Source-written, kernel pending. The remaining inputs are the
-- original analytic NodeZero proofs and concrete integer apartness.
open import Data.Fin.Base as Fin using (Fin; toℕ)
import Data.Fin.Properties as FP
import Data.Nat.Properties as NP
import Real as R
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.CM163BishopHecke41MatrixSymmetryExact as Mat
import DASHI.Moonshine.CM163BishopHecke41PolynomialUnisolvenceExact as P
import DASHI.Moonshine.CM163BishopHecke41NodeDifferenceExact as D
import DASHI.Moonshine.CM163BishopHecke41AllIntegerNodesExact as Nodes
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; powC)
open Comp using (complexTrans; complexSym)

-- The X-evaluation is retained in each of the 43 Y coefficients.
coefficient : Mat.Coefficient → BishopComplex → Fin 43 → BishopComplex
coefficient c x j = N.sumC (λ i →
  Poly.realC (I.embed (c (Mat.expo i) (Mat.expo j))) *C powC x (Mat.expo i))

matrixRow : Mat.Coefficient → BishopComplex → D.Row 43
matrixRow c x = P.descending (coefficient c x)

swapLast : ∀ a b c → ((a *C b) *C c) ≈C ((a *C c) *C b)
swapLast a b c = complexTrans (L.complexMultiplyAssociative a b c)
  (complexTrans (A.mulCCongruent (C.≈C-refl _) (L.complexMultiplyCommutative b c))
    (complexSym (L.complexMultiplyAssociative a c b)))

matrixRead : ∀ c x y → Mat.matrix c x y ≈C P.eval (matrixRow c x) y
matrixRead c x y =
  complexTrans (Mat.fubini (Mat.term c x y))
    (complexTrans (N.sumCong _ _ (λ j →
      complexTrans (N.sumCong _ _ (λ i → swapLast
        (Poly.realC (I.embed (c (Mat.expo i) (Mat.expo j))))
        (powC y (Mat.expo j)) (powC x (Mat.expo i))))
        (N.sumMul (λ i →
          Poly.realC (I.embed (c (Mat.expo i) (Mat.expo j))) *C powC x (Mat.expo i))
          (powC y (Mat.expo j)))))
      (complexSym (P.descendingRead (coefficient c x) y)))

integerNodes : Fin 43 → BishopComplex
integerNodes i = Poly.realC (I.embed (Nodes.node (toℕ i)))

module At (inputs : Round11.BishopCutset) where
  module M = Mat.At inputs
  module N0 = Nodes.At inputs

  actualProductRow : U.BishopUpperHalfPlanePoint → D.Row 43
  actualProductRow p = P.productRow (M.H.chart p)

  actualProductRead : ∀ p y →
    P.eval (actualProductRow p) y ≈C M.H.G.product p y
  actualProductRead p y = P.productRead (M.H.chart p) y

  -- No interpolation axiom: degree reduction in P.unique recursively
  -- removes one distinct root, using only exact complex cancellation.
  fullComplex : P.Apart integerNodes → N0.NodeZero → ∀ p y →
    M.H.G.product p y ≈C Mat.matrix Nodes.candidate (M.H.G.j p) y
  fullComplex apart zeros p y =
    complexTrans (complexSym (actualProductRead p y))
      (complexTrans (P.unique (actualProductRow p)
        (matrixRow Nodes.candidate (M.H.G.j p)) integerNodes apart
        (λ i → complexTrans (actualProductRead p (integerNodes i))
          (complexTrans (N0.nodeIdentity zeros (toℕ i) (NP.≤-pred (FP.toℕ<n i)) p)
            (matrixRead Nodes.candidate (M.H.G.j p) (integerNodes i)))) y)
        (complexSym (matrixRead Nodes.candidate (M.H.G.j p) y)))

  fullIdentity : P.Apart integerNodes → N0.NodeZero →
    M.FullIdentity Nodes.candidate
  fullIdentity apart zeros p y = fullComplex apart zeros p (Poly.realC y)
