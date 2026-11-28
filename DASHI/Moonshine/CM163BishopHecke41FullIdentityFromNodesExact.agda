module DASHI.Moonshine.CM163BishopHecke41FullIdentityFromNodesExact where

-- G3: actual degree-42 polynomial uniqueness, not a new axiom.
-- Source-written, kernel pending. The remaining inputs are the
-- original analytic NodeZero proofs. Integer apartness is constructed.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base as Fin using (Fin; toℕ)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
import Data.Fin.Properties as FP
import Data.Nat.Properties as NP
import Real as R
import RealProperties as RP
import DASHI.Foundations.BishopNatRealPositiveExact as Pos
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as ApartC
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
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

-- Offset enumeration is recursive on Fin, so removing the first
-- root definitionally gives the next consecutive block.
offset : ∀ {n} → Nat → Fin n → Nat
offset k Fin.zero = k
offset k (Fin.suc i) = offset (suc k) i

offsetRead : ∀ {n} k (i : Fin n) → offset k i ≡ k + toℕ i
offsetRead k Fin.zero = sym (NP.+-identityʳ k)
offsetRead k (Fin.suc i) = trans (offsetRead (suc k) i)
  (sym (NP.+-suc k (toℕ i)))

shifted : ∀ {n} → Nat → Fin n → BishopComplex
shifted k i = Poly.realC (I.embed (+ (offset k i)))

-- The head-to-tail real difference is exactly the positive integer
-- successor, not an arbitrary complex-apartness axiom.
offsetApart : ∀ {n} k (i : Fin n) →
  Rec.BishopComplexNonzero (A._-C_ (shifted (suc k) i)
    (Poly.realC (I.embed (+ k))))
offsetApart k i =
  let h = suc (toℕ i)
      eq = trans (offsetRead (suc k) i) (sym (NP.+-suc k (toℕ i)))
      realRead = RP.≃-trans
        (RP.+-cong (I.embedCong (cong +_ eq)) RP.≃-refl)
        (RP.≃-trans (RP.+-cong (I.embedAdd (+ k) (+ h)) RP.≃-refl)
          (let open RP.ℝ-Solver in solve 2 (λ a b → (a ⊕ b) ⊖ a ⊜ b)
            RP.≃-refl (I.embed (+ k)) (I.embed (+ h))))
  in ApartC.complexNonzeroFromRealApart
    (ApartC.apartCongruent (RP.≃-symm realRead)
      (inj₂ (Pos.natRealSuccessorStrictlyPositive (toℕ i))))

apartFrom : ∀ n k → P.Apart (shifted {n} k)
apartFrom zero k = tt
apartFrom (suc n) k = (λ i → offsetApart k i) , apartFrom n (suc k)

integerNodes : Fin 43 → BishopComplex
integerNodes = shifted zero

integerApart : P.Apart integerNodes
integerApart = apartFrom 43 zero

integerNodeRead : ∀ i → offset zero i ≡ toℕ i
integerNodeRead i = offsetRead zero i

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
  nodeAtFin : N0.NodeZero → ∀ p (i : Fin 43) →
    M.H.G.product p (integerNodes i) ≈C Mat.matrix Nodes.candidate (M.H.G.j p) (integerNodes i)
  nodeAtFin zeros p i rewrite integerNodeRead i =
    N0.nodeIdentity zeros (toℕ i) (NP.≤-pred (FP.toℕ<n i)) p

  fullComplex : N0.NodeZero → ∀ p y →
    M.H.G.product p y ≈C Mat.matrix Nodes.candidate (M.H.G.j p) y
  fullComplex zeros p y =
    complexTrans (complexSym (actualProductRead p y))
      (complexTrans (P.unique (actualProductRow p)
        (matrixRow Nodes.candidate (M.H.G.j p)) integerNodes integerApart
        (λ i → complexTrans (actualProductRead p (integerNodes i))
          (complexTrans (nodeAtFin zeros p i)
            (matrixRead Nodes.candidate (M.H.G.j p) (integerNodes i)))) y)
        (complexSym (matrixRead Nodes.candidate (M.H.G.j p) y)))

  fullIdentity : N0.NodeZero →
    M.FullIdentity Nodes.candidate
  fullIdentity zeros p y = fullComplex zeros p (Poly.realC y)
