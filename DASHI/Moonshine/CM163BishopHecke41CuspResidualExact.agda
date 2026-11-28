module DASHI.Moonshine.CM163BishopHecke41CuspResidualExact where

-- SOURCE-WRITTEN, kernel pending. The literal polynomial and actual
-- Hecke series live on the same coefficient stream. After checking
-- the integer prefix, remove precisely the pole power. No analytic
-- rigidity or uniform cusp bound is inferred from this factor alone.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_,_)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41LiteralResidualReflectionExact as Ref
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_-C_; _*C_; powC)
open N using (SeriesC; twist)
open Comp using (complexTrans; complexSym)

subtract : ∀ {t f g} → Eval.Eval t f → Eval.Eval t g →
  Eval.Eval t (λ n → f n -C g n)
subtract {t} {f} {g} a b =
  let x = twist t f; y = twist t g
      ab = C.componentwise-absolute-series-convergent
        (CP.minusAbs (C.realTerms x) (C.realTerms y) (C.realAbsolute (Eval.absolute a)) (C.realAbsolute (Eval.absolute b)))
        (CP.minusAbs (C.imagTerms x) (C.imagTerms y) (C.imagAbsolute (Eval.absolute a)) (C.imagAbsolute (Eval.absolute b)))
      cv = C.complex-series-converges-to
        (CP.minusConv (C.realConverges (Eval.converges a)) (C.realConverges (Eval.converges b)))
        (CP.minusConv (C.imagConverges (Eval.converges a)) (C.imagConverges (Eval.converges b)))
      eq : ∀ n → (x n -C y n) ≈C twist t (λ k → f k -C g k) n
      eq n = complexTrans (A.subCCongruent
        (L.complexMultiplyCommutative (f n) (powC t n))
        (L.complexMultiplyCommutative (g n) (powC t n)))
        (complexTrans (complexSym (Alg.mulSub (powC t n) (f n) (g n)))
          (L.complexMultiplyCommutative (powC t n) (f n -C g n)))
  in record { value = Eval.value a -C Eval.value b
    ; absolute = CP.complexAbsTransport eq ab
    ; converges = CP.complexLimitTransport eq cv }

module At (inputs : Round11.BishopCutset) where
  module P = Poly.At inputs
  module V = P.V
  module G = V.A0.G
  module R = Ref.At inputs
  open V using (t; K)

  d : ∀ p → BishopComplex
  d p = G.diagonal p -C Poly.poly (G.j p) Packet.diagonal

  s : ∀ p → BishopComplex
  s p = G.product p K -C Poly.poly (G.j p) Packet.slice

  dEval : ∀ p → Eval.Eval (t p) R.O.diagonalResidual
  dEval p = subtract (V.diagonal p) (P.diagonalColumn p)

  sEval : ∀ p → Eval.Eval (t p) R.O.sliceResidual
  sEval p = subtract (V.slice p) (P.sliceColumn p)

  dClear : ∀ p → (powC (t p) 3362 *C d p) ≈C Eval.value (dEval p)
  dClear p = complexTrans (Alg.mulSub (powC (t p) 3362) _ _)
    (A.subCCongruent (V.actualDiagonal p) (P.diagonalT p))

  sClear : ∀ p → (powC (t p) 1722 *C s p) ≈C Eval.value (sEval p)
  sClear p = complexTrans (Alg.mulSub (powC (t p) 1722) _ _)
    (A.subCCongruent (V.actualSlice p) (P.sliceT p))

  dTail : ∀ p → Eval.Eval (t p) (Tail.drop 3363 R.O.diagonalResidual)
  dTail p = Tail.tailRead (V.Rm.tNZ p) 3363 (dEval p)

  sTail : ∀ p → Eval.Eval (t p) (Tail.drop 1723 R.O.sliceResidual)
  sTail p = Tail.tailRead (V.Rm.tNZ p) 1723 (sEval p)

  cancelPole : ∀ p k a b →
    (powC (t p) k *C a) ≈C (powC (t p) (suc k) *C b) →
    a ≈C (t p *C b)
  cancelPole p k a b h = J.cancelLeft (powC (t p) k) a (t p *C b)
    (J.nonzeroPower (V.Rm.tNZ p) k)
    (complexTrans h
      (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative (t p) (powC (t p) k)) (C.≈C-refl _))
        (L.complexMultiplyAssociative (powC (t p) k) (t p) b)))

  diagonalFactor : R.W.UnitGate → R.W.DiagonalGate → ∀ p →
    d p ≈C (t p *C Eval.value (dTail p))
  diagonalFactor hu hd p = cancelPole p 3362 _ _
    (complexTrans (dClear p) (Tail.factor (V.Rm.tNZ p) 3362 (dEval p) (R.diagonalZero hu hd)))

  sliceFactor : R.W.UnitGate → R.W.SliceGate → ∀ p →
    s p ≈C (t p *C Eval.value (sTail p))
  sliceFactor hu hs p = cancelPole p 1722 _ _
    (complexTrans (sClear p) (Tail.factor (V.Rm.tNZ p) 1722 (sEval p) (R.sliceZero hu hs)))

  -- S/T transport is on the *uncleared* residual, not on its
  -- normalized t power, which is not itself modular invariant.
  jS : ∀ p → G.j (Gen.actS p) ≈C G.j p
  jS p = G.KJ.jS p (G.globalGuard p) (G.globalGuard (Gen.actS p))

  jT : ∀ p → G.j (Gen.actT p) ≈C G.j p
  jT p = G.KJ.jT p (G.globalGuard p) (G.globalGuard (Gen.actT p))

  dS : ∀ p → d (Gen.actS p) ≈C d p
  dS p = A.subCCongruent (G.diagonalS p) (Poly.polyCong (jS p) Packet.diagonal)
  dT : ∀ p → d (Gen.actT p) ≈C d p
  dT p = A.subCCongruent (G.diagonalT p) (Poly.polyCong (jT p) Packet.diagonal)
  sS : ∀ p → s (Gen.actS p) ≈C s p
  sS p = A.subCCongruent (G.productS p K) (Poly.polyCong (jS p) Packet.slice)
  sT : ∀ p → s (Gen.actT p) ≈C s p
  sT p = A.subCCongruent (G.productT p K) (Poly.polyCong (jT p) Packet.slice)
