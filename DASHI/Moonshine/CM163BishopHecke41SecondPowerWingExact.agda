module DASHI.Moonshine.CM163BishopHecke41SecondPowerWingExact where

-- SOURCE-WRITTEN, kernel pending. The second divided difference of the
-- original power wing, including coincident endpoints. Classical
-- divided differences; no derivative or quotient-by-increment oracle.
open import Agda.Builtin.Nat using (Nat; zero; suc)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41UniformSeriesContinuityExact as Uniform
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)
open Uniform using (complexPrefix)

-- T_n(u,v,w) = sum_{i+j+k=n-2} u^i v^j w^k.
-- Use precisely the original Q recurrence, not a new power series.
T : BishopComplex → BishopComplex → BishopComplex → Nat → BishopComplex
T u v w zero = A.zeroC
T u v w (suc n) = D.Q v w n +C u *C T u v w n

factor : ∀ u v w n → (D.Q u w n -C D.Q u v n) ≈C
  ((w -C v) *C T u v w n)
factor u v w zero = complexTrans (J.sameSub A.zeroC)
  (complexSym (L.complexMultiplyRightZero (w -C v)))
factor u v w (suc n) =
  complexTrans (A.subCCongruent (D.qStep u w n) (D.qStep u v n))
    (complexTrans (J.addStep (powC w n) (u *C D.Q u w n)
                             (powC v n) (u *C D.Q u v n))
      (complexTrans (A.addCCongruent (D.factor v w n)
        (complexTrans (J.subFactor u (D.Q u w n) (D.Q u v n))
          (A.mulCCongruent (C.≈C-refl _) (factor u v w n))))
        (Cross.restFinish u (w -C v) (D.Q v w n) (T u v w n))))

-- Explicit monomial wing: its outer index is the retained u degree.
-- This form gives a polynomial, not exponential, majorant.
wing : BishopComplex → BishopComplex → BishopComplex → Nat → Nat → BishopComplex
wing u v w k zero = A.zeroC
wing u v w k (suc n) =
  (powC u k *C D.Q v w n) +C wing u v w (suc k) n

wingStep : ∀ u v w k n → wing u v w (suc k) n ≈C
  (u *C wing u v w k n)
wingStep u v w k zero = complexSym (L.complexMultiplyRightZero u)
wingStep u v w k (suc n) =
  complexTrans (A.addCCongruent
    (L.complexMultiplyAssociative u (powC u k) (D.Q v w n))
    (wingStep u v w (suc k) n))
    (complexSym (L.complexMultiplyDistributesLeft u _ _))

wingRead : ∀ u v w n → wing u v w zero n ≈C T u v w n
wingRead u v w zero = C.≈C-refl _
wingRead u v w (suc n) =
  A.addCCongruent (L.complexMultiplyLeftIdentity _)
    (complexTrans (wingStep u v w zero n)
      (A.mulCCongruent (C.≈C-refl _) (wingRead u v w n)))

continuous : ∀ u v {w : Nat → BishopComplex} {z} → Lim.Conv w z → ∀ n →
  Lim.Conv (λ i → T u v (w i) n) (T u v z n)
continuous u v cv zero = Lim.constantC A.zeroC
continuous u v cv (suc n) = Lim.addConv
  (D.wingContinuous v cv zero n)
  (Lim.mulConst u (continuous u v cv n))

terms : N.SeriesC → BishopComplex → BishopComplex → BishopComplex → N.SeriesC
terms f u v w n = f n *C T u v w n

termFactor : ∀ f u v w n →
  (D.terms f u w n -C D.terms f u v n) ≈C ((w -C v) *C terms f u v w n)
termFactor f u v w n =
  complexTrans (J.subFactor (f n) (D.Q u w n) (D.Q u v n))
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (factor u v w n))
      (complexTrans (complexSym (L.complexMultiplyAssociative (f n) (w -C v) (T u v w n)))
        (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative (f n) (w -C v)) (C.≈C-refl _))
          (L.complexMultiplyAssociative (w -C v) (f n) (T u v w n)))))

prefixFactor : ∀ f u v w m →
  (complexPrefix (D.terms f u w) m -C complexPrefix (D.terms f u v) m) ≈C
  ((w -C v) *C complexPrefix (terms f u v w) m)
prefixFactor f u v w m =
  complexTrans (complexSym (D.prefixSub (D.terms f u w) (D.terms f u v) m))
    (complexTrans (D.prefixCong _ _ (termFactor f u v w) m)
      (D.prefixMul (w -C v) (terms f u v w) m))

-- This is the actual limit equality of the three specified series;
-- the remaining majorant owner must construct the second convergence.
limitFactor : ∀ f u v w a b c →
  C.ComplexSeriesConvergesTo (D.terms f u w) a →
  C.ComplexSeriesConvergesTo (D.terms f u v) b →
  C.ComplexSeriesConvergesTo (terms f u v w) c →
  (a -C b) ≈C ((w -C v) *C c)
limitFactor f u v w a b c ca cb cc =
  Lim.convUnique
    (Lim.convTransport (prefixFactor f u v w)
      (Lim.subConv (D.prefixLimit ca) (D.prefixLimit cb)))
    (Lim.mulConst (w -C v) (D.prefixLimit cc))

-- All first quotients come from the pre-existing actual series evaluator.
-- The only new analytic premise is convergence of the second-wing
-- series and its diagonal limit, not an arbitrary independent slope.
module Attach (f : N.SeriesC)
  (u : BishopComplex) (v : Nat → BishopComplex)
  (eu : Eval.Eval u f) (ev : ∀ n → Eval.Eval (v n) f)
  (q : Nat → BishopComplex) (a b : BishopComplex)
  (firstFactor : ∀ n → (Eval.value (ev n) -C Eval.value eu) ≈C
    ((v n -C u) *C q n))
  (firstSeries : ∀ n → C.ComplexSeriesConvergesTo (D.terms f u (v n)) (q n))
  (centerSeries : C.ComplexSeriesConvergesTo (D.terms f u u) a)
  (firstLimit : Lim.Conv q a)
  (t : Nat → BishopComplex)
  (secondSeries : ∀ n → C.ComplexSeriesConvergesTo (terms f u u (v n)) (t n))
  (secondLimit : Lim.Conv t b) where

  actualTwoJet : J2.Jet2 (λ n → v n -C u) (λ n → Eval.value (ev n))
    (Eval.value eu) a b
  actualTwoJet = record
    { first = record { J.quotient = q ; J.factor = firstFactor ; J.limit = firstLimit }
    ; second = record
      { J.quotient = t
      ; J.factor = λ n → limitFactor f u u (v n) (q n) a (t n)
          (firstSeries n) centerSeries (secondSeries n)
      ; J.limit = secondLimit } }
