module DASHI.Moonshine.CM163BishopHecke41ComplexExpSecondJetExact where

-- SOURCE-WRITTEN, kernel pending. Actual complex exponential, not
-- only a real directional restriction. The second remainder is the
-- original factorial tail evaluated on a fixed closed unit disk.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (from-yes)
import Real as R
open R using (_⋆)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopComplexExpFactEqualsNativeExpExact as Native
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Moonshine.AbelBishopFactorialComplexExpDiskExact as Fact
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Axis
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.JInvariantBishopComplexOriginQuadraticRemainderExact as Origin
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopThetaSignedReadoutExact as Sp
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41UniformSeriesContinuityExact as U
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as Jet
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Pow
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)

f : N.SeriesC
f n = Poly.realC (Fact.factorialCoefficient n)

weighted : ∀ z n → N.twist z f n ≈C Axis.originalBishopFactorialComplexTerm z n
weighted z n = complexSym (Origin.scaleAxis (Fact.factorialCoefficient n) (powC z n))

zeroAbs : Seq.SeriesOf_ConvergesAbsolutely (λ _ → R.0ℝ)
zeroAbs = Seq.proposition-3-5 Sp.zeroConvergent (zero , λ n _ →
  P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0))

referenceAbs : C.ComponentwiseAbsoluteSeriesConvergent (N.twist A.oneC f)
referenceAbs = CP.complexAbsTransport
  (λ n → complexSym (complexTrans (weighted A.oneC n)
    (Axis.originalBishopFactorialComplexTermRealAxis R.1ℝ n)))
  (C.componentwise-absolute-series-convergent (Exp.expAbsoluteSeriesConvergent R.1ℝ) zeroAbs)

reference : Eval.Eval A.oneC f
reference = record
  { value = C.complexSeriesLimit (N.twist A.oneC f) referenceAbs
  ; absolute = referenceAbs
  ; converges = C.complexSeriesLimitConvergence _ referenceAbs }

module F = U.Disk A.oneC Cancel.nonzeroOne f reference
module Remainder = U.Disk A.oneC Cancel.nonzeroOne (Tail.drop 2 f)
  (Tail.tailRead Cancel.nonzeroOne 2 reference)

Inside : BishopComplex → Set
Inside = F.Inside

expRead : (T : Cartesian.BishopSetoidComplexTranscendentals) → ∀ z → Inside z → Eval.Eval z f
expRead T z h = record
  { value = Weld.originalBishopExpOnSeries T z
  ; absolute = Eval.absolute (F.D.evaluate z h)
  ; converges = CP.complexLimitTransport (λ n → complexSym (weighted z n))
      (Native.originalBishopExpFactComplexSeriesConvergesToNativeExp T (C.re z) (C.im z)) }

remainder : ∀ z → Inside z → BishopComplex
remainder z h = Eval.value (Remainder.D.evaluate z h)

-- The first two actual factorial terms are kept, then the complete
-- shifted original coefficient stream is multiplied by z^2.
prefixExpansion : ∀ z n →
  U.complexPrefix (N.twist z f) (suc (suc n)) ≈C
    ((A.oneC +C z) +C powC z 2 *C U.complexPrefix (N.twist z (Tail.drop 2 f)) n)
prefixExpansion z zero =
  complexTrans (A.addCCongruent
    (complexTrans (L.complexAddLeftIdentity _) (complexTrans (weighted z zero) (Origin.head0 z)))
    (complexTrans (weighted z 1) (Origin.head1 z)))
    (complexSym (complexTrans (A.addCCongruent (C.≈C-refl _) (L.complexMultiplyRightZero _))
      (L.complexAddRightIdentity _)))
prefixExpansion z (suc n) =
  complexTrans (A.addCCongruent (prefixExpansion z n) (Tail.dropTwist z f 2 n))
    (complexTrans (L.complexAddAssociative _ _ _)
      (A.addCCongruent (C.≈C-refl _) (complexSym (L.complexMultiplyDistributesLeft (powC z 2) _ _))))

expansion : (T : Cartesian.BishopSetoidComplexTranscendentals) → ∀ z h →
  Weld.originalBishopExpOnSeries T z ≈C ((A.oneC +C z) +C powC z 2 *C remainder z h)
expansion T z h =
  let e = expRead T z h
      tail = Remainder.D.evaluate z h
      cv = Eval.converges e
      open C
      shifted = Completion.original-bishop-pointwise-complex-converges
        (Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
          (Seq.shift-is-subsequence (Seq.SeriesOf (C.realTerms (N.twist z f))) 2) (_ , realConverges cv))
        (Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
          (Seq.shift-is-subsequence (Seq.SeriesOf (C.imagTerms (N.twist z f))) 2) (_ , imagConverges cv))
  in Lim.convUnique (Lim.convTransport (prefixExpansion z) shifted)
    (Lim.addConv (Lim.constantC (A.oneC +C z)) (Lim.mulConst (powC z 2) (D.prefixLimit (Eval.converges tail))))

zeroInside : Inside A.zeroC
zeroInside = P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 0
  (Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ) P.≃-refl)
  (P.≤-respʳ-≃ (P.≃-symm Norm.normSqOne)
    (P.<⇒≤ (P.p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (from-yes (0ℚᵘ QP.<? 1ℚᵘ)))))

-- A zero phase retains only the head of the shifted series.
zeroPower : ∀ n → powC A.zeroC (suc n) ≈C A.zeroC
zeroPower n = L.complexMultiplyLeftZero _

zeroPrefix : ∀ n → U.complexPrefix (N.twist A.zeroC (Tail.drop 2 f)) (suc n) ≈C f 2
zeroPrefix zero = complexTrans (L.complexAddLeftIdentity _) (L.complexMultiplyRightIdentity _)
zeroPrefix (suc n) = complexTrans
  (A.addCCongruent (zeroPrefix n) (complexTrans (A.mulCCongruent (C.≈C-refl _) (zeroPower n))
    (L.complexMultiplyRightZero _))) (L.complexAddRightIdentity _)

center : remainder A.zeroC zeroInside ≈C Poly.realC ((+ 1 / 2) ⋆)
center =
  let cv = D.prefixLimit (Eval.converges (Remainder.D.evaluate A.zeroC zeroInside))
      shifted = Completion.original-bishop-pointwise-complex-converges
        (Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y (Seq.shift-is-subsequence (Seq.SeriesOf (C.realTerms (N.twist A.zeroC (Tail.drop 2 f)))) 1) (_ , C.realConverges (Eval.converges (Remainder.D.evaluate A.zeroC zeroInside))))
        (Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y (Seq.shift-is-subsequence (Seq.SeriesOf (C.imagTerms (N.twist A.zeroC (Tail.drop 2 f)))) 1) (_ , C.imagConverges (Eval.converges (Remainder.D.evaluate A.zeroC zeroInside))))
      c = Lim.convTransport zeroPrefix shifted
  in complexTrans (Lim.convUnique c (Lim.constantC (f 2))) (P.≃-refl , P.≃-refl)

-- Actual second coefficient at 0, in every complex direction.
secondLimit : (z : Nat → BishopComplex) → (h : ∀ n → Inside (z n)) →
  Lim.Conv z A.zeroC → Lim.Conv (λ n → remainder (z n) (h n)) (Poly.realC ((+ 1 / 2) ⋆))
secondLimit z h cv = Lim.limitTransport center
  (Remainder.continuous z A.zeroC h zeroInside cv (λ n → Remainder.D.evaluate (z n) (h n))
    (Remainder.D.evaluate A.zeroC zeroInside))

-- The normalized first slope is itself a genuine first jet.
slope : ∀ z h → BishopComplex
slope z h = A.oneC +C z *C remainder z h

slopeJet : (z : Nat → BishopComplex) → (h : ∀ n → Inside (z n)) →
  Lim.Conv z A.zeroC →
  Jet.Jet z (λ n → slope (z n) (h n)) A.oneC (Poly.realC ((+ 1 / 2) ⋆))
slopeJet z h cv = record
  { Jet.quotient = λ n → remainder (z n) (h n)
  ; Jet.factor = λ n → Jet.subtractHead A.oneC (z n *C remainder (z n) (h n))
  ; Jet.limit = secondLimit z h cv }
