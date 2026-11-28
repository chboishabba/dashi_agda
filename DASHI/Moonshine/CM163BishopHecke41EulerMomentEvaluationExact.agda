module DASHI.Moonshine.CM163BishopHecke41EulerMomentEvaluationExact where

-- SOURCE-WRITTEN / KERNEL PENDING. Transfer diagonal wing limits
-- back to the actual unnormalized source Euler series, preserving
-- absolute convergence and both signed complex coordinates.
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHecke41SecondPowerWingExact as T
import DASHI.Moonshine.CM163BishopHecke41DiagonalEulerMomentsExact as M
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as Bound
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_)
open Comp using (complexTrans; complexSym)

record Stream (f : N.SeriesC) : Set where
  field
    value : BishopComplex
    absolute : C.ComponentwiseAbsoluteSeriesConvergent f
    converges : C.ComplexSeriesConvergesTo f value
open Stream public

scale : ∀ k {f} → Stream f → Stream (λ n → k *C f n)
scale k {f} s = record
  { value = k *C value s
  ; absolute = Tail.mulAbs k f (absolute s)
  ; converges =
      let cv = Lim.convTransport (λ m → complexSym (D.prefixMul k f m))
            (Lim.mulConst k (D.prefixLimit (converges s)))
      in C.complex-series-converges-to
          (Completion.realConverges cv) (Completion.imaginaryConverges cv) }

add : ∀ {f g} → Stream f → Stream g → Stream (λ n → f n +C g n)
add {f} {g} s t = record
  { value = value s +C value t
  ; absolute = C.componentwise-absolute-series-convergent
      (CP.plusAbs _ _ (C.realAbsolute (absolute s)) (C.realAbsolute (absolute t)))
      (CP.plusAbs _ _ (C.imagAbsolute (absolute s)) (C.imagAbsolute (absolute t)))
  ; converges = C.complex-series-converges-to
      (CP.plusConv (C.realConverges (converges s)) (C.realConverges (converges t)))
      (CP.plusConv (C.imagConverges (converges s)) (C.imagConverges (converges t))) }

at : ∀ {q f g} → (∀ n → g n ≈C N.twist q f n) → Stream g → Eval.Eval q f
at eq s = record
  { Eval.value = value s
  ; Eval.absolute = CP.complexAbsTransport eq (absolute s)
  ; Eval.converges = CP.complexLimitTransport eq (converges s) }

fromEval : ∀ {q f} → Eval.Eval q f → Stream (N.twist q f)
fromEval ev = record { value = Eval.value ev ; absolute = Eval.absolute ev ; converges = Eval.converges ev }

module At (q inner : BishopComplex) (nz : Rec.BishopComplexNonzero inner)
  (f : N.SeriesC) where
  u = Bound.relative q inner nz
  g = N.twist inner f

  -- Twist composition followed by coefficientwise phase congruence
  -- gives exactly the original q, not a substituted scalar radius.
  original : ∀ h → N.twist u (N.twist inner h) N.≈cs N.twist q h
  original h = N.transCs (N.twistCompose u inner h)
    (N.twistPhaseCong (Bound.relativeRead q inner nz) h)

  firstOriginal : N.twist u (E.δ g) N.≈cs N.twist q (E.δ f)
  firstOriginal = N.transCs (N.twistCong u (E.dTwist inner f)) (original (E.δ f))

  secondOriginal : N.twist u (E.δ (E.δ g)) N.≈cs N.twist q (E.δ (E.δ f))
  secondOriginal = N.transCs (N.twistCong u
    (N.transCs (E.dCong (E.dTwist inner f)) (E.dTwist inner (E.δ f))))
    (original (E.δ (E.δ f)))

  first : Stream (D.terms g u u) → Eval.Eval q (E.δ f)
  first s = at (λ n → complexTrans (M.firstTerm g u n) (firstOriginal n)) (scale u s)

  second : Stream (D.terms g u u) → Stream (T.terms g u u u) →
    Eval.Eval q (E.δ (E.δ f))
  second s t =
    let a = scale u s
        b = scale u (scale u t)
    in at (λ n → complexTrans (M.secondTerm g u n) (secondOriginal n))
      (add a (add b b))
