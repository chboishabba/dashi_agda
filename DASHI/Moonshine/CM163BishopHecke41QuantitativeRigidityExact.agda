module DASHI.Moonshine.CM163BishopHecke41QuantitativeRigidityExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- Geometry is isolated as a constructive S/T orbit cover, not as an
-- analytic vanishing hypothesis. All remaining analytic estimates
-- are assembled on the actual ordinary residual coefficient streams.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as Series
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Same
import DASHI.Moonshine.CM163BishopHecke41DyadicCircleBoundsExact as Circle
import DASHI.Moonshine.CM163BishopHecke41DyadicFourierProjectionExact as Proj
import DASHI.Moonshine.CM163BishopHecke41FourierCoefficientBoundExact as Fourier
import DASHI.Moonshine.CM163BishopHecke41CuspContractionExact as Contract
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as Bound
import DASHI.Moonshine.CM163BishopHecke41UnramifiedResidualExact as Desc
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open Proj using (Point; Func)
open Contract using (Box; boxCong)
open Comp using (complexTrans; complexSym)

-- Compact finite T-runs keep the witness independent of the numeric
-- size of the real part. Their semantics are still proved by induction
-- from the one-step T invariance and the coordinate-setoid transport.
minusT : Point → Point
minusT = Gen.actMinusT

minusTUndo : ∀ p → U.tau (Gen.actT (minusT p)) ≈C U.tau p
minusTUndo = Gen.actTAfterMinusT

minusTHeight : ∀ p → R._≃_ (C.im (U.tau (minusT p))) (C.im (U.tau p))
minusTHeight = Gen.actMinusTHeight

forwardPowerPoint : Nat → Point → Point
forwardPowerPoint zero p = p
forwardPowerPoint (suc n) p = Gen.actT (forwardPowerPoint n p)

minusPowerPoint : Nat → Point → Point
minusPowerPoint zero p = p
minusPowerPoint (suc n) p = minusPowerPoint n (minusT p)

data Orbit : Point → Point → Set where
  stay : ∀ p → Orbit p p
  stepS : ∀ {p v} → Orbit p v → Orbit p (Gen.actS v)
  stepT : ∀ {p v} → Orbit p v → Orbit p (Gen.actT v)
  same : ∀ {p v w} → Orbit p v → U.tau v ≈C U.tau w → Orbit p w
  backS : ∀ {p v} → Orbit p (Gen.actS v) → Orbit p v
  backT : ∀ {p v} → Orbit p (Gen.actT v) → Orbit p v
  tRun : ∀ {p v} → Orbit p v → (n : Nat) → Orbit p (forwardPowerPoint n v)
  minusRun : ∀ {p v} → Orbit p v → (n : Nat) → Orbit p (minusPowerPoint n v)

forwardPowerRead : ∀ (F : Func) →
  (∀ p → F (Gen.actT p) ≈C F p) →
  ∀ n p → F p ≈C F (forwardPowerPoint n p)
forwardPowerRead F ht zero p = C.≈C-refl _
forwardPowerRead F ht (suc n) p =
  complexTrans (forwardPowerRead F ht n p)
    (complexSym (ht (forwardPowerPoint n p)))

minusTReadInvariant : ∀ (F : Func) →
  (∀ p → F (Gen.actT p) ≈C F p) →
  (∀ p v → U.tau p ≈C U.tau v → F p ≈C F v) →
  ∀ p → F (minusT p) ≈C F p
minusTReadInvariant F ht hc p =
  complexTrans (complexSym (ht (minusT p)))
    (hc (Gen.actT (minusT p)) p (minusTUndo p))

minusPowerRead : ∀ (F : Func) →
  (∀ p → F (Gen.actT p) ≈C F p) →
  (∀ p v → U.tau p ≈C U.tau v → F p ≈C F v) →
  ∀ n p → F p ≈C F (minusPowerPoint n p)
minusPowerRead F ht hc zero p = C.≈C-refl _
minusPowerRead F ht hc (suc n) p =
  complexTrans (minusTReadInvariant F ht hc p)
    (minusPowerRead F ht hc n (minusT p))

orbitRead : ∀ (F : Func) →
  (∀ p → F (Gen.actS p) ≈C F p) →
  (∀ p → F (Gen.actT p) ≈C F p) →
  (∀ p v → U.tau p ≈C U.tau v → F p ≈C F v) →
  ∀ {p v} → Orbit p v → F p ≈C F v
orbitRead F hs ht hc (stay p) = C.≈C-refl _
orbitRead F hs ht hc (stepS {v = v} w) = complexTrans (orbitRead F hs ht hc w) (complexSym (hs v))
orbitRead F hs ht hc (stepT {v = v} w) = complexTrans (orbitRead F hs ht hc w) (complexSym (ht v))
orbitRead F hs ht hc (same {v = v} {w = w} o e) = complexTrans (orbitRead F hs ht hc o) (hc v w e)
orbitRead F hs ht hc (backS {v = v} w) = complexTrans (orbitRead F hs ht hc w) (hs v)
orbitRead F hs ht hc (backT {v = v} w) = complexTrans (orbitRead F hs ht hc w) (ht v)
orbitRead F hs ht hc (tRun {v = v} w n) =
  complexTrans (orbitRead F hs ht hc w) (forwardPowerRead F ht n v)
orbitRead F hs ht hc (minusRun {v = v} w n) =
  complexTrans (orbitRead F hs ht hc w) (minusPowerRead F ht hc n v)

module At (inputs : Round11.BishopCutset) where
  module H = Circle.At inputs
  module Fourier0 = Fourier.At inputs
  module Rm = Ram.At inputs
  q = H.q
  nz = H.nz

  record Reduced (ref p : Point) : Set₁ where
    field
      point : Point
      word : Orbit p point
      inside : R._≤_ (Norm.normSqC (q point)) (Norm.normSqC (q ref))
      small : Upper.BishopComplexNormSquareUpperRadius
        (Bound.relative (q point) (q ref) (nz ref)) Contract.rho

  -- Only this geometric construction is still external to the
  -- analytic consumer. It is uniform in all residuals.
  Cover : Point → Set₁
  Cover ref = ∀ p → Reduced ref p

  module For (ref : Point) (cover : Cover ref)
    (f : N.SeriesC) (zeroMode : f zero ≈C A.zeroC)
    (ev : ∀ p → Eval.Eval (q p) f)
    (F : Func) (actual : ∀ p → F p ≈C Eval.value (ev p))
    (hs : ∀ p → F (Gen.actS p) ≈C F p)
    (ht : ∀ p → F (Gen.actT p) ≈C F p) where

    -- Setoid coordinate transport is derived from the SAME series,
    -- not assumed as an additional invariance premise.
    qCong : ∀ p v → U.tau p ≈C U.tau v → q p ≈C q v
    qCong p v (x , y) = Rm.expCong
      (P.-‿cong (P.*-cong P.≃-refl y) , P.*-cong P.≃-refl x)

    valueCong : ∀ p v → U.tau p ≈C U.tau v → F p ≈C F v
    valueCong p v h =
      let e = ev p
          moved : Eval.Eval (q v) f
          moved = record { value = Eval.value e
                         ; absolute = CP.complexAbsTransport (Series.twistPhaseCong (qCong p v h) f) (Eval.absolute e)
                         ; converges = CP.complexLimitTransport (Series.twistPhaseCong (qCong p v h) f) (Eval.converges e) }
      in complexTrans (actual p) (complexTrans (Same.sameEval moved (ev v)) (complexSym (actual v)))

    module D = Contract.Disk (q ref) (nz ref) f (ev ref) zeroMode
    module FB = Fourier0.For ref f ev
    module I = Contract.Iterate F

    initial : I.Global D.B.M
    initial p =
      let c = cover p
          v = Reduced.point c
          eq = complexTrans (orbitRead F hs ht valueCong (Reduced.word c)) (actual v)
      in boxCong (complexSym eq) (D.B.valueBound (q v) (Reduced.inside c) (ev v))

    shrink : ∀ M → R.NonNegative M → I.Global M → I.Global (R._*_ Contract.contraction M)
    shrink M nn hb p =
      let c = cover p
          v = Reduced.point c
          coeff = FB.coefficientBound M (λ u → boxCong (actual u) (hb u))
          eq = complexTrans (orbitRead F hs ht valueCong (Reduced.word c)) (actual v)
      in boxCong (complexSym eq) (D.contract M nn coeff (q v) (Reduced.small c) (ev v))

    module End = I.From D.B.M D.B.Mnonnegative initial shrink
    zeroEverywhere : ∀ p → F p ≈C A.zeroC
    zeroEverywhere = End.zeroEverywhere

  module A0 = Desc.At inputs
  module R0 = A0.R0

  diagonalZero : ∀ ref → Cover ref → R0.R.W.UnitGate → R0.R.W.DiagonalGate →
    ∀ p → R0.d p ≈C A.zeroC
  diagonalZero ref cover hu hd =
    let series = A0.diagonal hu hd ref
        module End = For ref cover
          (Tail.drop 82 (R41.restrictC A0.O.diagonalResidual))
          (Desc.ZeroConstantSeries.zeroConstant series)
          (λ p → Desc.ZeroConstantSeries.evaluated (A0.diagonal hu hd p))
          R0.d (λ p → Desc.ZeroConstantSeries.actual (A0.diagonal hu hd p))
          R0.dS R0.dT
    in End.zeroEverywhere

  sliceZero : ∀ ref → Cover ref → R0.R.W.UnitGate → R0.R.W.SliceGate →
    ∀ p → R0.s p ≈C A.zeroC
  sliceZero ref cover hu hs =
    let series = A0.slice hu hs ref
        module End = For ref cover
          (Tail.drop 42 (R41.restrictC A0.O.sliceResidual))
          (Desc.ZeroConstantSeries.zeroConstant series)
          (λ p → Desc.ZeroConstantSeries.evaluated (A0.slice hu hs p))
          R0.s (λ p → Desc.ZeroConstantSeries.actual (A0.slice hu hs p))
          R0.sS R0.sT
    in End.zeroEverywhere
