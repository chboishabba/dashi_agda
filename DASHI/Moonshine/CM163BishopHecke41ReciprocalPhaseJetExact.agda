module DASHI.Moonshine.CM163BishopHecke41ReciprocalPhaseJetExact where

-- R3/R4, SOURCE-WRITTEN / KERNEL PENDING.
-- One original logarithmic jet at the selected center, applied on
-- the three actual modular rays, not three independent coefficients.
open import Agda.Builtin.Nat using (Nat; _+_)
import Data.Nat.Properties as NP
import Sequence as Seq
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
open import Data.Fin.Base as Fin using (Fin; toℕ)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ)
open import Data.Product.Base using (_,_)
import Real as R
import RealProperties as P
open R using (_*_)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Const
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopCM163ReciprocalGeometryExact as Geo
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.CM163BishopHecke41ReciprocalRayCoordinateExact as Ray
import DASHI.Moonshine.CM163BishopHecke41ActualReciprocalRayTransportExact as Transport
import DASHI.Moonshine.CM163BishopHecke41ActualJLogPhaseJetExact as Log
import DASHI.Moonshine.CM163BishopHecke41ComplexExpSecondJetExact as Exp
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; scaleC)
open Comp using (complexTrans; complexSym)

multiplier : BishopComplex
multiplier = C.complex R.0ℝ (Phase.two * Phase.pi)

ell : BishopComplex
ell = multiplier *C Ray.d

-- Affine parameter transport supplies convergence of ALL 42 charts
-- before applying any analytic series theorem.
finiteRead : ∀ k p → U.tau (Chart.finitePoint k p) ≈C
  scaleC Chart.inv41 (U.tau p +C Poly.realC (K.embedInteger (+ k)))
finiteRead k p = P.≃-refl ,
  P.*-congˡ (P.≃-symm (P.+-identityʳ (C.im (U.tau p))))

finiteCV : ∀ k → Lim.Conv (λ n → U.tau (Chart.finitePoint k (Ray.ray n)))
  (U.tau (Chart.finitePoint k Fixed.p))
finiteCV k = Lim.convTransport (λ n → complexSym (finiteRead k (Ray.ray n)))
  (Lim.limitTransport (complexSym (finiteRead k Fixed.p))
    (Conv.scaleConv (Const.constantConverges Chart.inv41)
      (Lim.addConv Ray.tauCV (Lim.constantC (Poly.realC (K.embedInteger (+ k)))))))

chartCV : ∀ i → Lim.Conv (λ n → U.tau (Chart.chartPoint i (Ray.ray n)))
  (U.tau (Chart.chartPoint i Fixed.p))
chartCV i with toℕ i ≟ 41
... | yes _ = Conv.scaleConv (Const.constantConverges Chart.fortyOne) Ray.tauCV
... | no _ = finiteCV (toℕ i)

-- Use a common tail of the actual ray.  The initial large
-- increments do not satisfy the local exponential unit-disk bound.
drop : ∀ {X : Set} → Nat → (Nat → X) → Nat → X
drop k f n = f (n + k)

dropRealCV : ∀ k {f : Nat → R.ℝ} {a} →
  Seq._ConvergesTo_ f a → Seq._ConvergesTo_ (drop k f) a
dropRealCV k cv =
  Seq.xₙ⊆yₙ∧yₙ→y
    (Seq.subseq* ((λ n → n + k) , (λ n → P.≃-refl) ,
      (λ n → NP.n<1+n (n + k)))) (_ , cv)

dropCV : ∀ k {f : Nat → BishopComplex} {a} →
  Lim.Conv f a → Lim.Conv (drop k f) a
dropCV k cv = Completion.original-bishop-pointwise-complex-converges
  (dropRealCV k (Completion.realConverges cv))
  (dropRealCV k (Completion.imaginaryConverges cv))

dropJet : ∀ k {w f a b} → J.Jet w f a b →
  J.Jet (drop k w) (drop k f) a b
dropJet k j = record
  { J.quotient = drop k (J.quotient j)
  ; J.factor = λ n → J.factor j (n + k)
  ; J.limit = dropCV k (J.limit j) }

drop2 : ∀ k {w f a b c} → J2.Jet2 w f a b c →
  J2.Jet2 (drop k w) (drop k f) a b c
drop2 k j = record
  { J2.first = dropJet k (J2.first j)
  ; J2.second = dropJet k (J2.second j) }

-- All rotations use the same base exponent and coefficients.
module At (inputs : Round11.BishopCutset) (start : Nat) where
  W = drop start Ray.w
  point = drop start Ray.ray
  wCV = dropCV start Ray.wCV

  module H = Log.At inputs
  module Ph = H.Phase.Ph
  module Base = H.Around Fixed.p
  module G = H.G
  module T = Transport.At inputs

  exponentRead : ∀ p → Ph.exponent p ≈C (multiplier *C U.tau p)
  exponentRead p =
    (let open P.ℝ-Solver in solve 3 (λ a x y →
      (⊝ (a ⊗ y)) ⊜ (Κ 0ℚᵘ ⊗ x) ⊖ (a ⊗ y))
      P.≃-refl (Phase.two * Phase.pi) (C.re (U.tau p)) (C.im (U.tau p))) ,
    (let open P.ℝ-Solver in solve 3 (λ a x y →
      a ⊗ x ⊜ (Κ 0ℚᵘ ⊗ y) ⊕ (a ⊗ x))
      P.≃-refl (Phase.two * Phase.pi) (C.re (U.tau p)) (C.im (U.tau p)))

  exponentCV : ∀ (v : Nat → U.BishopUpperHalfPlanePoint) p →
    Lim.Conv (λ n → U.tau (v n)) (U.tau p) →
    Lim.Conv (λ n → Ph.exponent (v n)) (Ph.exponent p)
  exponentCV v p cv = Lim.convTransport (λ n → complexSym (exponentRead (v n)))
    (Lim.limitTransport (complexSym (exponentRead p)) (Lim.mulConst multiplier cv))

  inc : U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint → BishopComplex
  inc p v = Ph.exponent v -C Ph.exponent p

  incCV : ∀ (v : Nat → U.BishopUpperHalfPlanePoint) p →
    Lim.Conv (λ n → U.tau (v n)) (U.tau p) →
    Lim.Conv (λ n → inc p (v n)) A.zeroC
  incCV v p cv = Lim.limitTransport (J.sameSub (Ph.exponent p))
    (Lim.subConv (exponentCV v p cv) (Lim.constantC (Ph.exponent p)))

  -- These are the exact domain conditions of the EXISTING analytic
  -- producer. Their eventual fulfillment is a separate order proof.
  Small : U.BishopUpperHalfPlanePoint → (Nat → U.BishopUpperHalfPlanePoint) → Set
  Small p v = ∀ n → Exp.Inside (inc p (v n))

  Inside : U.BishopUpperHalfPlanePoint → (Nat → U.BishopUpperHalfPlanePoint) → Set
  Inside p v = let module Local = H.Around p in ∀ n → Local.D.Ref.S.Inside (H.F.O.q (v n))

  phaseJet : ∀ (v : Nat → U.BishopUpperHalfPlanePoint) k →
    J2.Jet2 W (λ n → U.tau (v n)) Geo.tau (k *C Ray.d) ((k *C k) *C Ray.d) →
    J2.Jet2 W (λ n → Ph.exponent (v n)) (Ph.exponent Fixed.p)
      (k *C ell) ((k *C k) *C ell)
  phaseJet v k j = J2.cong2 (λ n → complexSym (exponentRead (v n)))
    (complexSym (exponentRead Fixed.p))
    (Transport.swapMiddle multiplier k Ray.d)
    (Transport.swapMiddle multiplier (k *C k) Ray.d)
    (J2.scale2 multiplier j)

  -- Fixed actual coefficients from the existing q-series jet.
  a0 b0 : BishopComplex
  a0 = ell *C Base.euler1
  b0 = a0 +C (ell *C (ell *C Base.eulerTaylor2))

  firstRotate : ∀ k → ((k *C ell) *C Base.euler1) ≈C (k *C a0)
  firstRotate k = L.complexMultiplyAssociative k ell Base.euler1

  secondRotate : ∀ k →
    ((((k *C k) *C ell) *C Base.euler1) +C
      ((k *C ell) *C ((k *C ell) *C Base.eulerTaylor2))) ≈C
    ((k *C k) *C b0)
  secondRotate k =
    complexTrans (A.addCCongruent (L.complexMultiplyAssociative (k *C k) ell Base.euler1)
      (complexTrans (complexSym (L.complexMultiplyAssociative (k *C ell) (k *C ell) Base.eulerTaylor2))
        (complexTrans (A.mulCCongruent (Alg.shuffle k ell k ell) (C.≈C-refl _))
          (complexTrans (L.complexMultiplyAssociative (k *C k) (ell *C ell) Base.eulerTaylor2)
            (A.mulCCongruent (C.≈C-refl _) (L.complexMultiplyAssociative ell ell Base.eulerTaylor2))))))
      (complexSym (L.complexMultiplyDistributesLeft (k *C k) a0 (ell *C (ell *C Base.eulerTaylor2))))

  along : ∀ (v : Nat → U.BishopUpperHalfPlanePoint) k →
    J2.Jet2 W (λ n → U.tau (v n)) Geo.tau (k *C Ray.d) ((k *C k) *C Ray.d) →
    Small Fixed.p v → Inside Fixed.p v →
    J2.Jet2 W (λ n → G.j (v n)) (G.j Fixed.p)
      (k *C a0) ((k *C k) *C b0)
  along v k tau small inside =
    let e = phaseJet v k tau
        cv = Lim.limitTransport (J.sameSub (Ph.exponent Fixed.p))
          (Lim.subConv (J.continuous wCV (J2.first e))
            (Lim.constantC (Ph.exponent Fixed.p)))
        outer = Base.actualLogJet v (λ n → inc Fixed.p (v n))
          (λ n → J.recover (Ph.exponent (v n)) (Ph.exponent Fixed.p)) small cv inside
    in J2.cong2 (λ _ → C.≈C-refl _) (C.≈C-refl _) (firstRotate k) (secondRotate k)
      (J2.compose wCV e outer)

  centerTau : J2.Jet2 W (λ n → U.tau (point n)) Geo.tau
    (A.oneC *C Ray.d) ((A.oneC *C A.oneC) *C Ray.d)
  centerTau = J2.cong2 (λ _ → C.≈C-refl _) (C.≈C-refl _)
    (complexSym (L.complexMultiplyLeftIdentity Ray.d))
    (complexSym (complexTrans (A.mulCCongruent (L.complexMultiplyLeftIdentity A.oneC) (C.≈C-refl _))
      (L.complexMultiplyLeftIdentity Ray.d))) (drop2 start Ray.tauJet)

  central : Small Fixed.p point → Inside Fixed.p point →
    J2.Jet2 W (λ n → G.j (point n)) (G.j Fixed.p) a0 b0
  central sm ins = J2.cong2 (λ _ → C.≈C-refl _) (C.≈C-refl _)
    (L.complexMultiplyLeftIdentity a0)
    (complexTrans (A.mulCCongruent (L.complexMultiplyLeftIdentity A.oneC) (C.≈C-refl _))
      (L.complexMultiplyLeftIdentity b0))
    (along point A.oneC centerTau sm ins)

  plus : Small Fixed.p (λ n → Transport.forward (point n)) →
    Inside Fixed.p (λ n → Transport.forward (point n)) →
    J2.Jet2 W (λ n → G.j (Chart.chartPoint (Fin.suc Fin.zero) (point n)))
      (G.j Fixed.p) (Geo.alpha *C a0) ((Geo.alpha *C Geo.alpha) *C b0)
  plus sm ins = J2.cong2 (λ n → T.forwardJ (point n))
    (C.≈C-refl _) (C.≈C-refl _) (C.≈C-refl _)
    (along (λ n → Transport.forward (point n)) Geo.alpha (drop2 start Transport.Plus.jet) sm ins)

  minus : Small Fixed.p (λ n → Transport.reverse (point n)) →
    Inside Fixed.p (λ n → Transport.reverse (point n)) →
    J2.Jet2 W (λ n → G.j (Chart.chartPoint Fin.zero (point n)))
      (G.j Fixed.p) (Geo.beta *C a0) ((Geo.beta *C Geo.beta) *C b0)
  minus sm ins = J2.cong2 (λ n → T.reverseJ (point n))
    (C.≈C-refl _) (C.≈C-refl _) (C.≈C-refl _)
    (along (λ n → Transport.reverse (point n)) Geo.beta (drop2 start Transport.Minus.jet) sm ins)

  -- R4: original chart continuity from the existing actual local jet,
  -- once the literal domain witnesses are constructed.
  jContinuous : ∀ p (v : Nat → U.BishopUpperHalfPlanePoint) →
    Lim.Conv (λ n → U.tau (v n)) (U.tau p) →
    Small p v → Inside p v →
    Lim.Conv (λ n → G.j (v n)) (G.j p)
  jContinuous p v cv sm ins =
    let module Local = H.Around p
        hcv = incCV v p cv
    in J.continuous hcv (J2.first (Local.actualLogJet v (λ n → inc p (v n))
      (λ n → J.recover (Ph.exponent (v n)) (Ph.exponent p)) sm hcv ins))

  chartJCV : (∀ i → Small (Chart.chartPoint i Fixed.p)
    (λ n → Chart.chartPoint i (point n))) →
    (∀ i → Inside (Chart.chartPoint i Fixed.p)
    (λ n → Chart.chartPoint i (point n))) →
    ∀ i → Lim.Conv (λ n → G.j (Chart.chartPoint i (point n)))
      (G.j (Chart.chartPoint i Fixed.p))
  chartJCV sm ins i = jContinuous (Chart.chartPoint i Fixed.p)
    (λ n → Chart.chartPoint i (point n)) (dropCV start (chartCV i)) (sm i) (ins i)
