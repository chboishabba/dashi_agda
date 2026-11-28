module DASHI.Moonshine.CM163BishopHecke41ReciprocalRayCoordinateExact where

-- R1 native original CM ray, SOURCE-WRITTEN KERNEL PENDING.
-- Use the existing Basel reciprocal real sequence h=1/(n+1).
-- tau(h)=tau_*+d*h, d=tau_*-conjugate(tau_*), and w=h/(1+h).
-- Therefore tau(h)=tau_*+d*w/(1-w) without dividing by the
-- vanishing displacement, and the first and second disk coefficients
-- of tau are BOTH d. All witnesses are on the original Bishop carrier.

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
open import Data.Integer.Base using (+_; -_)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as Apart
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact as Eps
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Const
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopNatRealPositiveExact as Pos
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163ReciprocalGeometryExact as Geo
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Literal
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open R using (_+_; _-_; _*_; _⋆)
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_)
open Comp using (complexTrans; complexSym)

h : Nat → R.ℝ
h = Basel.reciprocalSequence

hPositive : ∀ n → R._<_ R.0ℝ (h n)
hPositive n = P.posx⇒0<x (Eps.reciprocalNatPositive n)

hC : Nat → BishopComplex
hC n = Poly.realC (h n)

hCV : Lim.Conv hC A.zeroC
hCV = Completion.original-bishop-pointwise-complex-converges
  Basel.reciprocalSequenceConvergesZero (Const.constantConverges R.0ℝ)

hNZ : ∀ n → Rec.BishopComplexNonzero (hC n)
hNZ n = Apart.complexNonzeroFromRealApart (inj₂ (hPositive n))

positiveSum : ∀ {x y} → R._<_ R.0ℝ x → R._<_ R.0ℝ y → R._<_ R.0ℝ (x + y)
positiveSum a b = P.posx⇒0<x (P.posx,y⇒posx+y (P.0<x⇒posx a) (P.0<x⇒posx b))

positiveMul : ∀ {x y} → R._<_ R.0ℝ x → R._<_ R.0ℝ y → R._<_ R.0ℝ (x * y)
positiveMul a b = P.posx⇒0<x (P.posx,y⇒posx*y (P.0<x⇒posx a) (P.0<x⇒posx b))

den : Nat → BishopComplex
den n = A.oneC +C hC n

denNZ : ∀ n → Rec.BishopComplexNonzero (den n)
denNZ n = Apart.complexNonzeroFromRealApart
  (inj₂ (positiveSum (Pos.natRealSuccessorStrictlyPositive 0) (hPositive n)))

denCV : Lim.Conv den A.oneC
denCV = Lim.limitTransport (L.complexAddRightIdentity A.oneC)
  (Lim.addConv (Lim.constantC A.oneC) hCV)

inv : Nat → BishopComplex
inv n = Rec.reciprocalC (den n) (denNZ n)

invCV : Lim.Conv inv (Rec.reciprocalC A.oneC Cancel.nonzeroOne)
invCV = Conv.inverseLimit Cancel.nonzeroOne denCV
  (λ n → Rec.multiplyReciprocal (den n) (denNZ n))

w : Nat → BishopComplex
w n = Cancel.quot (hC n) (den n) (denNZ n)

wNZ : ∀ n → Rec.BishopComplexNonzero (w n)
wNZ n = Cancel.nonzeroMul (hNZ n)
  (record { Rec.normSquarePositive = Rec.reciprocalNormSquarePositive (den n) (denNZ n) })

wCV : Lim.Conv w A.zeroC
wCV = Lim.limitTransport (L.complexMultiplyLeftZero _)
  (Conv.mulConv hCV invCV)

denTimesW : ∀ n → (den n *C w n) ≈C hC n
denTimesW n = Cancel.clearQuot (hC n) (den n) (denNZ n)

-- Explicit positive vertical ray through the original selected point.
dImag : R.ℝ
dImag = CM.imag + CM.imag

d : BishopComplex
d = C.complex R.0ℝ dImag

dImagPositive : R._<_ R.0ℝ dImag
dImagPositive = positiveSum CM.imagPositive CM.imagPositive

dNZ : Rec.BishopComplexNonzero d
dNZ = Apart.complexNonzeroFromImagApart (inj₂ dImagPositive)

dRead : (Geo.tau -C Geo.tauBar) ≈C d
dRead =
  (let open P.ℝ-Solver in solve 0
    (Κ ((- (+ 1)) / 2) ⊖ Κ ((- (+ 1)) / 2) ⊜ Κ 0ℚᵘ) P.≃-refl) ,
  (let open P.ℝ-Solver in solve 1
    (λ r → Κ (+ 1 / 2) ⊗ r ⊖ Κ ((- (+ 1)) / 2) ⊗ r
      ⊜ (Κ (+ 1 / 2) ⊗ r) ⊕ (Κ (+ 1 / 2) ⊗ r)) P.≃-refl Geo.N.r)

ray : Nat → U.BishopUpperHalfPlanePoint
ray n = U.bishop-upper-half-plane-point
  (C.complex (C.re Geo.tau) (CM.imag + dImag * h n))
  (positiveSum CM.imagPositive (positiveMul dImagPositive (hPositive n)))

tauRead : ∀ n → U.tau (ray n) ≈C (Geo.tau +C d *C hC n)
tauRead n =
  (let open P.ℝ-Solver in solve 3
    (λ x y h → x ⊜ x ⊕ ((Κ 0ℚᵘ ⊗ h) ⊖ (y ⊗ Κ 0ℚᵘ)))
    P.≃-refl (C.re Geo.tau) dImag (h n)) ,
  (let open P.ℝ-Solver in solve 3
    (λ x y h → x ⊕ y ⊗ h ⊜ x ⊕ ((Κ 0ℚᵘ ⊗ Κ 0ℚᵘ) ⊕ (y ⊗ h)))
    P.≃-refl CM.imag dImag (h n))

tauCV : Lim.Conv (λ n → U.tau (ray n)) Geo.tau
tauCV = Lim.convTransport (λ n → complexSym (tauRead n))
  (Lim.limitTransport (L.complexAddRightIdentity Geo.tau)
    (Lim.addConv (Lim.constantC Geo.tau)
      (Lim.limitTransport (L.complexMultiplyRightZero d) (Lim.mulConst d hCV))))

diskSlope : Nat → BishopComplex
diskSlope n = d *C den n

diskSlopeCV : Lim.Conv diskSlope d
diskSlopeCV = Lim.limitTransport (L.complexMultiplyRightIdentity d) (Lim.mulConst d denCV)

-- The same quotient generates both first and second jets.  No
-- inverse of w or cancellation of a zero increment is used.
factorRead : ∀ n → (d *C hC n) ≈C (w n *C diskSlope n)
factorRead n = complexTrans
  (A.mulCCongruent (C.≈C-refl _) (complexSym (denTimesW n)))
  (complexTrans (complexSym (L.complexMultiplyAssociative d (den n) (w n)))
    (L.complexMultiplyCommutative (diskSlope n) (w n)))

firstJet : J.Jet w (λ n → U.tau (ray n)) Geo.tau d
firstJet = record
  { J.quotient = diskSlope
  ; J.factor = λ n → complexTrans (A.subCCongruent (tauRead n) (C.≈C-refl _))
      (complexTrans (J.subtractHead Geo.tau (d *C hC n)) (factorRead n))
  ; J.limit = diskSlopeCV }

diskSlopeRead : ∀ n → diskSlope n ≈C (d +C d *C hC n)
diskSlopeRead n = complexTrans (L.complexMultiplyDistributesLeft d A.oneC (hC n))
  (A.addCCongruent (L.complexMultiplyRightIdentity d) (C.≈C-refl _))

secondJet : J.Jet w (J.quotient firstJet) d d
secondJet = record
  { J.quotient = diskSlope
  ; J.factor = λ n → complexTrans (A.subCCongruent (diskSlopeRead n) (C.≈C-refl _))
      (complexTrans (J.subtractHead d (d *C hC n)) (factorRead n))
  ; J.limit = diskSlopeCV }

tauJet : J2.Jet2 w (λ n → U.tau (ray n)) Geo.tau d d
tauJet = record { J2.first = firstJet ; J2.second = secondJet }

subtractShift : ∀ a b c → ((a +C b) -C c) ≈C ((a -C c) +C b)
subtractShift a b c =
  (let open P.ℝ-Solver in solve 3 (λ x y z → (x ⊕ y) ⊖ z ⊜ (x ⊖ z) ⊕ y)
    P.≃-refl (C.re a) (C.re b) (C.re c)) ,
  (let open P.ℝ-Solver in solve 3 (λ x y z → (x ⊕ y) ⊖ z ⊜ (x ⊖ z) ⊕ y)
    P.≃-refl (C.im a) (C.im b) (C.im c))

diskDenRead : ∀ n → (U.tau (ray n) -C Geo.tauBar) ≈C diskSlope n
diskDenRead n = complexTrans (A.subCCongruent (tauRead n) (C.≈C-refl _))
  (complexTrans (subtractShift Geo.tau (d *C hC n) Geo.tauBar)
    (complexTrans (A.addCCongruent dRead (C.≈C-refl _))
      (complexSym (diskSlopeRead n))))

diskRead : ∀ n → (U.tau (ray n) -C Geo.tau) ≈C
  (w n *C (U.tau (ray n) -C Geo.tauBar))
diskRead n = complexTrans (J.factor firstJet n)
  (A.mulCCongruent (C.≈C-refl _) (complexSym (diskDenRead n)))

-- A separate, actual real nonzero null test sequence for reverse-slice
-- center extraction. It uses the SAME original reciprocal real.
testY : Nat → R.ℝ
testY n = (Literal.Kq ⋆) + h n

testRead : ∀ n → (Poly.realC (testY n) -C Shift.K) ≈C hC n
testRead n = proj₁ (J.subtractHead Shift.K (hC n)) , P.≃-refl

testNZ : ∀ n → Rec.BishopComplexNonzero (Poly.realC (testY n) -C Shift.K)
testNZ n = Apart.complexNonzeroFromRealApart
  (Apart.apartCongruent (P.≃-symm (proj₁ (testRead n))) (inj₂ (hPositive n)))

testCV : Lim.Conv (λ n → Poly.realC (testY n) -C Shift.K) A.zeroC
testCV = Lim.convTransport (λ n → complexSym (testRead n)) hCV
