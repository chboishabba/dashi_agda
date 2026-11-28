module DASHI.Moonshine.JInvariantBishopThetaSignedReadoutExact where

-- Source-written, kernel pending. The original weighted integer rows
-- on the actual two Machin half-phases. No extra analytic theta carrier.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_)
import Data.Integer as Z
open import Relation.Binary.PropositionalEquality using (sym; trans)
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
module ZSolver = +-*-Solver
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _⋆; _*_; _+_; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopThetaCoefficientEvaluationExact as E
import DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact as T
import DASHI.Moonshine.JInvariantThetaIntegerTwistExact as ZT
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as D
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; scaleC; powC)
open Comp using (complexTrans; complexSym)

scaleCong : ∀ {a b z w} → a ≃ b → z ≈C w → scaleC a z ≈C scaleC b w
scaleCong h (r , i) = P.*-cong h r , P.*-cong h i

scaleNest : ∀ a b z → scaleC a (scaleC b z) ≈C scaleC (a * b) z
scaleNest a b (C.complex x y) = P.≃-symm (P.*-assoc a b x) , P.≃-symm (P.*-assoc a b y)

scaleMinus : ∀ z → D.negC z ≈C scaleC (I.embed (- (+ 1))) z
scaleMinus (C.complex x y) =
  (let open P.ℝ-Solver in solve 1 (λ x → ⊝ x ⊜ Κ (- (+ 1) / 1) ⊗ x) P.≃-refl x) ,
  (let open P.ℝ-Solver in solve 1 (λ x → ⊝ x ⊜ Κ (- (+ 1) / 1) ⊗ x) P.≃-refl y)

signedPower : ∀ t n → powC (D.negC t) n ≈C scaleC (I.embed (T.sign n)) (powC t n)
signedPower t zero = complexSym (P.*-identityˡ R.1ℝ , P.*-identityˡ R.0ℝ)
signedPower t (suc n) =
  complexTrans (A.mulCCongruent (scaleMinus t) (signedPower t n))
    (complexTrans (CP.scaleProduct (I.embed (- (+ 1))) (I.embed (T.sign n)) t (powC t n))
      (scaleCong (P.≃-trans (P.≃-symm (I.embedMul (- (+ 1)) (T.sign n)))
        (I.embedCong (sym (ZT.signStep n)))) (C.≈C-refl _)))

twistedWeight : ∀ t f n → CP.weight (D.negC t) f n ≈C CP.weight t (ZT.twist f) n
twistedWeight t f n =
  complexTrans (A.scaleCCongruent (signedPower t n) (I.embed (f n)))
    (complexTrans (scaleNest (I.embed (f n)) (I.embed (T.sign n)) (powC t n))
      (scaleCong (P.≃-trans (P.*-comm (I.embed (f n)) (I.embed (T.sign n)))
        (P.≃-symm (I.embedMul (T.sign n) (f n)))) (C.≈C-refl _)))

coeffTransport : ∀ {t f g} → (∀ n → f n ≡ g n) → CP.Readout t f → CP.Readout t g
coeffTransport {t} {f} {g} h x =
  let eq : ∀ n → CP.weight t f n ≈C CP.weight t g n
      eq n = scaleCong (I.embedCong (h n)) (C.≈C-refl _)
  in record { value = CP.value x
            ; absolute = CP.complexAbsTransport eq (CP.absolute x)
            ; converges = CP.complexLimitTransport eq (CP.converges x) }

negativeReadout : ∀ {t u f} → u ≈C D.negC t → CP.Readout u f → CP.Readout t (ZT.twist f)
negativeReadout {t} {u} {f} h x =
  let eq : ∀ n → CP.weight u f n ≈C CP.weight t (ZT.twist f) n
      eq n = complexTrans (A.scaleCCongruent (A.powCCongruent h n) (I.embed (f n)))
        (twistedWeight t f n)
  in record { value = CP.value x
            ; absolute = CP.complexAbsTransport eq (CP.absolute x)
            ; converges = CP.complexLimitTransport eq (CP.converges x) }

-- A finite support series is absolutely convergent by comparison on
-- its zero tail; its actual limit follows by the shifted subsequence.
zeroPrefix : ∀ n → S.SeriesOf (λ _ → R.0ℝ) n ≃ R.0ℝ
zeroPrefix zero = P.≃-refl
zeroPrefix (suc n) = P.≃-trans (P.+-cong (zeroPrefix n) P.≃-refl) (P.+-identityʳ R.0ℝ)

zeroConvergent : S._isConvergent (S.SeriesOf (λ _ → R.0ℝ))
zeroConvergent = R.0ℝ , S.xₙ≃c⇒xₙ→c (λ {(suc n) → zeroPrefix (suc n)})

spike : ℝ → Nat → ℝ
spike x zero = R.0ℝ
spike x (suc zero) = x
spike x (suc (suc n)) = R.0ℝ

spikeAbs : ∀ x → S.SeriesOf_ConvergesAbsolutely (spike x)
spikeAbs x = S.proposition-3-5 zeroConvergent
  (2 , λ { zero () ; (suc zero) () ; (suc (suc n)) h →
    P.≤-reflexive (P.nonNegx⇒∣x∣≃x (P.0≤x⇒nonNegx P.≤-refl)) })

spikePrefix : ∀ x n → S.SeriesOf (spike x) (suc (suc n)) ≃ x
spikePrefix x zero = P.≃-trans (P.+-cong (P.+-identityʳ R.0ℝ) P.≃-refl) (P.+-identityˡ x)
spikePrefix x (suc n) = P.≃-trans (P.+-cong (spikePrefix x n) P.≃-refl) (P.+-identityʳ x)

spikeConv : ∀ x → S._ConvergesTo_ (S.SeriesOf (spike x)) x
spikeConv x =
  let h = S.absolute⇒isConvergent (spikeAbs x)
      shifted = S.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
        (S.shift-is-subsequence (S.SeriesOf (spike x)) 2) h
      constant = S.xₙ≃c⇒xₙ→c (λ {(suc n) → spikePrefix x (suc n)})
  in S.xₙ→x∧x≃y⇒xₙ→y (proj₂ h) (S.uniqueness-of-limits shifted constant)

zeroScale : ∀ z → scaleC (I.embed (+ 0)) z ≈C A.zeroC
zeroScale (C.complex x y) = P.*-zeroˡ x , P.*-zeroˡ y

monoTerm : ∀ t n → C.complex (spike (C.re (scaleC (I.embed (+ 16)) t)) n)
  (spike (C.im (scaleC (I.embed (+ 16)) t)) n) ≈C CP.weight t ZT.mono16 n
monoTerm t zero = complexSym (zeroScale _)
monoTerm t (suc zero) = A.scaleCCongruent (complexSym (Laws.complexMultiplyRightIdentity t)) (I.embed (+ 16))
monoTerm t (suc (suc n)) = complexSym (zeroScale _)

monoReadout : ∀ t → CP.Readout t ZT.mono16
monoReadout t =
  let v = scaleC (I.embed (+ 16)) t
      abs = C.componentwise-absolute-series-convergent (spikeAbs (C.re v)) (spikeAbs (C.im v))
      cv = C.complex-series-converges-to (spikeConv (C.re v)) (spikeConv (C.im v))
  in record { value = v ; absolute = CP.complexAbsTransport (monoTerm t) abs
            ; converges = CP.complexLimitTransport (monoTerm t) cv }

sumTerm : ∀ t f g n → (CP.weight t f n +C CP.weight t g n) ≈C CP.weight t (T.add f g) n
sumTerm t f g n =
  let a = I.embed (f n); b = I.embed (g n); x = C.re (powC t n); y = C.im (powC t n)
      h = P.≃-symm (I.embedAdd (f n) (g n))
  in P.≃-trans (P.≃-symm (P.*-distribʳ-+ x a b)) (P.*-congʳ h) ,
     P.≃-trans (P.≃-symm (P.*-distribʳ-+ y a b)) (P.*-congʳ h)


-- All subsequent evaluations retain the original integer coefficient
-- history. The signed subtraction is reflected, not approximated.
negEmbed : ∀ a → I.embed (Z.- a) ≃ R.- (I.embed a)
negEmbed a =
  P.≃-trans (I.embedCong (sym (negativeOneTimes a)))
    (P.≃-trans (I.embedMul (- (+ 1)) a)
      (let open P.ℝ-Solver in solve 1
        (λ x → Κ (- (+ 1) / 1) ⊗ x ⊜ ⊝ x) P.≃-refl (I.embed a)))
  where
  negativeOneTimes : ∀ a → Z._*_ (- (+ 1)) a ≡ Z.- a
  negativeOneTimes a =
    let open ZSolver in
    trans
      (solve 1 (λ x → con (- (+ 1)) :* x := con (+ 0) :- x) refl a)
      (ZP.+-identityˡ (Z.- a))

subTerm : ∀ t f g n → (CP.weight t f n -C CP.weight t g n) ≈C CP.weight t (T.sub f g) n
subTerm t f g n =
  let a = I.embed (f n); b = I.embed (g n); x = C.re (powC t n); y = C.im (powC t n)
      h = P.≃-symm (P.≃-trans (I.embedAdd (f n) (Z.- g n))
        (P.+-cong P.≃-refl (negEmbed (g n))))
      algebra : ∀ z → R._-_ (a * z) (b * z) ≃ (R._-_ a b) * z
      algebra z = let open P.ℝ-Solver in solve 3
        (λ a b z → (a ⊗ z) ⊖ (b ⊗ z) ⊜ (a ⊖ b) ⊗ z) P.≃-refl a b z
  in P.≃-trans (algebra x) (P.*-congʳ h) ,
     P.≃-trans (algebra y) (P.*-congʳ h)

plusReadout : ∀ {t f g} → CP.Readout t f → CP.Readout t g → CP.Readout t (T.add f g)
plusReadout {t} {f} {g} x y =
  let a = CP.absolute x; b = CP.absolute y
      c = CP.converges x; d = CP.converges y
      ab = C.componentwise-absolute-series-convergent
        (CP.plusAbs _ _ (C.realAbsolute a) (C.realAbsolute b))
        (CP.plusAbs _ _ (C.imagAbsolute a) (C.imagAbsolute b))
      cv = C.complex-series-converges-to
        (CP.plusConv (C.realConverges c) (C.realConverges d))
        (CP.plusConv (C.imagConverges c) (C.imagConverges d))
  in record { value = CP.value x +C CP.value y
            ; absolute = CP.complexAbsTransport (sumTerm t f g) ab
            ; converges = CP.complexLimitTransport (sumTerm t f g) cv }

minusReadout : ∀ {t f g} → CP.Readout t f → CP.Readout t g → CP.Readout t (T.sub f g)
minusReadout {t} {f} {g} x y =
  let a = CP.absolute x; b = CP.absolute y
      c = CP.converges x; d = CP.converges y
      ab = C.componentwise-absolute-series-convergent
        (CP.minusAbs _ _ (C.realAbsolute a) (C.realAbsolute b))
        (CP.minusAbs _ _ (C.imagAbsolute a) (C.imagAbsolute b))
      cv = C.complex-series-converges-to
        (CP.minusConv (C.realConverges c) (C.realConverges d))
        (CP.minusConv (C.imagConverges c) (C.imagConverges d))
  in record { value = CP.value x -C CP.value y
            ; absolute = CP.complexAbsTransport (subTerm t f g) ab
            ; converges = CP.complexLimitTransport (subTerm t f g) cv }

sameReadout : ∀ {t f} → (x y : CP.Readout t f) → CP.value x ≈C CP.value y
sameReadout {t} {f} x y = complexTrans
  (complexSym (C.complexSeriesLimitUnique (CP.weight t f) (CP.absolute x) (CP.value x) (CP.converges x)))
  (C.complexSeriesLimitUnique (CP.weight t f) (CP.absolute x) (CP.value y) (CP.converges y))

module At (inputs : Round11.BishopCutset) (p : U.BishopUpperHalfPlanePoint) where
  module S0 = E.At inputs p
  t = S0.t
  Aread : CP.Readout t T.A
  Aread = coeffTransport ZT.aRead (CP.product (monoReadout t) S0.positiveH4)

  Bread : CP.Readout t T.B
  Bread = S0.positiveB

  Cread : CP.Readout t T.C
  Cread = coeffTransport (λ n → sym (ZT.negativeSheet n))
    (negativeReadout (S0.Rw.signedQ Phase.positive p) S0.negativeB)

  a b c : BishopComplex
  a = CP.value Aread
  b = CP.value Bread
  c = CP.value Cread

  -- Actual values on the original integer row. The only premise is
  -- the all-index arithmetic Jacobi identity on precisely these rows.
  jacobiFromCoefficients : (∀ n → T.B n ≡ T.add T.A T.C n) → b ≈C (a +C c)
  jacobiFromCoefficients h =
    sameReadout (coeffTransport h Bread) (plusReadout Aread Cread)

  -- Q, W and V on the original half-phase, with unconditional
  -- absolute convergence and evaluation of their literal histories.
  Qread : CP.Readout t T.qTheta
  Qread = plusReadout
    (minusReadout (CP.product Aread Aread) (CP.product Aread Bread))
    (CP.product Bread Bread)

  Wread : CP.Readout t T.wTheta
  Wread = CP.product
    (CP.product (plusReadout Aread Bread) (minusReadout (plusReadout Aread Aread) Bread))
    (minusReadout Aread (plusReadout Bread Bread))

  Vread : CP.Readout t T.vTheta
  Vread = CP.product (CP.product Aread Bread) (minusReadout Bread Aread)
