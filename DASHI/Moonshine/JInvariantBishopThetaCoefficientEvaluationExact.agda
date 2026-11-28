module DASHI.Moonshine.JInvariantBishopThetaCoefficientEvaluationExact where

-- Source-written, kernel pending. Full coefficient histories, including
-- degree zero, and the actual fourth-power Cauchy products on both
-- original Machin half sheets. The primitive coefficient count is
-- bounded by 2n <= n² for n>=2; no finite-truncation analytic assertion.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (1ℚᵘ)
open import Data.Product.Base using (_,_)
import Real as R
open R using (ℝ; _≃_; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Geo
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopNatEmbeddingMonotoneExact as Mono
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Rad
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact as T
import DASHI.Moonshine.JInvariantBishopThetaDiskExact as TD
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; scaleC)

coefNat : Nat → (Nat → Nat) → Nat → Nat
coefNat c f zero = 1
coefNat c f (suc n) = c * T.count f (suc n) (suc n)

coef : Nat → (Nat → Nat) → I.SeriesZ
coef c f n = + coefNat c f n

theta3Read : ∀ n → coef 2 T.sqN n ≡ T.theta3 n
theta3Read zero = refl
theta3Read (suc n) = refl

halfRead : ∀ n → coef 1 T.triN n ≡ T.halfTheta n
halfRead zero = refl
halfRead (suc n) = lift (NP.*-identityˡ (T.count T.triN (suc n) (suc n)))
  where lift : ∀ {a b : Nat} → a ≡ b → (+ a) ≡ (+ b)
        lift refl = refl

module OnDisk (t : BishopComplex) (r : ℝ) (disk : Disk.BishopUnitDiskQ t r) where
  unit = Disk.unitInterval disk
  envelope = Disk.powerEnvelope disk

  budget : Nat → ℝ
  budget = Geo.polynomialGeometricTerm r 2

  budgetConverges = Geo.polynomialGeometricSeriesConvergent r 2
    (Unit.ratioNonnegative unit) (Unit.ratioBelowOne unit)

  coeffBound : ∀ c f → c ≤ 2 → f zero ≡ zero → ∀ n →
    coefNat c f (suc (suc n)) ≤ suc (suc n) * suc (suc n)
  coeffBound c f hc hf n =
    NP.≤-trans (NP.*-mono-≤ hc (TD.countPositive f hf (suc n) (suc (suc n))))
      (NP.*-mono-≤ (s≤s (s≤s z≤n)) NP.≤-refl)

  coeffRealBound : ∀ c f → c ≤ 2 → f zero ≡ zero → ∀ n →
    R._≤_ (I.embed (coef c f (suc (suc n)))) (R.pow (NR.natReal (suc (suc n))) 2)
  coeffRealBound c f hc hf n =
    P.≤-respʳ-≃
      (P.≃-trans (NR.natRealMul (suc (suc n)) (suc (suc n)))
        (let open P.ℝ-Solver in solve 1 (λ x → x ⊗ x ⊜ (Κ 1ℚᵘ ⊗ x) ⊗ x)
          P.≃-refl (NR.natReal (suc (suc n)))))
      (Mono.natRealMonotone (coeffBound c f hc hf n))

  reBound : ∀ c f → c ≤ 2 → f zero ≡ zero → ∀ n → 2 ≤ n →
    R._≤_ ∣ C.re (CP.weight t (coef c f) n) ∣ (budget n)
  reBound c f hc hf zero ()
  reBound c f hc hf (suc zero) ()
  reBound c f hc hf (suc (suc n)) h =
    E.scaledComponentAbsoluteBound (Geo.natRealNonnegative _) (Unit.ratioPowerNonnegative unit _)
      (coeffRealBound c f hc hf n) (Norm.realPowerBound envelope (suc n))

  imBound : ∀ c f → c ≤ 2 → f zero ≡ zero → ∀ n → 2 ≤ n →
    R._≤_ ∣ C.im (CP.weight t (coef c f) n) ∣ (budget n)
  imBound c f hc hf zero ()
  imBound c f hc hf (suc zero) ()
  imBound c f hc hf (suc (suc n)) h =
    E.scaledComponentAbsoluteBound (Geo.natRealNonnegative _) (Unit.ratioPowerNonnegative unit _)
      (coeffRealBound c f hc hf n) (Norm.imagPowerBound envelope (suc n))

  primitiveAbsolute : ∀ c f → c ≤ 2 → f zero ≡ zero →
    C.ComponentwiseAbsoluteSeriesConvergent (CP.weight t (coef c f))
  primitiveAbsolute c f hc hf = C.componentwise-absolute-series-convergent
    (S.proposition-3-5 budgetConverges (2 , λ n h → P.≤-respˡ-≃
      (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _)) (reBound c f hc hf n h)))
    (S.proposition-3-5 budgetConverges (2 , λ n h → P.≤-respˡ-≃
      (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _)) (imBound c f hc hf n h)))

  primitive : ∀ c f → c ≤ 2 → f zero ≡ zero → CP.Readout t (coef c f)
  primitive c f hc hf =
    let h = primitiveAbsolute c f hc hf
    in record { value = C.complexSeriesLimit _ h ; absolute = h
              ; converges = C.complexSeriesLimitConvergence _ h }

  transport : ∀ {f g : I.SeriesZ} → (∀ n → f n ≡ g n) →
    CP.Readout t f → CP.Readout t g
  transport {f} {g} h x =
    let eq : ∀ n → CP.weight t f n ≈C CP.weight t g n
        eq n rewrite h n = C.≈C-refl _
    in record { value = CP.value x
              ; absolute = CP.complexAbsTransport eq (CP.absolute x)
              ; converges = CP.complexLimitTransport eq (CP.converges x) }

  theta3 : CP.Readout t T.theta3
  theta3 = transport theta3Read (primitive 2 T.sqN NP.≤-refl refl)

  halfTheta : CP.Readout t T.halfTheta
  halfTheta = transport halfRead (primitive 1 T.triN (s≤s z≤n) refl)

  B : CP.Readout t T.B
  B = CP.fourth theta3

  H4 : CP.Readout t (T.fourth T.halfTheta)
  H4 = CP.fourth halfTheta

module At (inputs : Round11.BishopCutset) (p : U.BishopUpperHalfPlanePoint) where
  module Rw = D.At inputs
  t = Rw.q (D.left p)
  tMinus = Rw.q (D.right D.positive p)
  module Plus = OnDisk t (Rad.machinQRadius (C.im (U.tau (D.left p)))) (Rw.disk (D.left p))
  module Minus = OnDisk tMinus (Rad.machinQRadius (C.im (U.tau (D.right D.positive p)))) (Rw.disk (D.right D.positive p))

  positiveB = Plus.B
  negativeB = Minus.B
  positiveH4 = Plus.H4

  a : BishopComplex
  a = scaleC (NR.natReal 16) (t *C CP.value positiveH4)
  b c : BishopComplex
  b = CP.value positiveB
  c = CP.value negativeB

  square : (t *C t) ≈C Rw.q p
  square = Rw.squareQ p

  -- The remaining coefficient transport is the single monomial shift
  -- on H4 and the (-1)^n twist on negativeB. The existing Cauchy
  -- product now evaluates B and H4 on the actual full coefficient
  -- streams; this is not yet Jacobi or analytic modular uniqueness.
