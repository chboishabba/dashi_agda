module DASHI.Moonshine.JInvariantBishopThetaDiskExact where

-- Original theta exponent counts evaluated on the actual Bishop
-- complex disk. No Jacobi identity or modular-form uniqueness assumed.
-- Classical theta definitions; DASHI original-carrier convergence weld.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Relation.Nullary using (yes; no)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _*_; _⋆; ∣_∣)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Geo
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopNatEmbeddingMonotoneExact as Mono
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Rad
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact as T
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; _-C_; powC; scaleC)

-- The zero coordinate cannot contribute to a positive degree.
-- Counting the remaining k candidate magnitudes gives a linear
-- envelope without needing an independent square-root algorithm.
countPositive : ∀ f → f zero ≡ zero → ∀ n k → T.count f (suc n) k ≤ k
countPositive f h n zero rewrite h = z≤n
countPositive f h n (suc k) with f (suc k) NP.≟ suc n
... | yes _ = s≤s (countPositive f h n k)
... | no _ = NP.≤-step (countPositive f h n k)

module OnDisk (t : BishopComplex) (r : ℝ) (disk : Disk.BishopUnitDiskQ t r) where
  unit = Disk.unitInterval disk
  envelope = Disk.powerEnvelope disk

  term : (Nat → Nat) → Nat → BishopComplex
  term f n = scaleC (NR.natReal (T.count f (suc n) (suc n))) (powC t (suc n))

  budget : Nat → ℝ
  budget = Geo.shiftedScaledPolynomialGeometricTerm R.1ℝ r 1

  budgetRead : ∀ n → (NR.natReal (suc n) * R.pow r (suc n)) ≃ budget n
  budgetRead n = let open P.ℝ-Solver in
    solve 2 (λ n r → n ⊗ r ⊜ Κ 1ℚᵘ ⊗ ((Κ 1ℚᵘ ⊗ n) ⊗ r))
      P.≃-refl (NR.natReal (suc n)) (R.pow r (suc n))

  budgetAbs = Geo.shiftedScaledPolynomialGeometricSeriesAbsolutelyConvergent
    r R.1ℝ 1 (Unit.ratioNonnegative unit) (Unit.ratioBelowOne unit)
      (Geo.natRealNonnegative 1)

  coefficientBound : ∀ f → f zero ≡ zero → ∀ n →
    R._≤_ (NR.natReal (T.count f (suc n) (suc n))) (NR.natReal (suc n))
  coefficientBound f h n = Mono.natRealMonotone (countPositive f h n (suc n))

  reBound : ∀ f → f zero ≡ zero → ∀ n → R._≤_ ∣ C.re (term f n) ∣ (budget n)
  reBound f h n = P.≤-respʳ-≃ (budgetRead n)
    (E.scaledComponentAbsoluteBound (Geo.natRealNonnegative _) (Unit.ratioPowerNonnegative unit _)
      (coefficientBound f h n) (Norm.realPowerBound envelope n))

  imBound : ∀ f → f zero ≡ zero → ∀ n → R._≤_ ∣ C.im (term f n) ∣ (budget n)
  imBound f h n = P.≤-respʳ-≃ (budgetRead n)
    (E.scaledComponentAbsoluteBound (Geo.natRealNonnegative _) (Unit.ratioPowerNonnegative unit _)
      (coefficientBound f h n) (Norm.imagPowerBound envelope n))

  absolute : ∀ f → f zero ≡ zero → C.ComponentwiseAbsoluteSeriesConvergent (term f)
  absolute f h = C.componentwise-absolute-series-convergent
    (E.absoluteSeriesFromMajorant (C.realTerms (term f)) budget budgetAbs (reBound f h))
    (E.absoluteSeriesFromMajorant (C.imagTerms (term f)) budget budgetAbs (imBound f h))

  value : ∀ f → f zero ≡ zero → BishopComplex
  value f h = C.complexSeriesLimit (term f) (absolute f h)

  convergence : ∀ f (h : f zero ≡ zero) → C.ComplexSeriesConvergesTo (term f) (value f h)
  convergence f h = C.complexSeriesLimitConvergence (term f) (absolute f h)

  -- theta3=1+2 sum_{n>0} c_n t^n, H=1+sum_{n>0} h_n t^n.
  -- H is theta2/(2*t^(1/4)); we only use the fourth power, so there
  -- is no branch choice or fractional reciprocal at zero.
  theta3 : BishopComplex
  theta3 = A.oneC +C Row.scale 2 (value T.sqN refl)
  H : BishopComplex
  H = A.oneC +C value T.triN refl

  B : BishopComplex
  B = powC theta3 4

  A4 : BishopComplex
  A4 = Row.scale 16 (t *C powC H 4)

module At (inputs : Round11.BishopCutset) (p : U.BishopUpperHalfPlanePoint) where
  module Rw = D.At inputs
  t : BishopComplex
  t = Rw.q (D.left p)
  tMinus : BishopComplex
  tMinus = Rw.q (D.right D.positive p)

  actualSquare : (t *C t) ≈C Rw.q p
  actualSquare = Rw.squareQ p

  actualOpposite : tMinus ≈C Row.negC t
  actualOpposite = Rw.signedQ D.positive p

  module Plus = OnDisk t (Rad.machinQRadius (C.im (U.tau (D.left p)))) (Rw.disk (D.left p))
  module Minus = OnDisk tMinus (Rad.machinQRadius (C.im (U.tau (D.right D.positive p)))) (Rw.disk (D.right D.positive p))

  a b c : BishopComplex
  a = Plus.A4
  b = Plus.B
  c = Minus.B

  -- Both sheets are actual exp values. The two normalizations are
  -- polynomial observations of these same coordinates.
  e4Theta : BishopComplex
  e4Theta = scaleC ((+ 1 / 2) ⋆) ((powC a 2 +C powC b 2) +C powC c 2)
  e6Theta : BishopComplex
  e6Theta = scaleC ((+ 1 / 2) ⋆) (((a +C b) *C (b +C c)) *C (c -C a))

  -- These are not yet identified with the original Eisenstein limits.
  -- Jacobi B=A+C, coefficient Cauchy transport and the all-index
  -- theta/Eisenstein identity are explicit remaining obligations.
