module DASHI.Moonshine.JInvariantBishopEisensteinEulerJetExact where

-- SOURCE-WRITTEN, not kernel checked. All-order weighted coefficient
-- series of the ORIGINAL E4/E6. Analytic differentiation of their
-- limits is a separate obligation, not inferred from convergence alone.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Product.Base using (_,_)
import Real as R
import RealProperties as P
import Sequence as S
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Poly
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as M

indexPower : Nat → Nat → R.ℝ
indexPower d n = R.pow (N.natReal (suc n)) d

indexPowerNN : (d n : Nat) → R.NonNegative (indexPower d n)
indexPowerNN d n = S.nonNegx⇒nonNegxⁿ d (Poly.natRealNonnegative (suc n))

-- Retain source degree d and index n separately.
e4JetTerm : C.BishopComplex → Nat → Nat → C.BishopComplex
e4JetTerm q d n = A.scaleC (indexPower d n) (E.e4BishopTerm q n)

e6UnsignedJetTerm : C.BishopComplex → Nat → Nat → C.BishopComplex
e6UnsignedJetTerm q d n =
  A.scaleC (indexPower d n) (E.e6BishopUnsignedTerm q n)

powAdd : (x : R.ℝ) (d b : Nat) →
  R._≃_ (R._*_ (R.pow x d) (R.pow x b)) (R.pow x (d + b))
powAdd x zero b = P.*-identityˡ (R.pow x b)
powAdd x (suc d) b =
  let open P.ℝ-Solver in
  P.≃-trans
    (solve 3 (λ u v w → (u ⊗ w) ⊗ v ⊜ (u ⊗ v) ⊗ w)
      P.≃-refl (R.pow x d) (R.pow x b) x)
    (P.*-cong (powAdd x d b) P.≃-refl)

jetMajorant : R.ℝ → R.ℝ → Nat → Nat → Nat → R.ℝ
jetMajorant scale r b d =
  Poly.shiftedScaledPolynomialGeometricTerm scale r (d + b)

jetMajorantMeaning : (scale r : R.ℝ) (b d n : Nat) →
  R._≃_ (R._*_ (indexPower d n)
    (Poly.shiftedScaledPolynomialGeometricTerm scale r b n))
    (jetMajorant scale r b d n)
jetMajorantMeaning scale r b d n =
  let
    x = N.natReal (suc n)
    u = R.pow x d
    v = R.pow x b
    w = R.pow r (suc n)
    open P.ℝ-Solver
  in P.≃-trans
    (solve 4 (λ u v w s → u ⊗ (s ⊗ (v ⊗ w)) ⊜ s ⊗ ((u ⊗ v) ⊗ w))
      P.≃-refl u v w scale)
    (P.*-cong P.≃-refl (P.*-cong (powAdd x d b) P.≃-refl))

-- This consumes the literal E4/E6 component envelope, not an invented
-- coefficient sequence. The stronger polynomial degree pays all jets.
weightedComponentBound : ∀ {scale r : R.ℝ} {b : Nat} →
  (unit : Unit.BishopUnitIntervalRatio r) →
  R.NonNegative scale →
  (component : R.ℝ) → (d n : Nat) →
  R._≤_ (R.∣ component ∣)
    (Poly.shiftedScaledPolynomialGeometricTerm scale r b n) →
  R._≤_ (R.∣ R._*_ (indexPower d n) component ∣)
    (jetMajorant scale r b d n)
weightedComponentBound {scale} {r} {b} unit nn component d n bound =
  P.≤-respʳ-≃ (jetMajorantMeaning scale r b d n)
    (E.scaledComponentAbsoluteBound
      (indexPowerNN d n)
      (Poly.shiftedScaledPolynomialGeometricTermNonnegative
        (Unit.ratioNonnegative unit) nn b n)
      P.≤-refl bound)

jetMajorantAbsolute : ∀ {r scale} →
  Unit.BishopUnitIntervalRatio r → R.NonNegative scale →
  (b d : Nat) →
  S.SeriesOf_ConvergesAbsolutely (jetMajorant scale r b d)
jetMajorantAbsolute {r} {scale} unit nn b d =
  Poly.shiftedScaledPolynomialGeometricSeriesAbsolutelyConvergent
    r scale (d + b) (Unit.ratioNonnegative unit)
    (Unit.ratioBelowOne unit) nn

module AtDisk {q : C.BishopComplex} {r : R.ℝ}
  (input : Disk.BishopUnitDiskQ q r) where

  unit = Disk.unitInterval input
  envelope = Disk.powerEnvelope input

  e4JetAbsolute : (d : Nat) →
    C.ComponentwiseAbsoluteSeriesConvergent (e4JetTerm q d)
  e4JetAbsolute d =
    C.componentwise-absolute-series-convergent
      (E.absoluteSeriesFromMajorant (C.realTerms (e4JetTerm q d))
        (jetMajorant M.e4Scale r 4 d)
        (jetMajorantAbsolute unit M.e4ScaleNonnegative 4 d)
        (λ n → weightedComponentBound unit M.e4ScaleNonnegative
          (C.re (E.e4BishopTerm q n)) d n
          (E.e4RealTermBound q unit envelope n)))
      (E.absoluteSeriesFromMajorant (C.imagTerms (e4JetTerm q d))
        (jetMajorant M.e4Scale r 4 d)
        (jetMajorantAbsolute unit M.e4ScaleNonnegative 4 d)
        (λ n → weightedComponentBound unit M.e4ScaleNonnegative
          (C.im (E.e4BishopTerm q n)) d n
          (E.e4ImagTermBound q unit envelope n)))

  e6UnsignedJetAbsolute : (d : Nat) →
    C.ComponentwiseAbsoluteSeriesConvergent (e6UnsignedJetTerm q d)
  e6UnsignedJetAbsolute d =
    C.componentwise-absolute-series-convergent
      (E.absoluteSeriesFromMajorant (C.realTerms (e6UnsignedJetTerm q d))
        (jetMajorant M.e6Scale r 6 d)
        (jetMajorantAbsolute unit M.e6ScaleNonnegative 6 d)
        (λ n → weightedComponentBound unit M.e6ScaleNonnegative
          (C.re (E.e6BishopUnsignedTerm q n)) d n
          (E.e6RealTermBound q unit envelope n)))
      (E.absoluteSeriesFromMajorant (C.imagTerms (e6UnsignedJetTerm q d))
        (jetMajorant M.e6Scale r 6 d)
        (jetMajorantAbsolute unit M.e6ScaleNonnegative 6 d)
        (λ n → weightedComponentBound unit M.e6ScaleNonnegative
          (C.im (E.e6BishopUnsignedTerm q n)) d n
          (E.e6ImagTermBound q unit envelope n)))

  e4TailJet : Nat → C.BishopComplex
  e4TailJet d = C.complexSeriesLimit (e4JetTerm q d) (e4JetAbsolute d)

  e6UnsignedTailJet : Nat → C.BishopComplex
  e6UnsignedTailJet d =
    C.complexSeriesLimit (e6UnsignedJetTerm q d) (e6UnsignedJetAbsolute d)

  e4JetConverges : (d : Nat) →
    C.ComplexSeriesConvergesTo (e4JetTerm q d) (e4TailJet d)
  e4JetConverges d =
    C.complexSeriesLimitConvergence (e4JetTerm q d) (e4JetAbsolute d)

  e6UnsignedJetConverges : (d : Nat) →
    C.ComplexSeriesConvergesTo (e6UnsignedJetTerm q d) (e6UnsignedTailJet d)
  e6UnsignedJetConverges d =
    C.complexSeriesLimitConvergence (e6UnsignedJetTerm q d) (e6UnsignedJetAbsolute d)

  -- Degree zero retains the actual completed normalized forms.
  -- Positive degrees have no constant term, and E6 keeps its minus sign.
  e4EulerJet : Nat → C.BishopComplex
  e4EulerJet zero = Disk.e4Limit (Disk.completeBishopUnitDiskEisenstein input)
  e4EulerJet (suc d) = e4TailJet (suc d)

  e6EulerJet : Nat → C.BishopComplex
  e6EulerJet zero = Disk.e6Limit (Disk.completeBishopUnitDiskEisenstein input)
  e6EulerJet (suc d) = A._-C_ A.zeroC (e6UnsignedTailJet (suc d))
