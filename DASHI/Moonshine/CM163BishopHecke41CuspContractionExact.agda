module DASHI.Moonshine.CM163BishopHecke41CuspContractionExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- Constructive rigidity by quantitative Fourier contraction.
-- No supremum attainment, classical maximum modulus, or holomorphy
-- oracle. The two remaining producers are actual strip reduction
-- and the uniform Fourier coefficient bound from the dyadic grid.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂; Σ)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (from-yes)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as PG
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Const
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as Bound
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_*C_)
open Comp using (complexTrans; complexSym)

rho contraction : ℝ
rho = (+ 1 / 6) ⋆
contraction = (+ 4 / 5) ⋆

rhoNN : R.NonNegative rho
rhoNN = P.0≤x⇒nonNegx
  (P.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / 6) (from-yes (0ℚᵘ QP.≤? (+ 1 / 6))))

contractNN : R.NonNegative contraction
contractNN = P.0≤x⇒nonNegx
  (P.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 4 / 5) (from-yes (0ℚᵘ QP.≤? (+ 4 / 5))))

contractLt : R._<_ contraction R.1ℝ
contractLt = P.p<q⇒p⋆<q⋆ (+ 4 / 5) 1ℚᵘ (from-yes ((+ 4 / 5) QP.<? 1ℚᵘ))

-- This bound is used for each signed coordinate (not for an
-- unproved equality of norms). The factor 4 includes BOTH products.
Box : ℝ → BishopComplex → Set
Box M z = ∣ C.re z ∣ ≤ M × ∣ C.im z ∣ ≤ M

boxCong : ∀ {M z w} → z ≈C w → Box M z → Box M w
boxCong eq h = P.≤-respˡ-≃ (P.∣-∣-cong (proj₁ eq)) (proj₁ h) ,
  P.≤-respˡ-≃ (P.∣-∣-cong (proj₂ eq)) (proj₂ h)

geo : Nat → ℝ
geo n = Seq.SeriesOf (λ k → R.pow rho (suc k)) n

-- EXACT finite geometric identity; no limit exchange is required
-- to obtain the universal 1/5 budget for the positive powers.
geoRead : ∀ n → geo n ≃ (((+ 1 / 5) ⋆) * (R.1ℝ - R.pow rho n))
geoRead zero = let open P.ℝ-Solver in solve 0
  (Κ 0ℚᵘ ⊜ Κ (+ 1 / 5) ⊗ (Κ 1ℚᵘ ⊖ Κ 1ℚᵘ)) P.≃-refl
geoRead (suc n) = P.≃-trans (P.+-cong (geoRead n) P.≃-refl)
  (let open P.ℝ-Solver in solve 1 (λ p →
    Κ (+ 1 / 5) ⊗ (Κ 1ℚᵘ ⊖ p) ⊕ p ⊗ Κ (+ 1 / 6)
      ⊜ Κ (+ 1 / 5) ⊗ (Κ 1ℚᵘ ⊖ p ⊗ Κ (+ 1 / 6)))
    P.≃-refl (R.pow rho n))

geoBound : ∀ n → geo n ≤ ((+ 1 / 5) ⋆)
geoBound n =
  let p = R.pow rho n
      nn = Seq.nonNegx⇒nonNegxⁿ n rhoNN
      h = P.+-monoʳ-≤ (R.1ℝ - p) (P.nonNegx⇒0≤x nn)
      subOne = P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 1
        (λ p → p ⊕ (Κ 1ℚᵘ ⊖ p) ⊜ Κ 1ℚᵘ) P.≃-refl p)
        (P.≤-respˡ-≃ (P.+-identityˡ (R.1ℝ - p)) h)
      fifthNN = P.0≤x⇒nonNegx
        (P.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / 5) (from-yes (0ℚᵘ QP.≤? (+ 1 / 5))))
  in P.≤-respˡ-≃ (P.≃-symm (geoRead n))
    (P.≤-respʳ-≃ (P.*-identityʳ ((+ 1 / 5) ⋆))
      (P.*-monoˡ-≤-nonNeg subOne fifthNN))

two four : ℝ
two = (+ 2 / 1) ⋆
four = (+ 4 / 1) ⋆

twoNN : R.NonNegative two
twoNN = PG.natRealNonnegative 2
fourNN : R.NonNegative four
fourNN = PG.natRealNonnegative 4

module Disk (r : BishopComplex) (nz : Rec.BishopComplexNonzero r)
  (f : N.SeriesC) (reference : Eval.Eval r f) (zeroMode : f zero ≈C A.zeroC) where
  module B = Bound.Disk r nz f reference

  -- Coefficients are weighted by the actual reference phase r.
  -- This is precisely what the Laurent projection recovers.
  CoeffBound : ℝ → Set
  CoeffBound M = ∀ n → Box (two * M) (N.twist r f n)

  Small : BishopComplex → Set
  Small q = Upper.BishopComplexNormSquareUpperRadius (Bound.relative q r nz) rho

  termBound : ∀ M → R.NonNegative M → CoeffBound M →
    ∀ q → Small q → ∀ n → Box ((four * M) * R.pow rho n) (N.twist q f n)
  termBound M nn coeff q small n =
    let a = N.twist r f n
        w = A.powC (Bound.relative q r nz) n
        z = N.twist (Bound.relative q r nz) B.refTerms n
        coeffs = coeff n
        h = Bound.productBound (C.re a) (C.im a) (C.re w) (C.im w) (two * M)
          (proj₁ coeffs) (proj₂ coeffs)
        p = R.pow rho n
        read = let open P.ℝ-Solver in solve 2
          (λ p M → (p ⊕ p) ⊗ (Κ (+ 2 / 1) ⊗ M) ⊜ (Κ (+ 4 / 1) ⊗ M) ⊗ p)
          P.≃-refl p M
        hi = P.≤-respʳ-≃ read
          (P.*-monoʳ-≤-nonNeg
            (P.+-mono-≤ (Upper.realPowerUpper small n) (Upper.imagPowerUpper small n))
            (P.nonNegx,y⇒nonNegx*y twoNN nn))
        -- The product bound uses w*a; twist stores a*w.
        eq = complexTrans (L.complexMultiplyCommutative w a) (B.termRead q n)
    in boxCong eq (P.≤-trans (proj₁ h) hi , P.≤-trans (proj₂ h) hi)

  termZero : ∀ q → N.twist q f zero ≈C A.zeroC
  termZero q = complexTrans (A.mulCCongruent zeroMode (C.≈C-refl _))
    (L.complexMultiplyLeftZero _)

  prefixBound : ∀ (g : Nat → ℝ) M → R.NonNegative M →
    g zero ≃ R.0ℝ →
    (∀ n → ∣ g n ∣ ≤ ((four * M) * R.pow rho n)) →
    ∀ n → ∣ Seq.SeriesOf g (suc n) ∣ ≤ ((four * M) * geo n)
  prefixBound g M nn h0 hb zero =
    P.≤-respˡ-≃
      (P.≃-symm (P.≃-trans (P.∣-∣-cong (P.≃-trans (P.+-identityˡ _) h0))
        (P.nonNegx⇒∣x∣≃x P.nonNeg0)))
      (P.≤-respʳ-≃ (P.≃-symm (P.*-zeroʳ (four * M))) P.≤-refl)
  prefixBound g M nn h0 hb (suc n) =
    P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ (Seq.SeriesOf g (suc n)) (g (suc n)))
      (P.≤-respʳ-≃ (P.≃-symm (P.*-distribˡ-+ (four * M) (geo n) (R.pow rho (suc n))))
        (P.+-mono-≤ (prefixBound g M nn h0 hb n) (hb (suc n))))

  coordinate : ∀ g v M → R.NonNegative M → g zero ≃ R.0ℝ →
    (∀ n → ∣ g n ∣ ≤ ((four * M) * R.pow rho n)) →
    Seq._ConvergesTo_ (Seq.SeriesOf g) v → ∣ v ∣ ≤ contraction * M
  coordinate g v M nn h0 hb cv =
    let bound = P.nonNegx,y⇒nonNegx*y fourNN nn
        finish = let open P.ℝ-Solver in solve 1
          (λ M → (Κ (+ 4 / 1) ⊗ M) ⊗ Κ (+ 1 / 5) ⊜ Κ (+ 4 / 5) ⊗ M)
          P.≃-refl M
        each : ∀ n → ∣ Seq.SeriesOf g n ∣ ≤ contraction * M
        each zero = P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x P.nonNeg0))
          (P.nonNegx⇒0≤x (P.nonNegx,y⇒nonNegx*y contractNN nn))
        each (suc n) = P.≤-trans (prefixBound g M nn h0 hb n)
          (P.≤-respʳ-≃ finish (P.*-monoˡ-≤-nonNeg (geoBound n) bound))
    in Seq.xₙ≤y⇒limxₙ≤y each (_ , Seq.∣xₙ∣→∣x₀∣ (v , cv))

  contract : ∀ M → R.NonNegative M → CoeffBound M → ∀ q → Small q →
    (ev : Eval.Eval q f) → Box (contraction * M) (Eval.value ev)
  contract M nn coeff q small ev =
    coordinate (C.realTerms (N.twist q f)) (C.re (Eval.value ev)) M nn
      (proj₁ (termZero q)) (λ n → proj₁ (termBound M nn coeff q small n))
      (C.realConverges (Eval.converges ev)) ,
    coordinate (C.imagTerms (N.twist q f)) (C.im (Eval.value ev)) M nn
      (proj₂ (termZero q)) (λ n → proj₂ (termBound M nn coeff q small n))
      (C.imagConverges (Eval.converges ev))

Point = U.BishopUpperHalfPlanePoint

-- General iteration on a global bound, retaining the same point and
-- the same function at every step. An arbitrary modular invariant
-- cusp-null function is NOT assumed zero: the quantitative shrink
-- is the substantive analytic prerequisite.
module Iterate (F : Point → BishopComplex) where
  Global : ℝ → Set
  Global M = ∀ p → Box M (F p)

  module From (M : ℝ) (nn : R.NonNegative M) (initial : Global M)
    (shrink : ∀ b → R.NonNegative b → Global b → Global (contraction * b)) where
    budget : Nat → ℝ
    budget n = M * R.pow contraction n

    budgetNN : ∀ n → R.NonNegative (budget n)
    budgetNN n = P.nonNegx,y⇒nonNegx*y nn (Seq.nonNegx⇒nonNegxⁿ n contractNN)

    bound : ∀ n → Global (budget n)
    bound zero p =
      let b = initial p
          eq = P.≃-symm (P.*-identityʳ M)
      in P.≤-respʳ-≃ eq (proj₁ b) , P.≤-respʳ-≃ eq (proj₂ b)
    bound (suc n) p =
      let b = shrink (budget n) (budgetNN n) (bound n) p
          eq = let open P.ℝ-Solver in solve 2
            (λ M p → Κ (+ 4 / 5) ⊗ (M ⊗ p) ⊜ M ⊗ (p ⊗ Κ (+ 4 / 5)))
            P.≃-refl M (R.pow contraction n)
      in P.≤-respʳ-≃ eq (proj₁ b) , P.≤-respʳ-≃ eq (proj₂ b)

    powerNull : Seq._ConvergesTo_ (R.pow contraction) R.0ℝ
    powerNull =
      let s = PG.polynomialGeometricSeriesConvergent contraction zero
            (P.nonNegx⇒0≤x contractNN) contractLt
          cv = Lim.seriesTermNull (PG.polynomialGeometricTerm contraction zero) (proj₁ s) (proj₂ s)
      in Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc n) → P.*-identityˡ (R.pow contraction (suc n))}) (_ , cv)

    budgetNull : Seq._ConvergesTo_ budget R.0ℝ
    budgetNull = Seq.xₙ→x∧x≃y⇒xₙ→y
      (Conv.mulR (Const.constantConverges M) powerNull) (P.*-zeroʳ M)

    zeroEverywhere : ∀ p → F p ≈C A.zeroC
    zeroEverywhere p =
      Seq.uniqueness-of-limits (Const.constantConverges (C.re (F p)))
        (Lim.dominatedNull budgetNull budgetNN (λ n → proj₁ (bound n p))) ,
      Seq.uniqueness-of-limits (Const.constantConverges (C.im (F p)))
        (Lim.dominatedNull budgetNull budgetNN (λ n → proj₂ (bound n p)))
