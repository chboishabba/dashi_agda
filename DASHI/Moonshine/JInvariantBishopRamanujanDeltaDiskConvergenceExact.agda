module DASHI.Moonshine.JInvariantBishopRamanujanDeltaDiskConvergenceExact where

-- SOURCE-WRITTEN, kernel pending. At any literal disk radius r<1,
-- choose a larger Bishop radius rho<1. The finite-prefix recurrence
-- bound at rho gives a geometric absolute majorant at r. No eta
-- product identity or global j-invariance is used by this construction.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Agda.Builtin.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _+_; _-_; _*_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import Inverse as I
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Poly
import DASHI.Analysis.BishopStrictRatioInterpolationExact as Interp
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Env
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as FiniteOrder
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopNatEmbeddingMonotoneExact as Mono
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Div
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumBoundExact as DivBound
import DASHI.Moonshine.JInvariantBishopEvenZetaNormalizationExact as Z
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as W
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.JInvariantBishopEulerRecurrenceRadiusBoundExact as B
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
open G using (Series; neg)

prefixMono : ∀ f g → (∀ n → R._≤_ (f n) (g n)) → ∀ n →
  R._≤_ (Seq.SeriesOf f n) (Seq.SeriesOf g n)
prefixMono f g h zero = P.≤-refl
prefixMono f g h (suc n) = P.+-mono-≤ (prefixMono f g h n) (h n)

-- Generic version of the existing Basel finite-prefix-below-limit proof.
prefixBelow : ∀ f → (∀ n → R.NonNegative (f n)) →
  (cv : Seq._isConvergent (Seq.SeriesOf f)) → ∀ count →
  R._≤_ (Seq.SeriesOf f count) (Seq.lim cv)
prefixBelow f nn cv count =
  let s = Seq.SeriesOf f
      shifted = λ index → s (index + count)
      sub : Seq._SubsequenceOf_ shifted s
      sub = Seq.subseq* ((λ index → index + count) , (λ _ → P.≃-refl) ,
        (λ index → NP.n<1+n (index + count)))
      cs = s count , Power.constantConverges (s count)
      vs = Seq.lim cv , Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y sub cv
  in Seq.xₙ≤yₙ⇒limxₙ≤limyₙ
    (λ index → Seq.isIncreasing⇒isIncreasing₂
      (FiniteOrder.partialSumsIncreasing nn) (index + count) count (NP.m≤n+m count index))
    cs vs

sigmaEnvelope : ∀ n → R._≤_ (NR.natReal (24 Nat.* Div.sigma1 (suc n)))
  (NR.natReal 24 * R.pow (NR.natReal (suc n)) 2)
sigmaEnvelope n = P.≤-respʳ-≃
  (P.≃-trans (NR.natRealMul 24 (suc n Nat.* suc n))
    (P.*-congˡ (P.≃-trans (NR.natRealMul (suc n) (suc n))
      (let open P.ℝ-Solver in solve 1 (λ x → x ⊗ x ⊜ (Κ 1ℚᵘ ⊗ x) ⊗ x)
        P.≃-refl (NR.natReal (suc n))))))
  (Mono.natRealMonotone (NP.*-mono-≤ NP.≤-refl (DivBound.sigma1QuadraticBound (suc n))))

module AtRho (rho : ℝ) (rhoUnit : Unit.BishopUnitIntervalRatio rho) where
  rhoNN = Unit.ratioNonnegative rhoUnit
  rhoSmall = Unit.ratioBelowOne rhoUnit
  rhoPowNN : ∀ n → R.NonNegative (R.pow rho n)
  rhoPowNN n = Seq.nonNegx⇒nonNegxⁿ n (P.0≤x⇒nonNegx rhoNN)

  budget : Series
  budget = Poly.shiftedScaledPolynomialGeometricTerm (NR.natReal 24) rho 2
  budgetNN : ∀ n → R.NonNegative (budget n)
  budgetNN = Poly.shiftedScaledPolynomialGeometricTermNonnegative rhoNN (Poly.natRealNonnegative 24) 2

  budgetConv : Seq._isConvergent (Seq.SeriesOf budget)
  budgetConv = Seq.absolute⇒isConvergent
    (Poly.shiftedScaledPolynomialGeometricSeriesAbsolutelyConvergent rho (NR.natReal 24) 2
      rhoNN rhoSmall (Poly.natRealNonnegative 24))

  massLimit : ℝ
  massLimit = Seq.lim budgetConv

  eplusRead : ∀ n → D.Eplus (suc n) ≃ R.- (NR.natReal (24 Nat.* Div.sigma1 (suc n)))
  eplusRead n = let open P.ℝ-Solver in solve 1 (λ a → (⊝ a) ⊖ Κ 0ℚᵘ ⊜ ⊝ a)
    P.≃-refl (NR.natReal (24 Nat.* Div.sigma1 (suc n)))

  plusAbs : ∀ n → ∣ W.weighted rho D.Eplus (suc n) ∣ ≃
    (R.pow rho (suc n) * NR.natReal (24 Nat.* Div.sigma1 (suc n)))
  plusAbs n = P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ (R.pow rho (suc n)) (D.Eplus (suc n)))
    (P.*-cong (P.nonNegx⇒∣x∣≃x (rhoPowNN (suc n)))
      (P.≃-trans (P.∣-∣-cong (eplusRead n))
        (P.≃-trans P.∣-x∣≃∣x∣ (P.nonNegx⇒∣x∣≃x (Poly.natRealNonnegative _)))))

  plusBound : ∀ n → R._≤_ ∣ W.weighted rho D.Eplus (suc n) ∣ (budget n)
  plusBound n = P.≤-respˡ-≃ (P.≃-symm (plusAbs n))
    (P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 3
      (λ r c a → r ⊗ (c ⊗ a) ⊜ c ⊗ (a ⊗ r)) P.≃-refl
      (R.pow rho (suc n)) (NR.natReal 24) (R.pow (NR.natReal (suc n)) 2))
      (P.*-monoˡ-≤-nonNeg (sigmaEnvelope n) (rhoPowNN (suc n))))

  minusBound : ∀ n → R._≤_ ∣ W.weighted rho (neg D.Eplus) (suc n) ∣ (budget n)
  minusBound n = P.≤-respˡ-≃ (P.≃-symm (P.≃-trans
    (P.∣-∣-cong (let open P.ℝ-Solver in solve 2 (λ r x → r ⊗ (⊝ x) ⊜ ⊝ (r ⊗ x))
      P.≃-refl (R.pow rho (suc n)) (D.Eplus (suc n))))
    P.∣-x∣≃∣x∣)) (plusBound n)

  massPlus : ∀ n → R._≤_ (B.mass (Row.shift (W.weighted rho D.Eplus)) (suc n)) massLimit
  massPlus n = P.≤-trans (prefixMono _ budget plusBound (suc n)) (prefixBelow budget budgetNN budgetConv (suc n))
  massMinus : ∀ n → R._≤_ (B.mass (Row.shift (W.weighted rho (neg D.Eplus))) (suc n)) massLimit
  massMinus n = P.≤-trans (prefixMono _ budget minusBound (suc n)) (prefixBelow budget budgetNN budgetConv (suc n))

  -- Native Archimedean witness from the pinned Bishop library.
  M : Nat
  M = proj₁ (P.fast-archimedean-ℝ massLimit)
  threshold : R._≤_ massLimit (NR.natReal (suc M))
  threshold = P.<⇒≤ (proj₂ (P.fast-archimedean-ℝ massLimit))

  module Bound = B.AtRadius rho massLimit M massPlus massMinus threshold

module AtDisk (q : C.BishopComplex) (r : ℝ) (disk : Disk.BishopUnitDiskQ q r) where
  rUnit = Disk.unitInterval disk
  rNN = Unit.ratioNonnegative rUnit
  rSmall = Unit.ratioBelowOne rUnit
  above = Interp.interpolateStrictUnitRatio rNN rSmall
  rho = proj₁ above
  rhoPositive = proj₁ (proj₂ above)
  rBelowRho = proj₁ (proj₂ (proj₂ above))
  rhoSmall = proj₂ (proj₂ (proj₂ above))
  rhoUnit : Unit.BishopUnitIntervalRatio rho
  rhoUnit = record { Unit.ratioNonnegative = P.<⇒≤ rhoPositive ; Unit.ratioBelowOne = rhoSmall }
  module Rho = AtRho rho rhoUnit

  rhoNZ : R._≄0 rho
  rhoNZ = inj₂ rhoPositive
  ri = I._⁻¹ rho rhoNZ
  riPositive = I.0<x⇒0<x⁻¹ rhoNZ rhoPositive
  factor : ℝ
  factor = ri * r
  factorNN : R.NonNegative factor
  factorNN = P.nonNegx,y⇒nonNegx*y (P.0≤x⇒nonNegx (P.<⇒≤ riPositive)) (P.0≤x⇒nonNegx rNN)
  factorSmall : R._<_ factor R.1ℝ
  factorSmall = P.<-respʳ-≃ (P.≃-trans (P.*-comm ri rho) (I.*-inverseʳ rho rhoNZ))
    (P.*-monoʳ-<-pos (P.0<x⇒posx riPositive) rBelowRho)

  rhoFactor : rho * factor ≃ r
  rhoFactor = P.≃-trans (P.≃-symm (P.*-assoc rho ri r))
    (P.≃-trans (P.*-congʳ (I.*-inverseʳ rho rhoNZ)) (P.*-identityˡ r))

  rescale : ∀ f n → W.weighted r f n ≃
    R.pow factor n * W.weighted rho f n
  rescale f n =
    P.≃-trans (P.*-congʳ (Z.powCong (P.≃-symm rhoFactor) n))
      (P.≃-trans (P.*-congʳ (Z.powProd rho factor n))
        (let open P.ℝ-Solver in solve 3
          (λ a b x → (a ⊗ b) ⊗ x ⊜ b ⊗ (a ⊗ x)) P.≃-refl
          (R.pow rho n) (R.pow factor n) (f n)))

  scaledBound : ∀ f C0 → (∀ n → R._≤_ ∣ W.weighted rho f n ∣ C0) →
    ∀ n → R._≤_ ∣ W.weighted r f n ∣ (C0 * R.pow factor n)
  scaledBound f C0 h n =
    P.≤-respˡ-≃ (P.≃-symm (P.≃-trans (P.∣-∣-cong (rescale f n))
      (P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ (R.pow factor n) (W.weighted rho f n))
        (P.*-congʳ (P.nonNegx⇒∣x∣≃x (Seq.nonNegx⇒nonNegxⁿ n factorNN))))))
      (P.≤-respʳ-≃ (P.*-comm (R.pow factor n) C0)
        (P.*-monoˡ-≤-nonNeg (h n) (Seq.nonNegx⇒nonNegxⁿ n factorNN)))

  majorantConv : ∀ C0 → Seq._isConvergent (Seq.SeriesOf (λ n → C0 * R.pow factor n))
  majorantConv C0 =
    let g = Poly.polynomialGeometricTerm factor 0
        gc = Poly.polynomialGeometricSeriesConvergent factor 0 (P.nonNegx⇒0≤x factorNN) factorSmall
        pc = Seq.lim gc
        cv = Conv.mulR (Power.constantConverges C0) (proj₂ gc)
        read = λ n → P.≃-trans (Z.prefixScale C0 (R.pow factor) n)
          (P.*-congˡ (Z.prefixCong (R.pow factor) g (λ k → P.≃-symm (P.*-identityˡ (R.pow factor k))) n))
    in C0 * pc , Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc n) → P.≃-symm (read (suc n))}) (_ , cv)

  weight : Series → Nat → C.BishopComplex
  weight f n = A.scaleC (f n) (A.powC q n)

  realBound : ∀ f n → R._≤_ ∣ C.re (weight f (suc n)) ∣ ∣ W.weighted r f (suc n) ∣
  realBound f n =
    let p = R.pow r (suc n)
        pNN = Seq.nonNegx⇒nonNegxⁿ (suc n) (P.0≤x⇒nonNegx rNN)
    in P.≤-respˡ-≃ (P.≃-symm (P.∣x*y∣≃∣x∣*∣y∣ (f (suc n)) (C.re (A.powC q (suc n)))))
      (P.≤-respʳ-≃ (P.≃-symm (P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ p (f (suc n)))
        (P.≃-trans (P.*-congʳ (P.nonNegx⇒∣x∣≃x pNN)) (P.*-comm p ∣ f (suc n) ∣))))
        (P.*-monoˡ-≤-nonNeg (Env.realPowerBound (Disk.powerEnvelope disk) n) (P.nonNeg∣x∣ (f (suc n)))))

  imagBound : ∀ f n → R._≤_ ∣ C.im (weight f (suc n)) ∣ ∣ W.weighted r f (suc n) ∣
  imagBound f n =
    let p = R.pow r (suc n)
        pNN = Seq.nonNegx⇒nonNegxⁿ (suc n) (P.0≤x⇒nonNegx rNN)
    in P.≤-respˡ-≃ (P.≃-symm (P.∣x*y∣≃∣x∣*∣y∣ (f (suc n)) (C.im (A.powC q (suc n)))))
      (P.≤-respʳ-≃ (P.≃-symm (P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ p (f (suc n)))
        (P.≃-trans (P.*-congʳ (P.nonNegx⇒∣x∣≃x pNN)) (P.*-comm p ∣ f (suc n) ∣))))
        (P.*-monoˡ-≤-nonNeg (Env.imagPowerBound (Disk.powerEnvelope disk) n) (P.nonNeg∣x∣ (f (suc n)))))

  absolute : ∀ f C0 → (∀ n → R._≤_ ∣ W.weighted rho f n ∣ C0) →
    C.ComponentwiseAbsoluteSeriesConvergent (weight f)
  absolute f C0 h = C.componentwise-absolute-series-convergent
    (Seq.proposition-3-5 (majorantConv C0) (1 , λ { zero () ; (suc n) _ →
      P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ (C.re (weight f (suc n))))))
        (P.≤-trans (realBound f n) (scaledBound f C0 h (suc n))) }))
    (Seq.proposition-3-5 (majorantConv C0) (1 , λ { zero () ; (suc n) _ →
      P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ (C.im (weight f (suc n))))))
        (P.≤-trans (imagBound f n) (scaledBound f C0 h (suc n))) }))

  unitAbsolute : C.ComponentwiseAbsoluteSeriesConvergent (weight D.unit)
  unitAbsolute = absolute D.unit Rho.Bound.U0.C Rho.Bound.unitBound
  inverseAbsolute : C.ComponentwiseAbsoluteSeriesConvergent (weight D.reciprocal)
  inverseAbsolute = absolute D.reciprocal Rho.Bound.V0.C Rho.Bound.inverseBound

  unitValue inverseValue : C.BishopComplex
  unitValue = C.complexSeriesLimit (weight D.unit) unitAbsolute
  inverseValue = C.complexSeriesLimit (weight D.reciprocal) inverseAbsolute
