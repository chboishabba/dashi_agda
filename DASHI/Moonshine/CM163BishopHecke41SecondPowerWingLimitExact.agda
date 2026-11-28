module DASHI.Moonshine.CM163BishopHecke41SecondPowerWingLimitExact where

-- SOURCE-WRITTEN, kernel pending. A summable quadratic coefficient
-- budget constructs both the second wing value and its diagonal
-- sequential limit on the closed unit disk.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as PG
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHecke41SecondPowerWingExact as T
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as B
import DASHI.Moonshine.CM163BishopHecke41UniformSeriesContinuityExact as Uniform
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
open C using (BishopComplex)
open A using (_-C_; _*C_; powC)
open Completion using (original-bishop-pointwise-complex-converges; realConverges; imaginaryConverges)
open Uniform using (complexPrefix)

-- Each component of a triple monomial costs at most four using
-- the original componentwise unit-power bounds. There are n(n-1)/2.
tri : Nat → ℝ
tri zero = R.0ℝ
tri (suc n) = (D.two * (D.two * NR.natReal n)) + tri n

partBound : ∀ u v w → D.UnitDisk u → D.UnitDisk v → D.UnitDisk w → ∀ k n →
  ∣ C.re (powC u k *C D.Q v w n) ∣ ≤ (D.two * (D.two * NR.natReal n)) ×
  ∣ C.im (powC u k *C D.Q v w n) ∣ ≤ (D.two * (D.two * NR.natReal n))
partBound u v w hu hv hw k n =
  let a = powC u k
      q = D.Q v w n
      h = D.wingBound v w hv hw zero n
      b = B.productBound (C.re q) (C.im q) (C.re a) (C.im a)
        (D.two * NR.natReal n) (proj₁ h) (proj₂ h)
      m : D.mass a ≤ D.two
      m = P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 0
        (Κ 1ℚᵘ ⊕ Κ 1ℚᵘ ⊜ Κ (+ 2 / 1)) P.≃-refl)
        (P.+-mono-≤ (B.realUnit hu k) (B.imagUnit hu k))
      mono = P.*-monoʳ-≤-nonNeg m (P.nonNegx,y⇒nonNegx*y
        (PG.natRealNonnegative 2) (PG.natRealNonnegative n))
  in P.≤-trans (proj₁ b) mono , P.≤-trans (proj₂ b) mono

wingBound : ∀ u v w → D.UnitDisk u → D.UnitDisk v → D.UnitDisk w → ∀ k n →
  ∣ C.re (T.wing u v w k n) ∣ ≤ tri n ×
  ∣ C.im (T.wing u v w k n) ∣ ≤ tri n
wingBound u v w hu hv hw k zero =
  P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0) ,
  P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0)
wingBound u v w hu hv hw k (suc n) =
  let a = powC u k *C D.Q v w n
      b = T.wing u v w (suc k) n
      h = partBound u v w hu hv hw k n
      j = wingBound u v w hu hv hw (suc k) n
  in P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ (C.re a) (C.re b))
      (P.+-mono-≤ (proj₁ h) (proj₁ j)) ,
     P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ (C.im a) (C.im b))
      (P.+-mono-≤ (proj₂ h) (proj₂ j))

moment : N.SeriesC → Nat → ℝ
moment f n = D.mass (f n) * tri n

termBound : ∀ f u v w → D.UnitDisk u → D.UnitDisk v → D.UnitDisk w → ∀ n →
  ∣ C.re (T.terms f u v w n) ∣ ≤ moment f n ×
  ∣ C.im (T.terms f u v w n) ∣ ≤ moment f n
termBound f u v w hu hv hw n =
  let eq = T.wingRead u v w n
      h = wingBound u v w hu hv hw zero n
      a = T.T u v w n
  in B.productBound (C.re a) (C.im a) (C.re (f n)) (C.im (f n)) (tri n)
       (P.≤-respˡ-≃ (P.∣-∣-cong (proj₁ eq)) (proj₁ h))
       (P.≤-respˡ-≃ (P.∣-∣-cong (proj₂ eq)) (proj₂ h))

prefixContinuous : ∀ f u v {w : Nat → BishopComplex} {z} → Lim.Conv w z → ∀ m →
  Lim.Conv (λ i → complexPrefix (T.terms f u v (w i)) m)
    (complexPrefix (T.terms f u v z) m)
prefixContinuous f u v cv zero = Lim.constantC A.zeroC
prefixContinuous f u v cv (suc m) =
  Lim.addConv (prefixContinuous f u v cv m)
    (Conv.mulConv (Lim.constantC (f m)) (T.continuous u v cv m))

module At (f : N.SeriesC) (summable : Seq._isConvergent (Seq.SeriesOf (moment f))) where
  module Budget = Uniform.Budget (moment f) summable

  absolute : ∀ u v w → D.UnitDisk u → D.UnitDisk v → D.UnitDisk w →
    C.ComponentwiseAbsoluteSeriesConvergent (T.terms f u v w)
  absolute u v w hu hv hw = C.componentwise-absolute-series-convergent
    (Seq.proposition-3-5 summable (zero , λ n _ →
      P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _)))
        (proj₁ (termBound f u v w hu hv hw n))))
    (Seq.proposition-3-5 summable (zero , λ n _ →
      P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _)))
        (proj₂ (termBound f u v w hu hv hw n))))

  value : ∀ u v w → D.UnitDisk u → D.UnitDisk v → D.UnitDisk w → BishopComplex
  value u v w hu hv hw = C.complexSeriesLimit (T.terms f u v w) (absolute u v w hu hv hw)

  converges : ∀ u v w hu hv hw →
    C.ComplexSeriesConvergesTo (T.terms f u v w) (value u v w hu hv hw)
  converges u v w hu hv hw = C.complexSeriesLimitConvergence _ (absolute u v w hu hv hw)

  continuous : ∀ u v (hu : D.UnitDisk u) (hv : D.UnitDisk v)
    (w : Nat → BishopComplex) z → (hw : ∀ n → D.UnitDisk (w n)) →
    (hz : D.UnitDisk z) → Lim.Conv w z →
    Lim.Conv (λ n → value u v (w n) hu hv (hw n)) (value u v z hu hv hz)
  continuous u v hu hv w z hw hz cv =
    original-bishop-pointwise-complex-converges
      (Uniform.sequenceUniform (λ n → C.re (value u v (w n) hu hv (hw n)))
        (C.re (value u v z hu hv hz))
        (λ m n → C.re (complexPrefix (T.terms f u v (w n)) m))
        (λ m → C.re (complexPrefix (T.terms f u v z) m))
        (λ m → realConverges (prefixContinuous f u v cv m))
        (λ k → Budget.cutoff k ,
          (λ n → Budget.limitError (C.realTerms (T.terms f u v (w n))) _
            (λ i → proj₁ (termBound f u v (w n) hu hv (hw n) i))
            (C.realConverges (converges u v (w n) hu hv (hw n))) k) ,
          Budget.limitError (C.realTerms (T.terms f u v z)) _
            (λ i → proj₁ (termBound f u v z hu hv hz i))
            (C.realConverges (converges u v z hu hv hz)) k))
      (Uniform.sequenceUniform (λ n → C.im (value u v (w n) hu hv (hw n)))
        (C.im (value u v z hu hv hz))
        (λ m n → C.im (complexPrefix (T.terms f u v (w n)) m))
        (λ m → C.im (complexPrefix (T.terms f u v z) m))
        (λ m → imaginaryConverges (prefixContinuous f u v cv m))
        (λ k → Budget.cutoff k ,
          (λ n → Budget.limitError (C.imagTerms (T.terms f u v (w n))) _
            (λ i → proj₂ (termBound f u v (w n) hu hv (hw n) i))
            (C.imagConverges (converges u v (w n) hu hv (hw n))) k) ,
          Budget.limitError (C.imagTerms (T.terms f u v z)) _
            (λ i → proj₂ (termBound f u v z hu hv hz i))
            (C.imagConverges (converges u v z hu hv hz)) k))

module TwoJet (f : N.SeriesC)
  (firstMoment : Seq._isConvergent (Seq.SeriesOf (D.moment f)))
  (secondMoment : Seq._isConvergent (Seq.SeriesOf (moment f))) where
  module First = D.Factorization f firstMoment
  module Second = At f secondMoment

  actual : ∀ u (hu : D.UnitDisk u) (v : Nat → BishopComplex) →
    (hv : ∀ n → D.UnitDisk (v n)) → Lim.Conv v u →
    (eu : Eval.Eval u f) → (ev : ∀ n → Eval.Eval (v n) f) →
    J2.Jet2 (λ n → v n -C u) (λ n → Eval.value (ev n)) (Eval.value eu)
      (First.D.value u u hu hu) (Second.value u u u hu hu hu)
  actual u hu v hv cv eu ev =
    T.Attach.actualTwoJet f u v eu ev
      (λ n → First.D.value u (v n) hu (hv n))
      (First.D.value u u hu hu) (Second.value u u u hu hu hu)
      (λ n → First.increment u (v n) hu (hv n) eu (ev n))
      (λ n → First.D.converges u (v n) hu (hv n))
      (First.D.converges u u hu hu)
      (First.D.continuous u hu v u hv hu cv)
      (λ n → Second.value u u (v n) hu hu (hv n))
      (λ n → Second.converges u u (v n) hu hu (hv n))
      (Second.continuous u u hu hu v u hv hu cv)
