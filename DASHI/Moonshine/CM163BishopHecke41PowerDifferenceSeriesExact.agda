module DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact where

-- SOURCE-WRITTEN, kernel pending. First-order analytic factorization
-- of a complex power series on a closed unit disk with summable first
-- coefficient moment. The quotient is a genuine series of finite
-- polynomial wings, including at coincident endpoints.
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
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as B
import DASHI.Moonshine.CM163BishopHecke41UniformSeriesContinuityExact as Uniform
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)
open Completion using (original-bishop-pointwise-complex-converges; realConverges; imaginaryConverges)
open Uniform using (complexPrefix)

two : ℝ
two = (+ 2 / 1) ⋆

wing : BishopComplex → BishopComplex → Nat → Nat → BishopComplex
wing u v k zero = A.zeroC
wing u v k (suc n) = (powC u k *C powC v n) +C wing u v (suc k) n

Q : BishopComplex → BishopComplex → Nat → BishopComplex
Q u v = wing u v zero

wingStep : ∀ u v k n → wing u v (suc k) n ≈C (u *C wing u v k n)
wingStep u v k zero = complexSym (L.complexMultiplyRightZero u)
wingStep u v k (suc n) =
  complexTrans (A.addCCongruent (L.complexMultiplyAssociative u (powC u k) (powC v n))
    (wingStep u v (suc k) n))
    (complexSym (L.complexMultiplyDistributesLeft u _ _))

qStep : ∀ u v n → Q u v (suc n) ≈C (powC v n +C u *C Q u v n)
qStep u v n = A.addCCongruent (L.complexMultiplyLeftIdentity _) (wingStep u v zero n)

differenceStep : ∀ u v a b → (v *C b -C u *C a) ≈C ((v -C u) *C b +C u *C (b -C a))
differenceStep u v a b =
  complexTrans (A.subCCongruent
    (A.mulCCongruent (complexTrans (Cross.zeroExpand v u) (L.complexAddCommutative _ _)) (C.≈C-refl _))
    (C.≈C-refl _))
    (Cross.restStep u (v -C u) b a)

factor : ∀ u v n → (powC v n -C powC u n) ≈C ((v -C u) *C Q u v n)
factor u v zero = complexTrans (Prod.differenceSelf A.oneC) (complexSym (L.complexMultiplyRightZero _))
factor u v (suc n) =
  complexTrans (differenceStep u v (powC u n) (powC v n))
    (complexTrans (A.addCCongruent (C.≈C-refl _) (A.mulCCongruent (C.≈C-refl _) (factor u v n)))
      (complexTrans (Cross.restFinish u (v -C u) (powC v n) (Q u v n))
        (A.mulCCongruent (C.≈C-refl _) (complexSym (qStep u v n)))))

UnitDisk : BishopComplex → Set₁
UnitDisk u = Upper.BishopComplexNormSquareUpperRadius u R.1ℝ

mass : BishopComplex → ℝ
mass a = ∣ C.re a ∣ + ∣ C.im a ∣

pairBound : ∀ u v → UnitDisk u → UnitDisk v → ∀ k n →
  ∣ C.re (powC u k *C powC v n) ∣ ≤ two ×
  ∣ C.im (powC u k *C powC v n) ∣ ≤ two
pairBound u v hu hv k n =
  let a = powC u k; b = powC v n
      h = B.productBound (C.re b) (C.im b) (C.re a) (C.im a) R.1ℝ (B.realUnit hv n) (B.imagUnit hv n)
      m : mass a ≤ two
      m = P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 0 (Κ 1ℚᵘ ⊕ Κ 1ℚᵘ ⊜ Κ (+ 2 / 1)) P.≃-refl)
        (P.+-mono-≤ (B.realUnit hu k) (B.imagUnit hu k))
  in P.≤-trans (P.≤-respʳ-≃ (P.*-identityʳ _) (proj₁ h)) m ,
     P.≤-trans (P.≤-respʳ-≃ (P.*-identityʳ _) (proj₂ h)) m

countStep : ∀ n → (two + two * NR.natReal n) ≃ (two * NR.natReal (suc n))
countStep n = P.≃-trans
  (let open P.ℝ-Solver in solve 1
    (λ n → Κ (+ 2 / 1) ⊕ Κ (+ 2 / 1) ⊗ n ⊜ Κ (+ 2 / 1) ⊗ (n ⊕ Κ 1ℚᵘ)) P.≃-refl (NR.natReal n))
  (P.*-congˡ (P.≃-symm (NR.natRealSuccessor n)))

wingBound : ∀ u v → UnitDisk u → UnitDisk v → ∀ k n →
  ∣ C.re (wing u v k n) ∣ ≤ (two * NR.natReal n) ×
  ∣ C.im (wing u v k n) ∣ ≤ (two * NR.natReal n)
wingBound u v hu hv k zero =
  P.≤-reflexive (P.≃-trans (P.nonNegx⇒∣x∣≃x P.nonNeg0) (P.≃-symm (P.*-zeroʳ two))) ,
  P.≤-reflexive (P.≃-trans (P.nonNegx⇒∣x∣≃x P.nonNeg0) (P.≃-symm (P.*-zeroʳ two)))
wingBound u v hu hv k (suc n) =
  let a = powC u k *C powC v n
      b = wing u v (suc k) n
      h = pairBound u v hu hv k n
      j = wingBound u v hu hv (suc k) n
  in P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ (C.re a) (C.re b))
      (P.≤-respʳ-≃ (countStep n) (P.+-mono-≤ (proj₁ h) (proj₁ j))) ,
     P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ (C.im a) (C.im b))
      (P.≤-respʳ-≃ (countStep n) (P.+-mono-≤ (proj₂ h) (proj₂ j)))

moment : N.SeriesC → Nat → ℝ
moment f n = mass (f n) * (two * NR.natReal n)

terms : N.SeriesC → BishopComplex → BishopComplex → N.SeriesC
terms f u v n = f n *C Q u v n

termBound : ∀ f u v → UnitDisk u → UnitDisk v → ∀ n →
  ∣ C.re (terms f u v n) ∣ ≤ moment f n ×
  ∣ C.im (terms f u v n) ∣ ≤ moment f n
termBound f u v hu hv n = B.productBound (C.re (Q u v n)) (C.im (Q u v n))
  (C.re (f n)) (C.im (f n)) (two * NR.natReal n)
  (proj₁ (wingBound u v hu hv zero n)) (proj₂ (wingBound u v hu hv zero n))

wingContinuous : ∀ u {v : Nat → BishopComplex} {z} → Lim.Conv v z → ∀ k n →
  Lim.Conv (λ i → wing u (v i) k n) (wing u z k n)
wingContinuous u cv k zero = Lim.constantC A.zeroC
wingContinuous u cv k (suc n) = Lim.addConv
  (Conv.mulConv (Lim.constantC (powC u k)) (Uniform.powContinuous cv n))
  (wingContinuous u cv (suc k) n)

prefixContinuous : ∀ f u {v : Nat → BishopComplex} {z} → Lim.Conv v z → ∀ m →
  Lim.Conv (λ i → complexPrefix (terms f u (v i)) m) (complexPrefix (terms f u z) m)
prefixContinuous f u cv zero = Lim.constantC A.zeroC
prefixContinuous f u cv (suc m) = Lim.addConv (prefixContinuous f u cv m)
  (Conv.mulConv (Lim.constantC (f m)) (wingContinuous u cv zero m))

module At (f : N.SeriesC) (summable : Seq._isConvergent (Seq.SeriesOf (moment f))) where
  module Budget = Uniform.Budget (moment f) summable

  absolute : ∀ u v → UnitDisk u → UnitDisk v → C.ComponentwiseAbsoluteSeriesConvergent (terms f u v)
  absolute u v hu hv = C.componentwise-absolute-series-convergent
    (Seq.proposition-3-5 summable (zero , λ n _ →
      P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _))) (proj₁ (termBound f u v hu hv n))))
    (Seq.proposition-3-5 summable (zero , λ n _ →
      P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _))) (proj₂ (termBound f u v hu hv n))))

  value : ∀ u v → UnitDisk u → UnitDisk v → BishopComplex
  value u v hu hv = C.complexSeriesLimit (terms f u v) (absolute u v hu hv)

  converges : ∀ u v hu hv → C.ComplexSeriesConvergesTo (terms f u v) (value u v hu hv)
  converges u v hu hv = C.complexSeriesLimitConvergence _ (absolute u v hu hv)

  continuous : ∀ u (hu : UnitDisk u) (v : Nat → BishopComplex) z →
    (hv : ∀ n → UnitDisk (v n)) → (hz : UnitDisk z) → Lim.Conv v z →
    Lim.Conv (λ n → value u (v n) hu (hv n)) (value u z hu hz)
  continuous u hu v z hv hz cv =
    original-bishop-pointwise-complex-converges
      (Uniform.sequenceUniform (λ n → C.re (value u (v n) hu (hv n))) (C.re (value u z hu hz))
        (λ m n → C.re (complexPrefix (terms f u (v n)) m)) (λ m → C.re (complexPrefix (terms f u z) m))
        (λ m → realConverges (prefixContinuous f u cv m))
        (λ k → Budget.cutoff k ,
          (λ n → Budget.limitError (C.realTerms (terms f u (v n))) _ (λ i → proj₁ (termBound f u (v n) hu (hv n) i))
            (C.realConverges (converges u (v n) hu (hv n))) k) ,
          Budget.limitError (C.realTerms (terms f u z)) _ (λ i → proj₁ (termBound f u z hu hz i))
            (C.realConverges (converges u z hu hz)) k))
      (Uniform.sequenceUniform (λ n → C.im (value u (v n) hu (hv n))) (C.im (value u z hu hz))
        (λ m n → C.im (complexPrefix (terms f u (v n)) m)) (λ m → C.im (complexPrefix (terms f u z) m))
        (λ m → imaginaryConverges (prefixContinuous f u cv m))
        (λ k → Budget.cutoff k ,
          (λ n → Budget.limitError (C.imagTerms (terms f u (v n))) _ (λ i → proj₂ (termBound f u (v n) hu (hv n) i))
            (C.imagConverges (converges u (v n) hu (hv n))) k) ,
          Budget.limitError (C.imagTerms (terms f u z)) _ (λ i → proj₂ (termBound f u z hu hz i))
            (C.imagConverges (converges u z hu hz)) k))
