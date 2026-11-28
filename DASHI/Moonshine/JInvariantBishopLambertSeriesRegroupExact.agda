module DASHI.Moonshine.JInvariantBishopLambertSeriesRegroupExact where

-- SOURCE-WRITTEN, kernel pending. Actual positive (m,d) series,
-- exact factor-pair readout, and positive degree majorant. The
-- general cofinal compiler consumes explicit finite triangle limits.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
open import Relation.Binary.PropositionalEquality using (cong; sym)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Poly
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Foundations.BishopNatEmbeddingPowerExact as NatPow
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as F
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Pow
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H
import DASHI.Moonshine.JInvariantBishopLambertDegreeChartExact as D
import DASHI.Moonshine.JInvariantBishopLambertDegreeFibreExact as Fibre
import DASHI.Moonshine.JInvariantBishopLambertCofinalRegroupExact as Regroup
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorModularityExact as Mod
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as Major
import DASHI.Moonshine.JInvariantBishopEvenZetaNormalizationExact as Z
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as LR
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopFourierRowFiniteTailExact as FT
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_*C_; scaleC; powC)
open Comp using (complexTrans; complexSym)
open Re using (sum)

-- Zero keys are outside every actual factor-pair list. Define them
-- explicitly as zero, so all row-limit functions are total.
term : Nat → Nat → BishopComplex → D.Key → BishopComplex
term c k q (zero , d) = A.zeroC
term c k q (suc m , zero) = A.zeroC
term c k q (suc m , suc d) =
  scaleC (N.natReal (c * Pow.powNat (suc d) k)) (powC q (suc m * suc d))

budget : Nat → Nat → R.ℝ → D.Key → R.ℝ
budget c k r (zero , d) = R.0ℝ
budget c k r (suc m , zero) = R.0ℝ
budget c k r (suc m , suc d) =
  N.natReal (c * Pow.powNat (suc d) k) R.* R.pow r (suc m * suc d)

foldRead : ∀ {X : Set} (f : X → R.ℝ) xs → sum f xs R.≃ Fibre.foldR f xs
foldRead f [] = P.≃-refl
foldRead f (x ∷ xs) = P.+-cong P.≃-refl (foldRead f xs)

factorTerm : ∀ c k q {r} (p : F.PositiveFactorPair r) →
  term c k q (D.key p) ≈C Fibre.pairTerm c k q p
factorTerm c k q (F.positiveFactorPair zero () bd m eq)
factorTerm c k q (F.positiveFactorPair (suc d) h bd m eq) = C.≈C-refl _

degreeTerm : Nat → Nat → BishopComplex → Nat → BishopComplex
degreeTerm c k q n = scaleC (N.natReal (c * Pow.sigmaPower k (suc n))) (powC q (suc n))

degreeBudget : Nat → Nat → R.ℝ → Nat → R.ℝ
degreeBudget c k r n = N.natReal (c * Pow.sigmaPower k (suc n)) R.* R.pow r (suc n)

fibreTerm : ∀ c k q n → Mod.sumC (term c k q) (D.fibre n) ≈C degreeTerm c k q n
fibreTerm c k q n =
  let ps = F.positiveFactorPairs (suc n) (s≤s z≤n)
      h = Mod.sumCMap (term c k q) D.key ps
      r = Fibre.pairTerm c k q
  in complexTrans h (complexTrans
    (Mod.sumCCong (λ p → term c k q (D.key p)) r ps (factorTerm c k q))
    (complexTrans (foldRead (λ p → C.re (r p)) ps , foldRead (λ p → C.im (r p)) ps)
      (Fibre.degreeFibre c k (suc n) (s≤s z≤n) q)))

factorBudget : ∀ c k r {n} (p : F.PositiveFactorPair (suc n)) →
  budget c k r (D.key p) R.≃
  (N.natReal (c * Pow.powNat (F.divisor p) k) R.* R.pow r (suc n))
factorBudget c k r (F.positiveFactorPair zero () bd m eq)
factorBudget c k r (F.positiveFactorPair (suc d) h bd m eq) =
  P.*-congˡ (Fibre.realEq (cong (R.pow r) (sym eq)))

fibreBudget : ∀ c k r n →
  sum (budget c k r) (D.fibre n) R.≃ degreeBudget c k r n
fibreBudget c k r n =
  let ps = F.positiveFactorPairs (suc n) (s≤s z≤n)
      w = λ p → c * Pow.powNat (F.divisor p) k
      v = R.pow r (suc n)
  in P.≃-trans (Re.sumMap (budget c k r) D.key ps)
    (P.≃-trans (foldRead (λ p → budget c k r (D.key p)) ps)
      (P.≃-trans (Fibre.foldPointwiseR _ _ ps (factorBudget c k r))
        (P.≃-trans (Fibre.foldWeighted w v ps)
          (Fibre.realEq (cong (λ x → N.natReal x R.* v) (Fibre.coefficientReadout c k (suc n) (s≤s z≤n)))))))

triangleRead : ∀ f g → (∀ n → sum f (D.fibre n) R.≃ g n) →
  ∀ n → sum f (D.triangle n) R.≃ Seq.SeriesOf g n
triangleRead f g h zero = P.≃-refl
triangleRead f g h (suc n) = P.≃-trans (Ex.sumAppend f (D.triangle n) (D.fibre n))
  (P.+-cong (triangleRead f g h n) (h n))

oneToRead : ∀ f n → sum f (H.oneTo n) R.≃ Seq.SeriesOf (λ k → f (suc k)) n
oneToRead f zero = P.≃-refl
oneToRead f (suc n) = P.≃-trans (Ex.sumAppend f (H.oneTo n) (suc n ∷ []))
  (P.+-cong (oneToRead f n) (P.+-identityʳ (f (suc n))))

-- q^(m*d) comes from the same q^m row, with no assumption on a
-- separately evaluated exponential or branch of a complex logarithm.
powPow : ∀ q m d → powC (powC q m) d ≈C powC q (m * d)
powPow q m zero = Fibre.realEq (cong (λ k → C.re (powC q k)) (sym (NP.*-zeroʳ m))) ,
  Fibre.realEq (cong (λ k → C.im (powC q k)) (sym (NP.*-zeroʳ m)))
powPow q m (suc d) =
  complexTrans (A.mulCCongruent (C.≈C-refl _) (powPow q m d))
    (complexTrans (LR.powAdd q m (m * d))
      (let h = sym (NP.*-suc m d) in
       Fibre.realEq (cong (λ k → C.re (powC q k)) h) ,
       Fibre.realEq (cong (λ k → C.im (powC q k)) h)))

scaleScale : ∀ a b z → scaleC (a R.* b) z ≈C scaleC a (scaleC b z)
scaleScale a b (C.complex x y) = P.*-assoc a b x , P.*-assoc a b y

rowTermRead : ∀ c k q m d z → z ≈C powC q (suc m) →
  term c k q (suc m , suc d) ≈C scaleC (N.natReal c) (FT.term k z d)
rowTermRead c k q m d z h =
  complexTrans (Leaf.scaleCong (P.≃-trans (N.natRealMul c (Pow.powNat (suc d) k))
    (P.*-congˡ (NatPow.natRealPowNat (suc d) k)))
    (complexTrans (complexSym (powPow q (suc m) (suc d)))
      (A.powCCongruent (complexSym h) (suc d))))
    (scaleScale (N.natReal c) (R.pow (N.natReal (suc d)) k) (powC z (suc d)))

zeroSum : ∀ {X : Set} (xs : List X) → sum (λ _ → R.0ℝ) xs R.≃ R.0ℝ
zeroSum [] = P.≃-refl
zeroSum (x ∷ xs) = P.≃-trans (P.+-cong P.≃-refl (zeroSum xs)) (P.+-identityʳ R.0ℝ)

module At (c k : Nat) (q : BishopComplex) (r : R.ℝ) (input : Disk.BishopUnitDiskQ q r) where
  unit = Disk.unitInterval input
  env = Disk.powerEnvelope input

  budgetNN : ∀ x → R.NonNegative (budget c k r x)
  budgetNN (zero , d) = P.nonNeg0
  budgetNN (suc m , zero) = P.nonNeg0
  budgetNN (suc m , suc d) = P.nonNegx,y⇒nonNegx*y (Poly.natRealNonnegative _)
    (E.ratioPowerNonnegative unit _)

  realBound : ∀ x → R._≤_ (R.∣ C.re (term c k q x) ∣) (budget c k r x)
  realBound (zero , d) = P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0)
  realBound (suc m , zero) = P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0)
  realBound (suc m , suc d) =
    E.scaledComponentAbsoluteBound (Poly.natRealNonnegative _) (E.ratioPowerNonnegative unit _)
      P.≤-refl (E.realPowerBound env (d + m * suc d))
  imagBound : ∀ x → R._≤_ (R.∣ C.im (term c k q x) ∣) (budget c k r x)
  imagBound (zero , d) = P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0)
  imagBound (suc m , zero) = P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0)
  imagBound (suc m , suc d) =
    E.scaledComponentAbsoluteBound (Poly.natRealNonnegative _) (E.ratioPowerNonnegative unit _)
      P.≤-refl (E.imagPowerBound env (d + m * suc d))

  -- The actual row readout for arbitrary positive m, with a proof of
  -- its q^m phase and the original radius on that row.
  rowConverges : ∀ m z s (disk : Disk.BishopUnitDiskQ z s) →
    z ≈C powC q (suc m) →
    Mod.Converges (λ n → Mod.sumC (λ d → term c k q (suc m , d)) (H.oneTo n))
      (scaleC (N.natReal c) (Lim.AtDisk.row disk k))
  rowConverges m z s disk phase =
    let module B = Lim.AtDisk disk
        hRe = λ n → C.re (FT.term k z n)
        hIm = λ n → C.im (FT.term k z n)
        re = Inv.mulR (Power.constantConverges (N.natReal c)) (C.realConverges
          (C.complexSeriesLimitConvergence (FT.term k z) (B.rowAbsolute k)))
        im = Inv.mulR (Power.constantConverges (N.natReal c)) (C.imagConverges
          (C.complexSeriesLimitConvergence (FT.term k z) (B.rowAbsolute k)))
        readRe = λ n → P.≃-trans (oneToRead (λ d → C.re (term c k q (suc m , d))) n)
          (P.≃-trans (Z.prefixCong _ _ (λ d → proj₁ (rowTermRead c k q m d z phase)) n)
            (Z.prefixScale (N.natReal c) hRe n))
        readIm = λ n → P.≃-trans (oneToRead (λ d → C.im (term c k q (suc m , d))) n)
          (P.≃-trans (Z.prefixCong _ _ (λ d → proj₂ (rowTermRead c k q m d z phase)) n)
            (Z.prefixScale (N.natReal c) hIm n))
    in Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc n) → P.≃-symm (readRe (suc n))}) (_ , re) ,
       Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc n) → P.≃-symm (readIm (suc n))}) (_ , im)

  -- Reverse from the actual degree-series limit into the horizontal
  -- row order; all analytic assumptions are literal one-dimensional
  -- convergence, not the desired interchange theorem.
  module FromDegree (v : BishopComplex) (B : R.ℝ)
    (signed : C.ComplexSeriesConvergesTo (degreeTerm c k q) v)
    (absoluteBudget : Seq._ConvergesTo_ (Seq.SeriesOf (degreeBudget c k r)) B)
    where
    real = λ x → C.re (term c k q x)
    imag = λ x → C.im (term c k q x)
    major = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ {(suc n) → P.≃-symm (triangleRead (budget c k r) (degreeBudget c k r)
        (fibreBudget c k r) (suc n))}) (B , absoluteBudget)
    module ReOrder = Regroup.At real (budget c k r) (C.re v) B realBound budgetNN
      (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc n) → P.≃-symm (triangleRead real (λ i → C.re (degreeTerm c k q i))
          (λ i → proj₁ (fibreTerm c k q i)) (suc n))}) (_ , C.realConverges signed)) major
    module ImOrder = Regroup.At imag (budget c k r) (C.im v) B imagBound budgetNN
      (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc n) → P.≃-symm (triangleRead imag (λ i → C.im (degreeTerm c k q i))
          (λ i → proj₂ (fibreTerm c k q i)) (suc n))}) (_ , C.imagConverges signed)) major

    actualRows : (value : Nat → BishopComplex) →
      (∀ m → Mod.Converges (λ n → Mod.sumC (λ d → term c k q (m , d)) (H.oneTo n)) (value m)) →
      Mod.Converges (λ n → Mod.sumC value (H.oneTo n)) v
    actualRows value cv = ReOrder.rowLimit (λ m → C.re (value m)) (λ m → proj₁ (cv m)) ,
      ImOrder.rowLimit (λ m → C.im (value m)) (λ m → proj₂ (cv m))
