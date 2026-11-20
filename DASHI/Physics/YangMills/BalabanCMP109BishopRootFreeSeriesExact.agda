module DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact where

-- Actual Bishop limits for the root-free SU(2) chart coefficients.
-- Uses the vendor ratio test already used by the Machin atan construction.
-- Credit: classical sine/cosine/arcsine series, Murray/Csimma Bishop library,
-- Bałaban CMP98/CMP109 and the original DASHI factorial/order owners.
-- No new real, limit, or convergence postulate.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as Z using (+_; +≤+)
import Data.Nat.Base as N
open N using (NonZero; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Product using (_,_; proj₂)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_; 0ℚᵘ; 1ℚᵘ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import ExtraProperties as Extra
import Real as B
import RealProperties as BP
import Sequence as Seq
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Fact
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Frac

term : (Nat → B.ℝ) → B.ℝ → Nat → B.ℝ
term c x n = B._*_ (c n) (B.pow x n)

magnitude : (Nat → B.ℝ) → B.ℝ → Nat → B.ℝ
magnitude c x n = B._*_ (c n) (B.∣_∣ (B.pow x n))

termAbs : ∀ c x n → B.NonNegative (c n) →
  B._≃_ (B.∣_∣ (term c x n)) (magnitude c x n)
termAbs c x n cn =
  BP.≃-trans
    (BP.∣x*y∣≃∣x∣*∣y∣ (c n) (B.pow x n))
    (BP.*-congʳ (BP.0≤x⇒∣x∣≃x (BP.nonNegx⇒0≤x cn)))

magnitudeSuccessor :
  ∀ c x n →
  (∀ k → B.NonNegative (c k)) →
  (∀ k → B._≤_ (c (suc k)) (c k)) →
  B._≤_ (magnitude c x (suc n))
    (B._*_ (B.∣_∣ x) (magnitude c x n))
magnitudeSuccessor c x n cn cs =
  BP.≤-respʳ-≃
    (Machin.threeFactorRotate (c n) (B.∣_∣ (B.pow x n)) (B.∣_∣ x))
    (BP.*-mono-≤
      (cn (suc n)) (BP.nonNeg∣x∣ (B.pow x (suc n)))
      (cs n)
      (BP.≤-reflexive (BP.∣x*y∣≃∣x∣*∣y∣ (B.pow x n) x)))

termRatio :
  ∀ c x n →
  (∀ k → B.NonNegative (c k)) →
  (∀ k → B._≤_ (c (suc k)) (c k)) →
  B._≤_ (B.∣_∣ x) Half.bishopQuarter →
  B._≤_ (B.∣_∣ (term c x (suc n)))
    (B._*_ Half.bishopQuarter (B.∣_∣ (term c x n)))
termRatio c x n cn cs inside =
  BP.≤-respʳ-≃
    (BP.*-congˡ (BP.≃-symm (termAbs c x n (cn n))))
    (BP.≤-respˡ-≃ (termAbs c x (suc n) (cn (suc n)))
      (BP.≤-trans (magnitudeSuccessor c x n cn cs)
        (BP.*-monoʳ-≤-nonNeg inside
          (BP.nonNegx,y⇒nonNegx*y (cn n) (BP.nonNeg∣x∣ (B.pow x n))))))

convergent :
  ∀ c x →
  (∀ k → B.NonNegative (c k)) →
  (∀ k → B._≤_ (c (suc k)) (c k)) →
  B._≤_ (B.∣_∣ x) Half.bishopQuarter →
  Seq._isConvergent (Seq.SeriesOf (term c x))
convergent c x cn cs inside =
  Seq.proposition-3-6-1
    (Machin.quarterPositive , Machin.quarterBelowOne)
    (zero , λ index _ → termRatio c x index cn cs inside)

factorialGrowth : ∀ n → E.factorial n N.≤ E.factorial (suc n)
factorialGrowth n =
  subst (λ a → a N.≤ E.factorial (suc n))
    (NP.*-identityˡ (E.factorial n))
    (NP.*-mono-≤ (s≤s (z≤n {n = n})) (NP.≤-refl {n = E.factorial n}))

factorialInverseTwoStep :
  ∀ n → B._≤_ (B._⋆ (E.inverseFactorialRational (suc (suc n))))
                   (B._⋆ (E.inverseFactorialRational n))
factorialInverseTwoStep n =
  let
    instance
      oldNonzero : NonZero (E.factorial n)
      oldNonzero = NP._!≢0 n
      newNonzero : NonZero (E.factorial (suc (suc n)))
      newNonzero = NP._!≢0 (suc (suc n))
  in BP.p≤q⇒p⋆≤q⋆
    (E.inverseFactorialRational (suc (suc n)))
    (E.inverseFactorialRational n)
    (Extra.q≤r⇒+p/r≤+p/q 1 (E.factorial n)
      (E.factorial (suc (suc n)))
      (NP.≤-trans (factorialGrowth n) (factorialGrowth (suc n))))

aCoefficient bCoefficient : Nat → B.ℝ
aCoefficient n = B._⋆ (E.inverseFactorialRational (E.evenExponent (suc n)))
bCoefficient n = B._⋆ (E.inverseFactorialRational (E.oddExponent (suc n)))

aNN : ∀ n → B.NonNegative (aCoefficient n)
aNN n = Fact.embeddedInverseFactorialNonnegative (E.evenExponent (suc n))
bNN : ∀ n → B.NonNegative (bCoefficient n)
bNN n = Fact.embeddedInverseFactorialNonnegative (E.oddExponent (suc n))
aStep : ∀ n → B._≤_ (aCoefficient (suc n)) (aCoefficient n)
aStep n = factorialInverseTwoStep (E.evenExponent (suc n))
bStep : ∀ n → B._≤_ (bCoefficient (suc n)) (bCoefficient n)
bStep n = factorialInverseTwoStep (E.oddExponent (suc n))

-- X is the signed argument -w, so the factorial coefficients are positive
-- and term c X n is exactly (-w)^n/(2n+k)!.
aSeries bSeries : (X : B.ℝ) →
  B._≤_ (B.∣_∣ X) Half.bishopQuarter → B.ℝ
aSeries X inside = Seq.lim (convergent aCoefficient X aNN aStep inside)
bSeries X inside = Seq.lim (convergent bCoefficient X bNN bStep inside)

aSeriesConverges : ∀ X inside →
  Seq._ConvergesTo_ (Seq.SeriesOf (term aCoefficient X)) (aSeries X inside)
aSeriesConverges X inside = proj₂ (convergent aCoefficient X aNN aStep inside)
bSeriesConverges : ∀ X inside →
  Seq._ConvergesTo_ (Seq.SeriesOf (term bCoefficient X)) (bSeries X inside)
bSeriesConverges X inside = proj₂ (convergent bCoefficient X bNN bStep inside)

-- arcsin(r)/r = sum c_n (r²)^n, c_0=1 and
-- c_(n+1)/c_n = ((2n+1)/(2n+2))*((2n+1)/(2n+3)).
-- Construct the coefficients by this rational product; no factorial/binomial
-- division at a real radius, and no zero case.

fraction : Nat → Nat → B.ℝ
fraction n d = B._⋆ (+ n / suc d)

fractionNN : ∀ n d → B.NonNegative (fraction n d)
fractionNN n d = BP.0≤x⇒nonNegx
  (BP.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ n / suc d) (Q.*≤* (Z.+≤+ z≤n)))

fractionBelowOne :
  ∀ n d → n N.≤ suc d → B._≤_ (fraction n d) B.1ℝ
fractionBelowOne n d le = BP.p≤q⇒p⋆≤q⋆ (+ n / suc d) 1ℚᵘ
  (Frac.natFractionLe
    (subst (λ l → l N.≤ 1 N.* suc d) (sym (NP.*-identityʳ n))
      (subst (λ r → n N.≤ r) (sym (NP.*-identityˡ (suc d))) le)))

arcRatio : Nat → B.ℝ
arcRatio n =
  B._*_ (fraction (E.oddExponent n) (E.oddExponent n))
         (fraction (E.oddExponent n) (suc (E.oddExponent n)))

arcRatioNN : ∀ n → B.NonNegative (arcRatio n)
arcRatioNN n = BP.nonNegx,y⇒nonNegx*y
  (fractionNN (E.oddExponent n) (E.oddExponent n))
  (fractionNN (E.oddExponent n) (suc (E.oddExponent n)))

arcRatioBelowOne : ∀ n → B._≤_ (arcRatio n) B.1ℝ
arcRatioBelowOne n =
  let o = E.oddExponent n
  in BP.≤-respʳ-≃ (BP.*-identityˡ B.1ℝ)
    (BP.*-mono-≤ (fractionNN o o) (fractionNN o (suc o))
      (fractionBelowOne o o (NP.n≤1+n o))
      (fractionBelowOne o (suc o)
        (NP.≤-trans (NP.n≤1+n o) (NP.n≤1+n (suc o)))))

arcCoefficient : Nat → B.ℝ
arcCoefficient zero = B.1ℝ
arcCoefficient (suc n) = B._*_ (arcCoefficient n) (arcRatio n)

arcNN : ∀ n → B.NonNegative (arcCoefficient n)
arcNN zero = BP.0≤x⇒nonNegx
  (BP.p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (Q.*≤* (Z.+≤+ z≤n)))
arcNN (suc n) = BP.nonNegx,y⇒nonNegx*y (arcNN n) (arcRatioNN n)

arcStep : ∀ n → B._≤_ (arcCoefficient (suc n)) (arcCoefficient n)
arcStep n =
  BP.≤-respʳ-≃ (BP.*-identityʳ (arcCoefficient n))
    (BP.*-monoˡ-≤-nonNeg (arcRatioBelowOne n) (arcNN n))

arcSeries : (s : B.ℝ) →
  B._≤_ (B.∣_∣ s) Half.bishopQuarter → B.ℝ
arcSeries s inside = Seq.lim (convergent arcCoefficient s arcNN arcStep inside)

arcSeriesConverges : ∀ s inside →
  Seq._ConvergesTo_ (Seq.SeriesOf (term arcCoefficient s)) (arcSeries s inside)
arcSeriesConverges s inside =
  proj₂ (convergent arcCoefficient s arcNN arcStep inside)
