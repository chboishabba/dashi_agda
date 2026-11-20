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
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Signs
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alt
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Bracket

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

------------------------------------------------------------------------
-- Bounds on the SAME limits, using the existing alternating-limit theorem.
------------------------------------------------------------------------

powNegEven : ∀ w n →
  B._≃_ (B.pow (B.- w) (Alt.double n)) (B.pow w (Alt.double n))
powNegEven w zero = BP.≃-refl
powNegEven w (suc n) =
  BP.≃-trans (Fact.powTwoStep (B.- w) (Alt.double n))
    (BP.≃-trans
      (BP.*-cong (powNegEven w n) (Signs.negatedSquareEquivalentSquare w))
      (BP.≃-symm (Fact.powTwoStep w (Alt.double n))))

powNegOdd : ∀ w n →
  B._≃_ (B.pow (B.- w) (suc (Alt.double n)))
          (B.- (B.pow w (suc (Alt.double n))))
powNegOdd w n =
  BP.≃-trans (BP.*-congʳ (powNegEven w n))
    (let open BP.ℝ-Solver
     in solve 2 (λ p x → p ⊗ (⊝ x) ⊜ ⊝ (p ⊗ x))
       BP.≃-refl (B.pow w (Alt.double n)) w)

evenSigned : ∀ c w n →
  B._≃_ (term c (B.- w) (Alt.double n)) (term c w (Alt.double n))
evenSigned c w n = BP.*-congˡ (powNegEven w n)

oddSigned : ∀ c w n →
  B._≃_ (term c (B.- w) (suc (Alt.double n)))
    (B.- (term c w (suc (Alt.double n))))
oddSigned c w n =
  BP.≃-trans (BP.*-congˡ (powNegOdd w n))
    (let open BP.ℝ-Solver
     in solve 2 (λ a p → a ⊗ (⊝ p) ⊜ ⊝ (a ⊗ p))
       BP.≃-refl (c (suc (Alt.double n))) (B.pow w (suc (Alt.double n))))

positiveTermNN : ∀ c w n →
  (∀ k → B.NonNegative (c k)) → B.NonNegative w →
  B.NonNegative (term c w n)
positiveTermNN c w n cn wn =
  BP.nonNegx,y⇒nonNegx*y (cn n) (Concrete.powNonnegative wn n)

quarterLeOne : B._≤_ Half.bishopQuarter B.1ℝ
quarterLeOne = BP.p≤q⇒p⋆≤q⋆ Half.quarter 1ℚᵘ
  (Extra.q≤r⇒+p/r≤+p/q 1 1 4 (s≤s z≤n))

alternatingData :
  ∀ c w (cn : ∀ k → B.NonNegative (c k))
    (cs : ∀ k → B._≤_ (c (suc k)) (c k)) →
  B.NonNegative w →
  B._≤_ (B.∣_∣ (B.- w)) Half.bishopQuarter →
  Alt.AlternatingDecreasingSeriesData
alternatingData c w cn cs wn inside = record
  { term = term c (B.- w)
  ; magnitude = λ n → B.∣_∣ (term c (B.- w) n)
  ; representedLimit = Seq.lim (convergent c (B.- w) cn cs inside)
  ; magnitudeNonnegative = λ n → BP.nonNeg∣x∣ (term c (B.- w) n)
  ; magnitudeDecreasing = λ n →
      BP.≤-trans (termRatio c (B.- w) n cn cs inside)
        (BP.≤-respʳ-≃ (BP.*-identityˡ (B.∣_∣ (term c (B.- w) n)))
          (BP.*-monoʳ-≤-nonNeg quarterLeOne (BP.nonNeg∣x∣ (term c (B.- w) n))))
  ; evenTermIsPositiveMagnitude = λ n →
      let eq = evenSigned c w n
          absEq = BP.≃-trans (BP.∣-∣-cong eq)
            (BP.nonNegx⇒∣x∣≃x (positiveTermNN c w (Alt.double n) cn wn))
      in BP.≃-trans eq (BP.≃-symm absEq)
  ; oddTermIsNegativeMagnitude = λ n →
      let eq = oddSigned c w n
          absEq = BP.≃-trans (BP.∣-∣-cong eq)
            (BP.≃-trans BP.∣-x∣≃∣x∣
              (BP.nonNegx⇒∣x∣≃x
                (positiveTermNN c w (suc (Alt.double n)) cn wn)))
      in BP.≃-trans eq (BP.-‿cong (BP.≃-symm absEq))
  ; seriesConvergesToRepresentedLimit =
      proj₂ (convergent c (B.- w) cn cs inside)
  }

alternatingLimitNonnegative :
  ∀ c w cn cs wn inside →
  B._≤_ B.0ℝ (Seq.lim (convergent c (B.- w) cn cs inside))
alternatingLimitNonnegative c w cn cs wn inside =
  Bracket.lowerPartialBelowRepresentedLimit
    (Alt.alternatingInterlacingData (alternatingData c w cn cs wn inside)) zero

alternatingLimitBelowFirst :
  ∀ c w cn cs wn inside →
  B._≤_ (Seq.lim (convergent c (B.- w) cn cs inside)) (c zero)
alternatingLimitBelowFirst c w cn cs wn inside =
  BP.≤-respʳ-≃
    (BP.≃-trans (BP.+-identityˡ (term c (B.- w) zero))
      (BP.*-identityʳ (c zero)))
    (Bracket.representedLimitBelowUpperPartial
      (Alt.alternatingInterlacingData (alternatingData c w cn cs wn inside)) zero)

aNonnegative : ∀ w (wn : B.NonNegative w) inside →
  B._≤_ B.0ℝ (aSeries (B.- w) inside)
aNonnegative w wn inside = alternatingLimitNonnegative aCoefficient w aNN aStep wn inside

bNonnegative : ∀ w (wn : B.NonNegative w) inside →
  B._≤_ B.0ℝ (bSeries (B.- w) inside)
bNonnegative w wn inside = alternatingLimitNonnegative bCoefficient w bNN bStep wn inside

bBelowOneSixth : ∀ w (wn : B.NonNegative w) inside →
  B._≤_ (bSeries (B.- w) inside) (B._⋆ (+ 1 / 6))
bBelowOneSixth w wn inside =
  alternatingLimitBelowFirst bCoefficient w bNN bStep wn inside

------------------------------------------------------------------------
-- Positive arcsinc majorant on the same limit. A loose bound 2 is enough
-- for Path13 even after componentwise averaging; no extra analytic chart
-- radius premise or separate series approximation is needed.
------------------------------------------------------------------------

twoB : B.ℝ
twoB = B._⋆ (+ 2 / 1)

arcCoefficientBelowOne : ∀ n → B._≤_ (arcCoefficient n) B.1ℝ
arcCoefficientBelowOne zero = BP.≤-refl
arcCoefficientBelowOne (suc n) =
  BP.≤-trans (arcStep n) (arcCoefficientBelowOne n)

quarterBelowHalf : B._≤_ Half.bishopQuarter Half.bishopHalf
quarterBelowHalf =
  BP.p≤q⇒p⋆≤q⋆ Half.quarter Half.half
    (Extra.q≤r⇒+p/r≤+p/q 1 2 4 (s≤s (s≤s z≤n)))

arcTermBelowHalfPower :
  ∀ s → B.NonNegative s →
  B._≤_ (B.∣_∣ s) Half.bishopQuarter →
  ∀ n → B._≤_ (term arcCoefficient s n) (B.pow Half.bishopHalf n)
arcTermBelowHalfPower s sn inside n =
  let sBound = BP.≤-trans
        (BP.≤-respˡ-≃ (BP.≃-symm (BP.nonNegx⇒∣x∣≃x sn)) inside)
        quarterBelowHalf
      powerBound = Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ n sBound sn
  in BP.≤-respʳ-≃ (BP.*-identityˡ (B.pow Half.bishopHalf n))
      (BP.*-mono-≤ (arcNN n) (Concrete.powNonnegative sn n)
        (arcCoefficientBelowOne n) powerBound)

arcReserve : Nat → B.ℝ
arcReserve n = B._*_ twoB (B.pow Half.bishopHalf n)

arcReserveNonnegative : ∀ n → B.NonNegative (arcReserve n)
arcReserveNonnegative n =
  BP.nonNegx,y⇒nonNegx*y
    (BP.0≤x⇒nonNegx (BP.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 2 / 1)
      (Q.*≤* (Z.+≤+ z≤n))))
    (Concrete.powNonnegative
      (BP.0≤x⇒nonNegx (BP.p≤q⇒p⋆≤q⋆ 0ℚᵘ Half.half
        (Q.*≤* (Z.+≤+ z≤n)))) n)

arcReserveSuccessor : ∀ n →
  B._≃_ (arcReserve (suc n)) (B.pow Half.bishopHalf n)
arcReserveSuccessor n =
  let open BP.ℝ-Solver
  in solve 1
    (λ p → Κ (+ 2 / 1) ⊗ (p ⊗ Κ (+ 1 / 2)) ⊜ p)
    BP.≃-refl (B.pow Half.bishopHalf n)

arcPrefixReserveBound :
  ∀ s → B.NonNegative s →
  B._≤_ (B.∣_∣ s) Half.bishopQuarter →
  ∀ n →
  B._≤_ (B._+_ (Seq.SeriesOf (term arcCoefficient s) n) (arcReserve n)) twoB
arcPrefixReserveBound s sn inside zero =
  BP.≤-reflexive
    (let open BP.ℝ-Solver
     in solve 0
        (Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ Κ 1ℚᵘ) ⊜ Κ (+ 2 / 1))
        BP.≃-refl)
arcPrefixReserveBound s sn inside (suc n) =
  let partial = Seq.SeriesOf (term arcCoefficient s) n
      p = B.pow Half.bishopHalf n
      t = term arcCoefficient s n
      stepEq = BP.+-congˡ (B._+_ partial t) (arcReserveSuccessor n)
      bound = BP.+-mono-≤
        (BP.+-monoʳ-≤ partial (arcTermBelowHalfPower s sn inside n))
        BP.≤-refl
      shape =
        let open BP.ℝ-Solver
        in solve 2
          (λ a p → (a ⊕ p) ⊕ p ⊜ a ⊕ (Κ (+ 2 / 1) ⊗ p))
          BP.≃-refl partial p
  in BP.≤-trans
      (BP.≤-respʳ-≃ shape (BP.≤-respˡ-≃ stepEq bound))
      (arcPrefixReserveBound s sn inside n)

arcPrefixBelowTwo : ∀ s → B.NonNegative s →
  B._≤_ (B.∣_∣ s) Half.bishopQuarter →
  ∀ n → B._≤_ (Seq.SeriesOf (term arcCoefficient s) n) twoB
arcPrefixBelowTwo s sn inside n =
  let partial = Seq.SeriesOf (term arcCoefficient s) n
  in BP.≤-trans
    (BP.≤-respˡ-≃ (BP.≃-symm (BP.+-identityʳ partial))
      (BP.+-monoʳ-≤ partial (BP.nonNegx⇒0≤x (arcReserveNonnegative n))))
    (arcPrefixReserveBound s sn inside n)

arcSeriesBelowTwo :
  ∀ s → B.NonNegative s →
  (inside : B._≤_ (B.∣_∣ s) Half.bishopQuarter) →
  B._≤_ (arcSeries s inside) twoB
arcSeriesBelowTwo s sn inside =
  Seq.xₙ≤yₙ⇒limxₙ≤limyₙ
    (arcPrefixBelowTwo s sn inside)
    (convergent arcCoefficient s arcNN arcStep inside)
    (twoB , Seq.xₙ≃c⇒xₙ→c (λ _ → BP.≃-refl))

arcSeriesNonnegative :
  ∀ s → B.NonNegative s →
  (inside : B._≤_ (B.∣_∣ s) Half.bishopQuarter) →
  B._≤_ B.0ℝ (arcSeries s inside)
arcSeriesNonnegative s sn inside =
  Seq.xₙisIncreasing⇒xₙ≤limxₙ
    (λ n →
      let partial = Seq.SeriesOf (term arcCoefficient s) n
      in BP.≤-respˡ-≃ (BP.≃-symm (BP.+-identityʳ partial))
        (BP.+-monoʳ-≤ partial
          (BP.nonNegx⇒0≤x (positiveTermNN arcCoefficient s n arcNN sn))))
    (convergent arcCoefficient s arcNN arcStep inside)
    zero
