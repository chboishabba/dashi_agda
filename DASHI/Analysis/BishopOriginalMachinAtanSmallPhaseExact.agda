module DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact where

-- Native K05 phase increment, using the original all-stage atan remainder
-- and the original Round11 factorial Taylor brackets.  No sign decision
-- on an arbitrary real: a nonnegative mesh increment <= 1/16 forces the
-- actual angle increment into the nonnegative half ball.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
open import Relation.Nullary.Decidable.Core using (from-yes)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import Inverse as I
import DASHI.Analysis.BishopOriginalMachinAtanSecondOrderExact as Atan2
import DASHI.Analysis.BishopOriginalLogAtanDerivativeLimitValuesExact as D
import DASHI.Foundations.BishopMachinArctanConstructionExact as A
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as One
import DASHI.Foundations.BishopSquareNonnegativeExact as Sq
import DASHI.Foundations.BishopInverseSquareProductExact as Inv
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Product
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as Cong
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Taylor
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route

half two three eight nine sixteen twentyfive tiny : ℝ
half = Atan2.half
two = (+ 2 / 1) ⋆
three = (+ 3 / 1) ⋆
eight = Atan2.eight
nine = (+ 9 / 1) ⋆
sixteen = (+ 16 / 1) ⋆
twentyfive = (+ 25 / 1) ⋆
tiny = (+ 1 / 16) ⋆

ratNN : (q : ℚᵘ) → Q.0ℚᵘ Q.≤ q → R.NonNegative (q ⋆)
ratNN q h = P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ Q.0ℚᵘ q h)

twoNN : R.NonNegative two
twoNN = ratNN (+ 2 / 1) (QP.nonNegative⁻¹ (+ 2 / 1))

threeNN : R.NonNegative three
threeNN = ratNN (+ 3 / 1) (QP.nonNegative⁻¹ (+ 3 / 1))

eightNN : R.NonNegative eight
eightNN = ratNN (+ 8 / 1) (QP.nonNegative⁻¹ (+ 8 / 1))

-- Use the existing literal half-ball inequality rather than decide
-- order on Bishop reals.
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
half≤one : half ≤ R.1ℝ
half≤one = P.<⇒≤ Exp.halfBelowOne

absNN : ∀ {x} → R.NonNegative x → ∣ x ∣ ≃ x
absNN = P.nonNegx⇒∣x∣≃x

absFlip : ∀ x y → ∣ (x - y) ∣ ≃ ∣ (y - x) ∣
absFlip = P.∣x-y∣≃∣y-x∣

absUpper : ∀ {x b} → ∣ x ∣ ≤ b → x ≤ b
absUpper h = P.≤-trans P.x≤∣x∣ h

absLower : ∀ {x b} → ∣ x ∣ ≤ b → R.- b ≤ x
absLower {x} {b} h =
  P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 1 (λ x → ⊝ (⊝ x) ⊜ x) P.≃-refl x)
    (P.neg-mono-≤ (P.≤-trans (P.x≤∣x∣ {x = R.- x})
      (P.≤-respˡ-≃ (P.∣-x∣≃∣x∣ {x = x}) h)))

boundMul : ∀ {a b A B} → ∣ a ∣ ≤ A → ∣ b ∣ ≤ B → ∣ (a * b) ∣ ≤ (A * B)
boundMul {a} {b} ha hb = P.≤-respˡ-≃ (P.∣x*y∣≃∣x∣*∣y∣ a b)
  (P.*-mono-≤ (P.nonNeg∣x∣ a) (P.nonNeg∣x∣ b) ha hb)

boundAdd : ∀ {a b A B} → ∣ a ∣ ≤ A → ∣ b ∣ ≤ B → ∣ (a + b) ∣ ≤ (A + B)
boundAdd {a} {b} ha hb = P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ a b) (P.+-mono-≤ ha hb)

boundSub : ∀ {a b A B} → ∣ a ∣ ≤ A → ∣ b ∣ ≤ B → ∣ (a - b) ∣ ≤ (A + B)
boundSub {a} {b} ha hb = boundAdd ha (P.≤-respˡ-≃ (P.∣-x∣≃∣x∣ {x = b}) hb)

record Point : Set where
  constructor point
  field
    x : ℝ
    nn : R.NonNegative x
    inside : x ≤ half
open Point public

asHalf : (p : Point) → ∣ x p ∣ ≤ half
asHalf p = P.≤-respˡ-≃ (absNN (nn p)) (inside p)

atan : Point → ℝ
atan p = A.bishopAtanHalfBall (x p) (asHalf p)

d : Point → ℝ
d p = Atan2.derivativeValue (x p) (asHalf p)

denom : ℝ → ℝ
denom x = R.1ℝ + x * x

dCancels : ∀ p → denom (x p) * d p ≃ R.1ℝ
dCancels p = D.originalAtanSourceDerivativeLimitIsReciprocal (x p) (asHalf p)

denomLower : ∀ x → R.1ℝ ≤ denom x
denomLower x = P.≤-respˡ-≃ (P.≃-symm (P.+-identityʳ R.1ℝ))
  (P.+-mono-≤ P.≤-refl (P.nonNegx⇒0≤x (Sq.bishopSquareNonnegative x)))

denomUpper : ∀ p → denom (x p) ≤ two
denomUpper p = P.≤-respʳ-≃
  (let open P.ℝ-Solver in solve 0 (Κ Q.1ℚᵘ ⊕ Κ Q.1ℚᵘ ⊜ Κ (+ 2 / 1)) P.≃-refl)
  (P.+-mono-≤ P.≤-refl
    (P.≤-respʳ-≃ (P.*-identityʳ R.1ℝ)
      (P.*-mono-≤ (nn p) (nn p) (P.≤-trans (inside p) half≤one)
        (P.≤-trans (inside p) half≤one))))

denomPositive : ∀ x → R.0ℝ < denom x
denomPositive x = P.<-≤-trans One.onePositive (denomLower x)

dNN : ∀ p → R.NonNegative (d p)
dNN p =
  let a = denom (x p)
      pos = denomPositive (x p)
      nz = inj₂ pos
      same = I.⁻¹-unique (d p) a nz (dCancels p)
  in P.nonNeg-cong (P.≃-symm same)
       (P.pos⇒nonNeg (P.0<x⇒posx (I.0<x⇒0<x⁻¹ nz pos)))

dUpper : ∀ p → d p ≤ R.1ℝ
dUpper p = P.≤-respˡ-≃ (P.≃-symm (P.*-identityˡ (d p)))
  (P.≤-respʳ-≃ (dCancels p)
    (P.*-monoʳ-≤-nonNeg (denomLower (x p)) (dNN p)))

dLower : ∀ p → half ≤ d p
dLower p = P.≤-respʳ-≃
  (let open P.ℝ-Solver in solve 1 (λ d → Κ (+ 1 / 2) ⊗ (Κ (+ 2 / 1) ⊗ d) ⊜ d) P.≃-refl (d p))
  (P.≤-respˡ-≃ (P.≃-symm (P.*-identityʳ half))
    (P.*-monoˡ-≤-nonNeg
      (P.≤-respˡ-≃ (P.≃-symm (dCancels p))
        (P.*-monoʳ-≤-nonNeg (denomUpper p) (dNN p)))
      Atan2.halfNN))

next : (p : Point) (h : ℝ) → R.NonNegative (x p + h) → (x p + h) ≤ half → Point
next p h yn yr = point (x p + h) yn yr

module Cell (p : Point) (h : ℝ) (hn : R.NonNegative h) (ht : h ≤ tiny)
            (yn : R.NonNegative (x p + h)) (yr : (x p + h) ≤ half) where
  q = next p h yn yr
  a = atan q - atan p
  err = a - h * d p
  h2 = h * h
  angle = two * a

  h2NN : R.NonNegative h2
  h2NN = Sq.bishopSquareNonnegative h

  errBound : ∣ err ∣ ≤ eight * h2
  errBound = P.≤-respʳ-≃
    (P.≃-trans (P.*-congʳ (P.*-cong (absNN hn) (absNN hn)))
      (P.*-comm h2 eight))
    (Atan2.actualRemainderBound (x p) h (nn p) yn (inside p) yr)

  errorSmall : eight * h2 ≤ half * h
  errorSmall = P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 1
      (λ h → Κ (+ 8 / 1) ⊗ (h ⊗ h) ⊜ h ⊗ (Κ (+ 8 / 1) ⊗ h)) P.≃-refl h)
    (P.≤-respʳ-≃
      (let open P.ℝ-Solver in solve 1
        (λ h → h ⊗ (Κ (+ 8 / 1) ⊗ Κ (+ 1 / 16)) ⊜ Κ (+ 1 / 2) ⊗ h) P.≃-refl h)
      (P.*-monoˡ-≤-nonNeg (P.*-monoˡ-≤-nonNeg ht eightNN) hn))

  aRead : a ≃ (h * d p + err)
  aRead = let open P.ℝ-Solver in solve 2
    (λ a b → a ⊜ b ⊕ (a ⊖ b)) P.≃-refl a (h * d p)

  aNonnegative : R.NonNegative a
  aNonnegative = P.0≤x⇒nonNegx
    (P.≤-respʳ-≃ (P.≃-symm aRead)
      (P.≤-respˡ-≃
        (let open P.ℝ-Solver in solve 1
          (λ h → Κ Q.0ℚᵘ ⊜ (h ⊗ Κ (+ 1 / 2)) ⊕ (⊝ (Κ (+ 1 / 2) ⊗ h))) P.≃-refl h)
        (P.+-mono-≤ (P.*-monoˡ-≤-nonNeg (dLower p) hn)
          (absLower (P.≤-trans errBound errorSmall)))))

  aUpper : a ≤ ((+ 3 / 2) ⋆) * h
  aUpper = P.≤-respˡ-≃ aRead
    (P.≤-respʳ-≃
      (let open P.ℝ-Solver in solve 1
        (λ h → h ⊗ Κ Q.1ℚᵘ ⊕ Κ (+ 1 / 2) ⊗ h ⊜ Κ (+ 3 / 2) ⊗ h) P.≃-refl h)
      (P.+-mono-≤ (P.*-monoˡ-≤-nonNeg (dUpper p) hn)
        (absUpper (P.≤-trans errBound errorSmall))))

  angleNN : R.NonNegative angle
  angleNN = P.nonNegx,y⇒nonNegx*y twoNN aNonnegative

  angleBound : angle ≤ three * h
  angleBound = P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 1
      (λ h → Κ (+ 2 / 1) ⊗ (Κ (+ 3 / 2) ⊗ h) ⊜ Κ (+ 3 / 1) ⊗ h) P.≃-refl h)
    (P.*-monoˡ-≤-nonNeg aUpper twoNN)

  angleHalf : angle ≤ half
  angleHalf = P.≤-trans angleBound
    (P.≤-trans (P.*-monoˡ-≤-nonNeg ht threeNN)
      (P.≤-respˡ-≃
        (let open P.ℝ-Solver in solve 0
          (Κ (+ 3 / 1) ⊗ Κ (+ 1 / 16) ⊜ Κ (+ 3 / 16)) P.≃-refl)
        (P.p≤q⇒p⋆≤q⋆ (+ 3 / 16) (+ 1 / 2)
          (from-yes ((+ 3 / 16) QP.≤? (+ 1 / 2))))))

  angleSquareBound : angle * angle ≤ nine * h2
  angleSquareBound = P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 1
      (λ h → (Κ (+ 3 / 1) ⊗ h) ⊗ (Κ (+ 3 / 1) ⊗ h) ⊜ Κ (+ 9 / 1) ⊗ (h ⊗ h)) P.≃-refl h)
    (P.*-mono-≤ angleNN angleNN angleBound angleBound)

  angleError : ∣ (angle - (two * h) * d p) ∣ ≤ sixteen * h2
  angleError = P.≤-respˡ-≃
    (P.≃-trans
      (P.∣-∣-cong (let open P.ℝ-Solver in solve 3
        (λ a h d → Κ (+ 2 / 1) ⊗ a ⊖ (Κ (+ 2 / 1) ⊗ h) ⊗ d
          ⊜ Κ (+ 2 / 1) ⊗ (a ⊖ h ⊗ d)) P.≃-refl a h (d p)))
      (P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ two err) (P.*-congʳ (absNN twoNN))))
    (P.≤-respʳ-≃
      (let open P.ℝ-Solver in solve 1
        (λ s → Κ (+ 2 / 1) ⊗ (Κ (+ 8 / 1) ⊗ s) ⊜ Κ (+ 16 / 1) ⊗ s) P.≃-refl h2)
      (P.*-monoˡ-≤-nonNeg errBound twoNN))

  module Trig (inputs : Round11.BishopCutset) where
    T = Route.machinTranscendentals inputs
    c = E.bishopCos (Round11.elementarySeries inputs) angle
    s = E.bishopSin (Round11.elementarySeries inputs) angle

    local : Concrete.ConcreteHalfBallSeriesInputs (Round11.elementarySeries inputs) angle
    local = record
      { termIdentification = Round11.concreteTermIdentification inputs
      ; valueNonnegative = angleNN
      ; insideHalf = P.≤-respˡ-≃ (absNN angleNN) angleHalf
      }
    bounds = Taylor.defectTaylorBounds local

    cosError : ∣ (c - R.1ℝ) ∣ ≤ nine * h2
    cosError = P.≤-respˡ-≃
      (P.≃-trans (absFlip c R.1ℝ)
        (P.0≤x⇒∣x∣≃x (Taylor.cosineDefectNonnegative bounds)))
      (P.≤-trans (Taylor.cosineDefectBelowQuadratic bounds)
        (P.≤-trans
          (P.≤-respʳ-≃ (P.*-identityˡ (angle * angle))
            (P.*-monoʳ-≤-nonNeg half≤one (Sq.bishopSquareNonnegative angle)))
          angleSquareBound))

    sinLinearError : ∣ (s - angle) ∣ ≤ nine * h2
    sinLinearError = P.≤-respˡ-≃
      (P.≃-trans (absFlip s angle)
        (P.0≤x⇒∣x∣≃x (Taylor.sineDefectNonnegative bounds)))
      (P.≤-trans (Taylor.sineDefectBelowCubic bounds)
        (P.≤-trans
          (P.≤-respˡ-≃
            (let open P.ℝ-Solver in solve 1
              (λ t → Κ (+ 1 / 6) ⊗ ((t ⊗ t) ⊗ t) ⊜ (t ⊗ t) ⊗ (Κ (+ 1 / 6) ⊗ t)) P.≃-refl angle)
            (P.≤-respʳ-≃ (P.*-identityʳ (angle * angle))
              (P.*-monoˡ-≤-nonNeg
                (P.≤-trans (P.*-monoˡ-≤-nonNeg (P.≤-trans angleHalf half≤one)
                  (ratNN (+ 1 / 6) (QP.nonNegative⁻¹ (+ 1 / 6))))
                  (P.≤-respˡ-≃ (P.*-identityʳ ((+ 1 / 6) ⋆))
                    (P.p≤q⇒p⋆≤q⋆ (+ 1 / 6) Q.1ℚᵘ
                      (from-yes ((+ 1 / 6) QP.≤? Q.1ℚᵘ)))))
                (Sq.bishopSquareNonnegative angle))))
          angleSquareBound))

    sinError : ∣ (s - (two * h) * d p) ∣ ≤ twentyfive * h2
    sinError = P.≤-respˡ-≃
      (P.∣-∣-cong (let open P.ℝ-Solver in solve 3
        (λ s a b → s ⊖ b ⊜ (s ⊖ a) ⊕ (a ⊖ b)) P.≃-refl s angle ((two * h) * d p)))
      (P.≤-respʳ-≃
        (let open P.ℝ-Solver in solve 1
          (λ t → Κ (+ 9 / 1) ⊗ t ⊕ Κ (+ 16 / 1) ⊗ t ⊜ Κ (+ 25 / 1) ⊗ t) P.≃-refl h2)
        (boundAdd sinLinearError angleError))
