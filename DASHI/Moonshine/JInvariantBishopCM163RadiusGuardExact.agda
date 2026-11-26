module DASHI.Moonshine.JInvariantBishopCM163RadiusGuardExact where

-- SOURCE-WRITTEN, UNCOMPILED. On the actual selected Bishop chart:
-- pi_M >= 3, sqrt(163) >= 12, exponent >= 36; use the first FOUR
-- terms (the cubic alone is >= 7776), not a decimal CM approximation.
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
open import Data.Nat.Base using (s≤s; z≤n)
open import Data.Sum.Base using (inj₂)
open import Relation.Nullary.Decidable.Core using (from-yes)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆; _≤_; _<_)
import RealProperties as P
import Sequence as S
import Inverse as Inv
import DASHI.Foundations.BishopNatSquareRootPositiveExact as RootPos
import DASHI.Foundations.BishopNatSquareRootSemanticSquareExact as RootSq
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflect
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Foundations.BishopMachinPiRationalWindowExact as MW
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as EP
import DASHI.Foundations.BishopExponentialCubicTranslationLowerExact as Cubic
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as Neg
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as MP
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM

ratNN : (p : Q.ℚᵘ) → Q.0ℚᵘ Q.≤ p → R.NonNegative (p ⋆)
ratNN p h = P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ Q.0ℚᵘ p h)

ratLe : (p q : Q.ℚᵘ) → p Q.≤ q → (p ⋆) ≤ (q ⋆)
ratLe = P.p≤q⇒p⋆≤q⋆

ratLt : (p q : Q.ℚᵘ) → p Q.< q → (p ⋆) < (q ⋆)
ratLt = P.p<q⇒p⋆<q⋆

nn12 : R.NonNegative ((+ 12 / 1) ⋆)
nn12 = ratNN (+ 12 / 1) (QP.nonNegative⁻¹ (+ 12 / 1))

rootNN : R.NonNegative N.r
rootNN = P.pos⇒nonNeg (RootPos.canonicalFloorSquareRootPositive (s≤s z≤n))

rootLower : ((+ 12 / 1) ⋆) ≤ N.r
rootLower = Reflect.squareReflectsOnNonnegative nn12 rootNN
  (P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 0
      (Κ (+ 144 / 1) ⊜ Κ (+ 12 / 1) ⊗ Κ (+ 12 / 1)) P.≃-refl)
    (P.≤-respʳ-≃ (P.≃-symm (RootSq.canonicalFloorSquareRootSquaresToNat 163))
      (ratLe (+ 144 / 1) (+ 163 / 1)
        (from-yes ((+ 144 / 1) QP.≤? (+ 163 / 1))))))

exponent : ℝ
exponent = Radius.qExponentMagnitude M.bishopMachinPi CM.imag

exponentShape : exponent ≃ (M.bishopMachinPi * N.r)
exponentShape = let open P.ℝ-Solver in solve 2
  (λ p r → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ r) ⊜ p ⊗ r)
  P.≃-refl M.bishopMachinPi N.r

exponentPositive : R.0ℝ < exponent
exponentPositive = Radius.qExponentMagnitudePositive MP.machinPiPositive CM.imagPositive

exponentNN : R.NonNegative exponent
exponentNN = P.0≤x⇒nonNegx (P.<⇒≤ exponentPositive)

exponentLower : ((+ 36 / 1) ⋆) ≤ exponent
exponentLower = P.≤-respʳ-≃ (P.≃-symm exponentShape)
  (P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 0
      (Κ (+ 3 / 1) ⊗ Κ (+ 12 / 1) ⊜ Κ (+ 36 / 1)) P.≃-refl)
    (P.≤-trans (P.*-monoˡ-≤-nonNeg rootLower
      (ratNN (+ 3 / 1) (QP.nonNegative⁻¹ (+ 3 / 1))))
      (P.*-monoʳ-≤-nonNeg MW.threeBelowMachinPiNonStrict rootNN)))

-- The third-power term alone dominates the required 1024 threshold.
lowerSquare : ((+ 36 / 1) ⋆) * ((+ 36 / 1) ⋆) ≤ exponent * exponent
lowerSquare = P.≤-trans
  (P.*-monoˡ-≤-nonNeg exponentLower
    (ratNN (+ 36 / 1) (QP.nonNegative⁻¹ (+ 36 / 1))))
  (P.*-monoʳ-≤-nonNeg exponentLower exponentNN)

lowerCube : (((+ 36 / 1) ⋆) * ((+ 36 / 1) ⋆)) * ((+ 36 / 1) ⋆)
  ≤ (exponent * exponent) * exponent
lowerCube = P.≤-trans
  (P.*-monoʳ-≤-nonNeg lowerSquare
    (ratNN (+ 36 / 1) (QP.nonNegative⁻¹ (+ 36 / 1))))
  (P.*-monoˡ-≤-nonNeg exponentLower (P.nonNegx,y⇒nonNegx*y exponentNN exponentNN))

cubicPart : ℝ
cubicPart = Cubic.oneSixth * Cubic.cube exponent

cubicLower : ((+ 7776 / 1) ⋆) ≤ cubicPart
cubicLower = P.≤-respˡ-≃
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 1 / 6) ⊗ ((Κ (+ 36 / 1) ⊗ Κ (+ 36 / 1)) ⊗ Κ (+ 36 / 1))
      ⊜ Κ (+ 7776 / 1)) P.≃-refl)
  (P.*-monoˡ-≤-nonNeg lowerCube (ratNN (+ 1 / 6) (QP.nonNegative⁻¹ (+ 1 / 6))))

cubicBelowExp : cubicPart ≤ Exp.bishopExp exponent
cubicBelowExp = P.≤-trans
  (P.≤-respˡ-≃ (P.+-identityˡ cubicPart)
    (P.+-monoˡ-≤ cubicPart
      (S.0≤x,y⇒0≤x+y
        (S.0≤x,y⇒0≤x+y (P.<⇒≤ Neg.onePositive) (P.nonNegx⇒0≤x exponentNN))
        (P.nonNegx⇒0≤x (P.nonNegx,y⇒nonNegx*y
          (ratNN (+ 1 / 2) (QP.nonNegative⁻¹ (+ 1 / 2)))
          (P.nonNegx,y⇒nonNegx*y exponentNN exponentNN))))))
  (P.≤-respˡ-≃ (Cubic.expFirstFourTerms exponent)
    (S.xₙisIncreasing⇒xₙ≤limxₙ (EP.expPartialSumsIncreasing exponentNN)
      (EP.expSeriesConvergent exponent) 4))

expLower : ((+ 1024 / 1) ⋆) < Exp.bishopExp exponent
expLower = P.<-≤-trans
  (ratLt (+ 1024 / 1) (+ 7776 / 1)
    (from-yes ((+ 1024 / 1) QP.<? (+ 7776 / 1))))
  (P.≤-trans cubicLower cubicBelowExp)

thresholdPositive : R.0ℝ < ((+ 1024 / 1) ⋆)
thresholdPositive = ratLt Q.0ℚᵘ (+ 1024 / 1) (QP.positive⁻¹ (+ 1024 / 1))

thresholdNZ : R._≄0 ((+ 1024 / 1) ⋆)
thresholdNZ = inj₂ thresholdPositive

thresholdInverse : Inv._⁻¹ ((+ 1024 / 1) ⋆) thresholdNZ ≃ ((+ 1 / 1024) ⋆)
thresholdInverse = P.≃-symm (Inv.⁻¹-unique ((+ 1 / 1024) ⋆)
  ((+ 1024 / 1) ⋆) thresholdNZ
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 1024 / 1) ⊗ Κ (+ 1 / 1024) ⊜ Κ Q.1ℚᵘ) P.≃-refl))

radiusPositive : R.0ℝ < CM.radius
radiusPositive = Neg.negativeExpPositive exponentPositive

radiusSmall : CM.radius < ((+ 1 / 1024) ⋆)
radiusSmall = P.<-respʳ-≃ thresholdInverse
  (P.<-respˡ-≃ (P.≃-symm (Neg.negativeExpIsInversePositiveExp exponentPositive))
    (Inv.x<y∧posx,y⇒y⁻¹<x⁻¹ expLower thresholdNZ
      (Neg.expNonzero exponentPositive) (P.0<x⇒posx thresholdPositive)
      (P.0<x⇒posx (Neg.expPositive exponentPositive))))

-- The existing cubic certificate actually suffices for the stronger
-- absolutely-convergent composition disk, without a new exp series.
expLower7000 : ((+ 7000 / 1) ⋆) < Exp.bishopExp exponent
expLower7000 = P.<-≤-trans
  (ratLt (+ 7000 / 1) (+ 7776 / 1)
    (from-yes ((+ 7000 / 1) QP.<? (+ 7776 / 1))))
  (P.≤-trans cubicLower cubicBelowExp)

threshold7000Positive : R.0ℝ < ((+ 7000 / 1) ⋆)
threshold7000Positive = ratLt Q.0ℚᵘ (+ 7000 / 1) (QP.positive⁻¹ (+ 7000 / 1))

threshold7000NZ : R._≄0 ((+ 7000 / 1) ⋆)
threshold7000NZ = inj₂ threshold7000Positive

threshold7000Inverse : Inv._⁻¹ ((+ 7000 / 1) ⋆) threshold7000NZ ≃ ((+ 1 / 7000) ⋆)
threshold7000Inverse = P.≃-symm (Inv.⁻¹-unique ((+ 1 / 7000) ⋆)
  ((+ 7000 / 1) ⋆) threshold7000NZ
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 7000 / 1) ⊗ Κ (+ 1 / 7000) ⊜ Κ Q.1ℚᵘ) P.≃-refl))

radiusCompositionSmall : CM.radius < ((+ 1 / 7000) ⋆)
radiusCompositionSmall = P.<-respʳ-≃ threshold7000Inverse
  (P.<-respˡ-≃ (P.≃-symm (Neg.negativeExpIsInversePositiveExp exponentPositive))
    (Inv.x<y∧posx,y⇒y⁻¹<x⁻¹ expLower7000 threshold7000NZ
      (Neg.expNonzero exponentPositive) (P.0<x⇒posx threshold7000Positive)
      (P.0<x⇒posx (Neg.expPositive exponentPositive))))
