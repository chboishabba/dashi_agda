module DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- Ludwig D. Faddeev and Victor N. Popov, "Feynman Diagrams for the
-- Yang--Mills Field", Physics Letters B 25 (1967), 29--30.
-- DOI: 10.1016/0370-2693(67)90067-6.
--
-- Luis F. Abbott, "The Background Field Method Beyond One Loop", Nuclear
-- Physics B 185 (1981), 189--203. DOI: 10.1016/0550-3213(81)90371-0.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Build the canonical SU(2), background-Feynman-gauge Bishop atom environment
-- from ONLY the genuine transcendental leaves:
--
--   sin(k_mu/2) and cos(k_mu).
--
-- The lattice momentum atom is not an independent receipt.  Its value and
-- interval are constructed from the literal Wilson definition
--
--       hat{k}^2 = 4 sum_mu sin^2(k_mu/2),
--
-- using the already-proved Bishop four-corner multiplication and additive
-- interval semantics.  The SU(2) adjoint Casimir and canonical gauge parameter
-- are exact singleton atoms 2 and 1.  Hence the L3 semantic frontier is reduced
-- to physical sine/cosine box enclosures alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _/_)
import Data.Rational.Properties as ℚP

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Product
import DASHI.Physics.YangMills.BalabanClayT4BishopExpressionIntervalSemanticsExact as Sem
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PhysicalTrigBoxData : Set₁ where
  field
    sineHalfValue : Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
    cosineFullValue : Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
    sineHalfInterval : Eval.MomentumRole → Eval.AxisIndex → Eval.RationalInterval
    cosineFullInterval : Eval.MomentumRole → Eval.AxisIndex → Eval.RationalInterval
    sineHalfSound : ∀ role axis →
      Product.BishopLiesIn
        (sineHalfValue role axis)
        (sineHalfInterval role axis)
    cosineFullSound : ∀ role axis →
      Product.BishopLiesIn
        (cosineFullValue role axis)
        (cosineFullInterval role axis)
open PhysicalTrigBoxData public

fourRational twoRational oneRational : ℚ
fourRational = + 4 / 1
twoRational = + 2 / 1
oneRational = + 1 / 1

singletonInterval : ℚ → Eval.RationalInterval
singletonInterval value = Eval.rationalInterval value value ℚP.≤-refl

fourValue twoValue oneValue : Bishop.ℝ
fourValue = Product.embed fourRational
twoValue = Product.embed twoRational
oneValue = Product.embed oneRational

singletonSound : ∀ rational →
  Product.BishopLiesIn (Product.embed rational) (singletonInterval rational)
singletonSound rational = Product.bishopLiesIn BishopP.≤-refl BishopP.≤-refl

sineSquareValue : PhysicalTrigBoxData → Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
sineSquareValue dataSet role axis =
  sineHalfValue dataSet role axis Bishop.* sineHalfValue dataSet role axis

sineSquareInterval : PhysicalTrigBoxData → Eval.MomentumRole → Eval.AxisIndex → Eval.RationalInterval
sineSquareInterval dataSet role axis =
  Typed.multiplyInterval
    (sineHalfInterval dataSet role axis)
    (sineHalfInterval dataSet role axis)

sineSquareSound : ∀ dataSet role axis →
  Product.BishopLiesIn
    (sineSquareValue dataSet role axis)
    (sineSquareInterval dataSet role axis)
sineSquareSound dataSet role axis =
  Product.multiplyIntervalBishopSound
    (sineHalfSound dataSet role axis)
    (sineHalfSound dataSet role axis)

scaledSineSquareValue : PhysicalTrigBoxData → Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
scaledSineSquareValue dataSet role axis =
  fourValue Bishop.* sineSquareValue dataSet role axis

scaledSineSquareInterval : PhysicalTrigBoxData → Eval.MomentumRole → Eval.AxisIndex → Eval.RationalInterval
scaledSineSquareInterval dataSet role axis =
  Typed.multiplyInterval
    (singletonInterval fourRational)
    (sineSquareInterval dataSet role axis)

scaledSineSquareSound : ∀ dataSet role axis →
  Product.BishopLiesIn
    (scaledSineSquareValue dataSet role axis)
    (scaledSineSquareInterval dataSet role axis)
scaledSineSquareSound dataSet role axis =
  Product.multiplyIntervalBishopSound
    (singletonSound fourRational)
    (sineSquareSound dataSet role axis)

hatMomentumValue : PhysicalTrigBoxData → Eval.MomentumRole → Bishop.ℝ
hatMomentumValue dataSet role =
  scaledSineSquareValue dataSet role Eval.axis0 Bishop.+
  scaledSineSquareValue dataSet role Eval.axis1 Bishop.+
  scaledSineSquareValue dataSet role Eval.axis2 Bishop.+
  scaledSineSquareValue dataSet role Eval.axis3

hatMomentumInterval : PhysicalTrigBoxData → Eval.MomentumRole → Eval.RationalInterval
hatMomentumInterval dataSet role =
  Typed.addInterval
    (Typed.addInterval
      (scaledSineSquareInterval dataSet role Eval.axis0)
      (scaledSineSquareInterval dataSet role Eval.axis1))
    (Typed.addInterval
      (scaledSineSquareInterval dataSet role Eval.axis2)
      (scaledSineSquareInterval dataSet role Eval.axis3))

hatMomentumSound : ∀ dataSet role →
  Product.BishopLiesIn
    (hatMomentumValue dataSet role)
    (hatMomentumInterval dataSet role)
hatMomentumSound dataSet role =
  Sem.addIntervalBishopSound
    (Sem.addIntervalBishopSound
      (scaledSineSquareSound dataSet role Eval.axis0)
      (scaledSineSquareSound dataSet role Eval.axis1))
    (Sem.addIntervalBishopSound
      (scaledSineSquareSound dataSet role Eval.axis2)
      (scaledSineSquareSound dataSet role Eval.axis3))

canonicalAtomValue : PhysicalTrigBoxData → Eval.TrigAtom → Bishop.ℝ
canonicalAtomValue dataSet (Eval.sineHalf role axis) = sineHalfValue dataSet role axis
canonicalAtomValue dataSet (Eval.cosineFull role axis) = cosineFullValue dataSet role axis
canonicalAtomValue dataSet (Eval.hatMomentumSquared role) = hatMomentumValue dataSet role
canonicalAtomValue dataSet Eval.colorCasimir = twoValue
canonicalAtomValue dataSet Eval.gaugeParameter = oneValue

canonicalAtomInterval : PhysicalTrigBoxData → Eval.TrigAtom → Eval.RationalInterval
canonicalAtomInterval dataSet (Eval.sineHalf role axis) = sineHalfInterval dataSet role axis
canonicalAtomInterval dataSet (Eval.cosineFull role axis) = cosineFullInterval dataSet role axis
canonicalAtomInterval dataSet (Eval.hatMomentumSquared role) = hatMomentumInterval dataSet role
canonicalAtomInterval dataSet Eval.colorCasimir = singletonInterval twoRational
canonicalAtomInterval dataSet Eval.gaugeParameter = singletonInterval oneRational

canonicalAtomSound : ∀ dataSet atom →
  Product.BishopLiesIn
    (canonicalAtomValue dataSet atom)
    (canonicalAtomInterval dataSet atom)
canonicalAtomSound dataSet (Eval.sineHalf role axis) = sineHalfSound dataSet role axis
canonicalAtomSound dataSet (Eval.cosineFull role axis) = cosineFullSound dataSet role axis
canonicalAtomSound dataSet (Eval.hatMomentumSquared role) = hatMomentumSound dataSet role
canonicalAtomSound dataSet Eval.colorCasimir = singletonSound twoRational
canonicalAtomSound dataSet Eval.gaugeParameter = singletonSound oneRational

canonicalBishopAtomEnvironment :
  PhysicalTrigBoxData → Sem.BishopAtomEnvironment
canonicalBishopAtomEnvironment dataSet = record
  { Sem.BishopAtomEnvironment.atomValue = canonicalAtomValue dataSet
  ; Sem.BishopAtomEnvironment.atomInterval = canonicalAtomInterval dataSet
  ; Sem.BishopAtomEnvironment.atomSound = canonicalAtomSound dataSet
  }

canonicalSU2ColorCasimirAtomLevel : ProofLevel
canonicalSU2ColorCasimirAtomLevel = machineChecked

canonicalBackgroundFeynmanGaugeAtomLevel : ProofLevel
canonicalBackgroundFeynmanGaugeAtomLevel = machineChecked

literalWilsonHatMomentumFromSineAtomsLevel : ProofLevel
literalWilsonHatMomentumFromSineAtomsLevel = machineChecked

-- Remaining transcendental atom producer only:
--   sineHalfSound / cosineFullSound on the actual physical box coordinates.
physicalTrigBoxDataProducerLevel : ProofLevel
physicalTrigBoxDataProducerLevel = conditional
