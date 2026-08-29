module DASHI.Physics.YangMills.BalabanClayT4SineDeterminesCosineAtomExact where

------------------------------------------------------------------------
-- ROUND87: DELETE AN INDEPENDENT COSINE-BOX PRODUCER
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang--Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Marc Daumas, David Lester and Cesar Munoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- MATHEMATICAL ROLE
--
-- The current literal one-loop atom environment asks for independent interval
-- producers for sin(k/2) and cos(k), and a later FP/Wilson bridge asks that they
-- satisfy
--
--        2 - 2 cos(k) = 4 sin^2(k/2).
--
-- For the finite beta evaluator this duplicates transcendental work.  Instead,
-- take the sine-half atom as primitive and DEFINE the coherent cosine atom by
--
--        cos_coh(k) := 1 - 2 sin^2(k/2).
--
-- Its Bishop-real interval is then derived using the already-proved four-corner
-- multiplication and subtraction semantics.  Hence only the sine-half box needs
-- an independent transcendental enclosure.  The remaining physical semantic
-- weld is the standard same-momentum identity cos_coh(k) = cos(k) for the
-- literal Fourier convention; interval certification no longer pays for both
-- functions independently.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _/_)

import Real as Bishop
import RealProperties as BishopP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Product
import DASHI.Physics.YangMills.BalabanClayT4BishopExpressionIntervalSemanticsExact as Sem
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical

record PhysicalSineHalfBoxData : Set₁ where
  field
    sineHalfValue : Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
    sineHalfInterval : Eval.MomentumRole → Eval.AxisIndex → Eval.RationalInterval
    sineHalfSound : ∀ role axis →
      Product.BishopLiesIn
        (sineHalfValue role axis)
        (sineHalfInterval role axis)
open PhysicalSineHalfBoxData public

sineSquareValue : PhysicalSineHalfBoxData → Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
sineSquareValue dataSet role axis =
  sineHalfValue dataSet role axis Bishop.* sineHalfValue dataSet role axis

sineSquareInterval : PhysicalSineHalfBoxData → Eval.MomentumRole → Eval.AxisIndex → Eval.RationalInterval
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

twoSineSquareValue : PhysicalSineHalfBoxData → Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
twoSineSquareValue dataSet role axis =
  Canonical.twoValue Bishop.* sineSquareValue dataSet role axis

twoSineSquareInterval : PhysicalSineHalfBoxData → Eval.MomentumRole → Eval.AxisIndex → Eval.RationalInterval
twoSineSquareInterval dataSet role axis =
  Typed.multiplyInterval
    (Canonical.singletonInterval Canonical.twoRational)
    (sineSquareInterval dataSet role axis)

twoSineSquareSound : ∀ dataSet role axis →
  Product.BishopLiesIn
    (twoSineSquareValue dataSet role axis)
    (twoSineSquareInterval dataSet role axis)
twoSineSquareSound dataSet role axis =
  Product.multiplyIntervalBishopSound
    (Canonical.singletonSound Canonical.twoRational)
    (sineSquareSound dataSet role axis)

derivedCosineFullValue : PhysicalSineHalfBoxData → Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
derivedCosineFullValue dataSet role axis =
  Canonical.oneValue Bishop.- twoSineSquareValue dataSet role axis

derivedCosineFullInterval : PhysicalSineHalfBoxData → Eval.MomentumRole → Eval.AxisIndex → Eval.RationalInterval
derivedCosineFullInterval dataSet role axis =
  Typed.subtractInterval
    (Canonical.singletonInterval Canonical.oneRational)
    (twoSineSquareInterval dataSet role axis)

derivedCosineFullSound : ∀ dataSet role axis →
  Product.BishopLiesIn
    (derivedCosineFullValue dataSet role axis)
    (derivedCosineFullInterval dataSet role axis)
derivedCosineFullSound dataSet role axis =
  Sem.subtractIntervalBishopSound
    (Canonical.singletonSound Canonical.oneRational)
    (twoSineSquareSound dataSet role axis)

derivedPhysicalTrigBoxData : PhysicalSineHalfBoxData → Canonical.PhysicalTrigBoxData
derivedPhysicalTrigBoxData dataSet = record
  { Canonical.PhysicalTrigBoxData.sineHalfValue = sineHalfValue dataSet
  ; Canonical.PhysicalTrigBoxData.cosineFullValue = derivedCosineFullValue dataSet
  ; Canonical.PhysicalTrigBoxData.sineHalfInterval = sineHalfInterval dataSet
  ; Canonical.PhysicalTrigBoxData.cosineFullInterval = derivedCosineFullInterval dataSet
  ; Canonical.PhysicalTrigBoxData.sineHalfSound = sineHalfSound dataSet
  ; Canonical.PhysicalTrigBoxData.cosineFullSound = derivedCosineFullSound dataSet
  }

-- Setoid-real half-angle coherence of the derived atom.  The identity is pure
-- ordered-ring algebra after the definition above; no second transcendental
-- enclosure is used.
derivedHalfAngleCoherence : ∀ dataSet role axis →
  Bishop._≃_
    (Canonical.twoValue Bishop.-
      (Canonical.twoValue Bishop.* derivedCosineFullValue dataSet role axis))
    (Canonical.scaledSineSquareValue
      (derivedPhysicalTrigBoxData dataSet) role axis)
derivedHalfAngleCoherence dataSet role axis =
  let open BishopP.ℝ-Solver
  in solve 1
      (λ s →
        Κ (+ 2 / 1)
          ⊖ (Κ (+ 2 / 1)
            ⊗ (Κ (+ 1 / 1) ⊖ (Κ (+ 2 / 1) ⊗ (s ⊗ s))))
        ⊜ Κ (+ 4 / 1) ⊗ (s ⊗ s))
      BishopP.≃-refl
      (sineHalfValue dataSet role axis)

sineHalfDeterminesCosineIntervalLevel : ProofLevel
sineHalfDeterminesCosineIntervalLevel = machineChecked

derivedHalfAngleCoherenceLevel : ProofLevel
derivedHalfAngleCoherenceLevel = machineChecked

-- Remaining literal Fourier semantic seam only: identify the physical cosine
-- appearing in the Wilson/FP Fourier formula with this coherent half-angle
-- definition.  This is one standard same-momentum trigonometric identity, not a
-- second interval-enclosure programme.
literalFourierCosineIsDerivedHalfAngleCosineLevel : ProofLevel
literalFourierCosineIsDerivedHalfAngleCosineLevel = standardImported
