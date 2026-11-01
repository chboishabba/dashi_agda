module DASHI.Physics.YangMills.BalabanSelectedConstraintGramCombesThomasExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Apply the repository's standard finite Combes--Thomas algebra first to the
-- redundancy-safe multiplier Gram operator K=L L*.  No constraint row is
-- deleted.  The spectral floor gamma_L is imposed only on a declared reduced
-- multiplier representative space and is independent of the 1/32 state-
-- Hessian floor.  A certified half-gap and pseudoinverse majorant obey
--
--   2 halfGap = gamma_L,
--   greenMajorant gamma_L = 2.
--
-- The module exposes the exact finite-range stencil, reduced coercivity,
-- diagonal tilt row budget and off-diagonal decay of K+.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _-_; _*_; _≤_; _<_; _/_; ∣_∣)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasTiltBudgetExact as Tilt

record ConstraintGramFiniteRange
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier) : Set₁ where
  field
    distance : Multiplier → Multiplier → ℚ
    interactionRange : ℚ
    interactionRangeNonnegative : 0ℚ ≤ interactionRange
    outsideRangeZero : ∀ left right →
      interactionRange < distance left right →
      Pseudo.constraintGram pseudoData left right ≡ 0ℚ

open ConstraintGramFiniteRange public

selectedConstraintGramFiniteRange :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (finiteRange : ConstraintGramFiniteRange pseudoData)
    left right →
  interactionRange finiteRange < distance finiteRange left right →
  Pseudo.constraintGram pseudoData left right ≡ 0ℚ
selectedConstraintGramFiniteRange finiteRange =
  outsideRangeZero finiteRange

record ConstraintGramReducedFloor
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier) : Set₁ where
  field
    ReducedMultiplier : (Multiplier → ℚ) → Set

    reducedFloor : ℚ
    halfGap : ℚ
    tiltedGreenMajorant : ℚ

    reducedFloorPositive : 0ℚ < reducedFloor
    halfGapNonnegative : 0ℚ ≤ halfGap
    tiltedGreenMajorantNonnegative : 0ℚ ≤ tiltedGreenMajorant

    halfGapCalibration :
      (+ 2 / 1) * halfGap ≡ reducedFloor

    tiltedGreenMajorantCalibration :
      tiltedGreenMajorant * reducedFloor ≡ (+ 2 / 1)

    reducedMultiplierCoercive : ∀ multiplier →
      ReducedMultiplier multiplier →
      reducedFloor
        * Rect.finiteDot
            (Pseudo.multiplierCarrier pseudoData)
            multiplier multiplier
      ≤ Rect.finiteDot
          (Pseudo.multiplierCarrier pseudoData)
          multiplier
          (Pseudo.gramApply pseudoData multiplier)

open ConstraintGramReducedFloor public

selectedConstraintGramReducedFloor :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (floorData : ConstraintGramReducedFloor pseudoData)
    multiplier →
  ReducedMultiplier floorData multiplier →
  reducedFloor floorData
    * Rect.finiteDot
        (Pseudo.multiplierCarrier pseudoData)
        multiplier multiplier
  ≤ Rect.finiteDot
      (Pseudo.multiplierCarrier pseudoData)
      multiplier
      (Pseudo.gramApply pseudoData multiplier)
selectedConstraintGramReducedFloor = reducedMultiplierCoercive

selectedConstraintGramTilt :
  ∀ {Multiplier} →
  (weight inverseWeight : Multiplier → ℚ) →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  CT.Matrix Multiplier
selectedConstraintGramTilt weight inverseWeight pseudoData =
  CT.diagonalConjugate weight inverseWeight
    (Pseudo.constraintGram pseudoData)

selectedConstraintGramTiltDefect :
  ∀ {Multiplier} →
  (weight inverseWeight : Multiplier → ℚ) →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  CT.Matrix Multiplier
selectedConstraintGramTiltDefect weight inverseWeight pseudoData =
  CT.diagonalTiltDefect weight inverseWeight
    (Pseudo.constraintGram pseudoData)

record ConstraintGramTiltCertificate
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (floorData : ConstraintGramReducedFloor pseudoData) : Set₁ where
  field
    weight inverseWeight : Multiplier → ℚ
    distortion rowMass : ℚ

    inverseLaw : ∀ row →
      inverseWeight row * weight row ≡ 1ℚ

    distortionNonnegative : 0ℚ ≤ distortion

    ratioBound : ∀ left right →
      ∣ weight left * inverseWeight right - 1ℚ ∣
      ≤ distortion

    gramRowMassBound : ∀ left →
      Tilt.absoluteRowMass
        (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
        (Pseudo.constraintGram pseudoData) left
      ≤ rowMass

    halfGapBudget :
      distortion * rowMass ≤ halfGap floorData

open ConstraintGramTiltCertificate public

selectedConstraintGramTiltBelowHalfGap :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {floorData : ConstraintGramReducedFloor pseudoData} →
  (certificate : ConstraintGramTiltCertificate pseudoData floorData) →
  ∀ left →
  Tilt.tiltDefectAbsoluteRowMass
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (weight certificate)
    (inverseWeight certificate)
    (Pseudo.constraintGram pseudoData)
    left
  ≤ halfGap floorData
selectedConstraintGramTiltBelowHalfGap
    {pseudoData = pseudoData} {floorData = floorData} certificate =
  Tilt.tiltDefectRowBelowBudget
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (weight certificate)
    (inverseWeight certificate)
    (Pseudo.constraintGram pseudoData)
    (distortion certificate)
    (rowMass certificate)
    (halfGap floorData)
    (distortionNonnegative certificate)
    (ratioBound certificate)
    (gramRowMassBound certificate)
    (halfGapBudget certificate)

record ConstraintGramDecayCertificate
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (floorData : ConstraintGramReducedFloor pseudoData)
    (root target : Multiplier) : Set₁ where
  field
    weight inverseWeight : Multiplier → ℚ
    inverseLaw : ∀ row →
      inverseWeight row * weight row ≡ 1ℚ
    rootInverseOne : inverseWeight root ≡ 1ℚ
    targetWeightNonnegative : 0ℚ ≤ weight target
    targetWeightAbsolute : ∣ weight target ∣ ≡ weight target
    tiltedGreenEntryBound :
      ∣ CT.diagonalConjugate weight inverseWeight
          (Pseudo.gramPseudoinverse pseudoData) root target ∣
      ≤ tiltedGreenMajorant floorData

open ConstraintGramDecayCertificate public

selectedConstraintGramCombesThomasDecay :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (floorData : ConstraintGramReducedFloor pseudoData)
    root target
    (certificate : ConstraintGramDecayCertificate
      pseudoData floorData root target) →
  ∣ Pseudo.gramPseudoinverse pseudoData root target ∣
  ≤ tiltedGreenMajorant floorData
      * weight certificate target
selectedConstraintGramCombesThomasDecay
    pseudoData floorData root target certificate =
  CT.combesThomasKernelDecayFromTiltedEntry
    (weight certificate)
    (inverseWeight certificate)
    (inverseLaw certificate)
    (Pseudo.gramPseudoinverse pseudoData)
    root target
    (tiltedGreenMajorant floorData)
    (rootInverseOne certificate)
    (targetWeightNonnegative certificate)
    (targetWeightAbsolute certificate)
    (tiltedGreenEntryBound certificate)

constraintGramFiniteRangeLevel : ProofLevel
constraintGramFiniteRangeLevel = machineChecked

constraintGramReducedFloorLevel : ProofLevel
constraintGramReducedFloorLevel = machineChecked

constraintGramCombesThomasReductionLevel : ProofLevel
constraintGramCombesThomasReductionLevel = machineChecked

selectedConstraintGramStencilProducerLevel : ProofLevel
selectedConstraintGramStencilProducerLevel = conditional

selectedConstraintGramReducedFloorProducerLevel : ProofLevel
selectedConstraintGramReducedFloorProducerLevel = conditional

selectedConstraintGramTiltProducerLevel : ProofLevel
selectedConstraintGramTiltProducerLevel = conditional
