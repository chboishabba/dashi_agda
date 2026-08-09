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
-- smaller multiplier Gram operator K=L L*.  The module exposes:
--
-- * an exact finite-range certificate for K;
-- * the literal tilted kernel and its three scalar inputs;
-- * a half-gap row-defect theorem from distortion times row mass;
-- * off-diagonal decay of K^{-1} (or K+) from a tilted-entry majorant.
--
-- The selected-background stencil, reduced floor and numerical tilt are
-- explicit producer fields.  No decay claim is promoted until those physical
-- fields are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; ∣_∣)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasTiltBudgetExact as Tilt

record ConstraintGramFiniteRange
    {Multiplier : Set}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier) : Set₁ where
  field
    distance : Multiplier → Multiplier → ℚ
    interactionRange : ℚ
    outsideRangeZero : ∀ left right →
      interactionRange < distance left right →
      KKT.constraintGram projectorData left right ≡ 0ℚ

open ConstraintGramFiniteRange public

selectedConstraintGramFiniteRange :
  ∀ {Multiplier}
    {projectorData : KKT.FiniteKKTProjectorData Multiplier} →
  ConstraintGramFiniteRange projectorData →
  ∀ left right →
  interactionRange _ < distance _ left right →
  KKT.constraintGram projectorData left right ≡ 0ℚ
selectedConstraintGramFiniteRange finiteRange =
  outsideRangeZero finiteRange

selectedConstraintGramTilt :
  ∀ {Multiplier} →
  (weight inverseWeight : Multiplier → ℚ) →
  KKT.FiniteKKTProjectorData Multiplier →
  CT.Matrix Multiplier
selectedConstraintGramTilt weight inverseWeight projectorData =
  CT.diagonalConjugate weight inverseWeight
    (KKT.constraintGram projectorData)

selectedConstraintGramTiltDefect :
  ∀ {Multiplier} →
  (weight inverseWeight : Multiplier → ℚ) →
  KKT.FiniteKKTProjectorData Multiplier →
  CT.Matrix Multiplier
selectedConstraintGramTiltDefect weight inverseWeight projectorData =
  CT.diagonalTiltDefect weight inverseWeight
    (KKT.constraintGram projectorData)

record ConstraintGramTiltCertificate
    {Multiplier : Set}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier) : Set₁ where
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
        (Matrix.coordinates (KKT.multiplierCarrier projectorData))
        (KKT.constraintGram projectorData) left
      ≤ rowMass

    halfGapBudget :
      distortion * rowMass ≤ Tilt.p33HalfGap

open ConstraintGramTiltCertificate public

selectedConstraintGramTiltBelowHalfGap :
  ∀ {Multiplier}
    {projectorData : KKT.FiniteKKTProjectorData Multiplier} →
  (certificate : ConstraintGramTiltCertificate projectorData) →
  ∀ left →
  Tilt.tiltDefectAbsoluteRowMass
    (Matrix.coordinates (KKT.multiplierCarrier projectorData))
    (weight certificate)
    (inverseWeight certificate)
    (KKT.constraintGram projectorData)
    left
  ≤ Tilt.p33HalfGap
selectedConstraintGramTiltBelowHalfGap
    {projectorData = projectorData} certificate =
  Tilt.p33TiltDefectBelowHalfGap
    (Matrix.coordinates (KKT.multiplierCarrier projectorData))
    (weight certificate)
    (inverseWeight certificate)
    (KKT.constraintGram projectorData)
    (distortion certificate)
    (rowMass certificate)
    (distortionNonnegative certificate)
    (ratioBound certificate)
    (gramRowMassBound certificate)
    (halfGapBudget certificate)

record ConstraintGramDecayCertificate
    {Multiplier : Set}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
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
          (KKT.multiplierGreen projectorData) root target ∣
      ≤ Tilt.p33TiltedResolventMajorant

open ConstraintGramDecayCertificate public

selectedConstraintGramCombesThomasDecay :
  ∀ {Multiplier}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    root target →
  ConstraintGramDecayCertificate projectorData root target →
  ∣ KKT.multiplierGreen projectorData root target ∣
  ≤ Tilt.p33TiltedResolventMajorant
      * ConstraintGramDecayCertificate.weight _ target
selectedConstraintGramCombesThomasDecay
    projectorData root target certificate =
  CT.combesThomasKernelDecayFromTiltedEntry
    (ConstraintGramDecayCertificate.weight certificate)
    (ConstraintGramDecayCertificate.inverseWeight certificate)
    (ConstraintGramDecayCertificate.inverseLaw certificate)
    (KKT.multiplierGreen projectorData)
    root target
    Tilt.p33TiltedResolventMajorant
    (ConstraintGramDecayCertificate.rootInverseOne certificate)
    (ConstraintGramDecayCertificate.targetWeightNonnegative certificate)
    (ConstraintGramDecayCertificate.targetWeightAbsolute certificate)
    (ConstraintGramDecayCertificate.tiltedGreenEntryBound certificate)

constraintGramFiniteRangeLevel : ProofLevel
constraintGramFiniteRangeLevel = machineChecked

constraintGramCombesThomasReductionLevel : ProofLevel
constraintGramCombesThomasReductionLevel = machineChecked

selectedConstraintGramStencilProducerLevel : ProofLevel
selectedConstraintGramStencilProducerLevel = conditional

selectedConstraintGramReducedFloorProducerLevel : ProofLevel
selectedConstraintGramReducedFloorProducerLevel = conditional

selectedConstraintGramTiltProducerLevel : ProofLevel
selectedConstraintGramTiltProducerLevel = conditional
