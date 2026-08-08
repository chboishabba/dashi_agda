module DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockTiltExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Michel Combes and Lawrence Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numérique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- DASHI CONTRIBUTION
--
-- Tilt the full local KKT block rather than an arbitrary dense reduced basis.
-- The state Hessian, constraint and adjoint-constraint perturbations are kept
-- as three named blocks. Given the exact finite KKT right inverse, conjugation
-- by any certified linear weight transports the right-inverse law to the
-- tilted block. The remaining analytic step is exactly the norm-smallness
-- estimate for these three perturbations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; 0ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenExact as Block

record KKTBlockWeight (Multiplier : Set) : Set₁ where
  field
    stateTilt stateUntilt : KKT.StateVector → KKT.StateVector
    multiplierTilt multiplierUntilt : (Multiplier → ℚ) → (Multiplier → ℚ)
    stateTiltUntilt : ∀ vector coordinate →
      stateTilt (stateUntilt vector) coordinate ≡ vector coordinate
    stateUntiltTilt : ∀ vector coordinate →
      stateUntilt (stateTilt vector) coordinate ≡ vector coordinate
    multiplierTiltUntilt : ∀ vector row →
      multiplierTilt (multiplierUntilt vector) row ≡ vector row
    multiplierUntiltTilt : ∀ vector row →
      multiplierUntilt (multiplierTilt vector) row ≡ vector row
    stateTiltAdd : ∀ left right coordinate →
      stateTilt (Rect.vectorAdd left right) coordinate
      ≡ stateTilt left coordinate + stateTilt right coordinate
open KKTBlockWeight public

tiltBlock : ∀ {Multiplier} → KKTBlockWeight Multiplier →
  Block.KKTBlockVector Multiplier → Block.KKTBlockVector Multiplier
tiltBlock weight vector = Block.block
  (stateTilt weight (Block.statePart vector))
  (multiplierTilt weight (Block.multiplierPart vector))

untiltBlock : ∀ {Multiplier} → KKTBlockWeight Multiplier →
  Block.KKTBlockVector Multiplier → Block.KKTBlockVector Multiplier
untiltBlock weight vector = Block.block
  (stateUntilt weight (Block.statePart vector))
  (multiplierUntilt weight (Block.multiplierPart vector))

tiltAfterUntiltExact : ∀ {Multiplier}
    (weight : KKTBlockWeight Multiplier) vector →
  Block.PointwiseKKTBlockEquality
    (tiltBlock weight (untiltBlock weight vector)) vector
tiltAfterUntiltExact weight vector = record
  { Block.PointwiseKKTBlockEquality.stateEqual =
      stateTiltUntilt weight (Block.statePart vector)
  ; Block.PointwiseKKTBlockEquality.multiplierEqual =
      multiplierTiltUntilt weight (Block.multiplierPart vector) }

untiltAfterTiltExact : ∀ {Multiplier}
    (weight : KKTBlockWeight Multiplier) vector →
  Block.PointwiseKKTBlockEquality
    (untiltBlock weight (tiltBlock weight vector)) vector
untiltAfterTiltExact weight vector = record
  { Block.PointwiseKKTBlockEquality.stateEqual =
      stateUntiltTilt weight (Block.statePart vector)
  ; Block.PointwiseKKTBlockEquality.multiplierEqual =
      multiplierUntiltTilt weight (Block.multiplierPart vector) }

tiltedKKTApply : ∀ {Multiplier} → Block.ConstrainedGreenData Multiplier →
  KKTBlockWeight Multiplier → Block.KKTBlockVector Multiplier →
  Block.KKTBlockVector Multiplier
tiltedKKTApply data weight source =
  tiltBlock weight (Block.applyKKTBlock data (untiltBlock weight source))

tiltedHessianDifference : ∀ {Multiplier} →
  Block.ConstrainedGreenData Multiplier → KKTBlockWeight Multiplier →
  KKT.StateVector → KKT.StateVector
tiltedHessianDifference data weight vector coordinate =
  stateTilt weight
    (Block.hessianApply data (stateUntilt weight vector)) coordinate
  - Block.hessianApply data vector coordinate

tiltedAdjointDifference : ∀ {Multiplier} →
  Block.ConstrainedGreenData Multiplier → KKTBlockWeight Multiplier →
  (Multiplier → ℚ) → KKT.StateVector
tiltedAdjointDifference data weight multiplier coordinate =
  stateTilt weight
    (KKT.constraintAdjointApply (Block.projectorData data)
      (multiplierUntilt weight multiplier)) coordinate
  - KKT.constraintAdjointApply (Block.projectorData data) multiplier coordinate

tiltedConstraintDifference : ∀ {Multiplier} →
  Block.ConstrainedGreenData Multiplier → KKTBlockWeight Multiplier →
  KKT.StateVector → Multiplier → ℚ
tiltedConstraintDifference data weight vector row =
  multiplierTilt weight
    (KKT.constraintApply (Block.projectorData data)
      (stateUntilt weight vector)) row
  - KKT.constraintApply (Block.projectorData data) vector row

tiltedKKTStateDifferenceSplits : ∀ {Multiplier}
    (data : Block.ConstrainedGreenData Multiplier)
    (weight : KKTBlockWeight Multiplier) vector coordinate →
  Block.statePart (tiltedKKTApply data weight vector) coordinate
    - Block.statePart (Block.applyKKTBlock data vector) coordinate
  ≡ tiltedHessianDifference data weight (Block.statePart vector) coordinate
    + tiltedAdjointDifference data weight (Block.multiplierPart vector) coordinate
tiltedKKTStateDifferenceSplits data weight vector coordinate = trans
  (cong (_- Block.statePart (Block.applyKKTBlock data vector) coordinate)
    (stateTiltAdd weight
      (Block.hessianApply data (stateUntilt weight (Block.statePart vector)))
      (KKT.constraintAdjointApply (Block.projectorData data)
        (multiplierUntilt weight (Block.multiplierPart vector))) coordinate))
  (ℚRing.solve-∀
    (stateTilt weight
      (Block.hessianApply data (stateUntilt weight (Block.statePart vector))) coordinate)
    (stateTilt weight
      (KKT.constraintAdjointApply (Block.projectorData data)
        (multiplierUntilt weight (Block.multiplierPart vector))) coordinate)
    (Block.hessianApply data (Block.statePart vector) coordinate)
    (KKT.constraintAdjointApply (Block.projectorData data)
      (Block.multiplierPart vector) coordinate))

tiltedKKTMultiplierDifferenceExact : ∀ {Multiplier}
    (data : Block.ConstrainedGreenData Multiplier)
    (weight : KKTBlockWeight Multiplier) vector row →
  Block.multiplierPart (tiltedKKTApply data weight vector) row
    - Block.multiplierPart (Block.applyKKTBlock data vector) row
  ≡ tiltedConstraintDifference data weight (Block.statePart vector) row
tiltedKKTMultiplierDifferenceExact data weight vector row = refl

tiltedKKTSolve : ∀ {Multiplier} → Block.ConstrainedGreenData Multiplier →
  KKTBlockWeight Multiplier → Block.KKTBlockVector Multiplier →
  Block.KKTBlockVector Multiplier
tiltedKKTSolve data weight source =
  tiltBlock weight (Block.solveKKTBlock data (untiltBlock weight source))

record ExtensionalKKTBlockWeight (Multiplier : Set) : Set₁ where
  field
    weight : KKTBlockWeight Multiplier
    stateTiltExtensional : ∀ {left right} →
      (∀ coordinate → left coordinate ≡ right coordinate) →
      ∀ coordinate → stateTilt weight left coordinate ≡ stateTilt weight right coordinate
    multiplierTiltExtensional : ∀ {left right} →
      (∀ row → left row ≡ right row) →
      ∀ row → multiplierTilt weight left row ≡ multiplierTilt weight right row
open ExtensionalKKTBlockWeight public

tiltBlockPointwiseCongExact : ∀ {Multiplier}
    (extensional : ExtensionalKKTBlockWeight Multiplier)
    {left right : Block.KKTBlockVector Multiplier} →
  Block.PointwiseKKTBlockEquality left right →
  Block.PointwiseKKTBlockEquality
    (tiltBlock (weight extensional) left)
    (tiltBlock (weight extensional) right)
tiltBlockPointwiseCongExact extensional equality = record
  { Block.PointwiseKKTBlockEquality.stateEqual =
      stateTiltExtensional extensional (Block.stateEqual equality)
  ; Block.PointwiseKKTBlockEquality.multiplierEqual =
      multiplierTiltExtensional extensional (Block.multiplierEqual equality) }

tiltedKKTRightInverseExact : ∀ {Multiplier}
    (data : Block.ConstrainedGreenData Multiplier)
    (extensional : ExtensionalKKTBlockWeight Multiplier) source →
  Block.PointwiseKKTBlockEquality
    (tiltedKKTApply data (weight extensional)
      (tiltedKKTSolve data (weight extensional) source)) source
tiltedKKTRightInverseExact data extensional source =
  let
    weightData = weight extensional
    baseSource = untiltBlock weightData source
    baseRight = Block.kktBlockRightInverseExact data baseSource
    tiltedBase = tiltBlockPointwiseCongExact extensional baseRight
    tiltUntil = tiltAfterUntiltExact weightData source
  in record
    { Block.PointwiseKKTBlockEquality.stateEqual = λ coordinate →
        trans (Block.stateEqual tiltedBase coordinate)
          (Block.stateEqual tiltUntil coordinate)
    ; Block.PointwiseKKTBlockEquality.multiplierEqual = λ row →
        trans (Block.multiplierEqual tiltedBase row)
          (Block.multiplierEqual tiltUntil row) }

fullKKTBlockTiltIdentityLevel : ProofLevel
fullKKTBlockTiltIdentityLevel = machineChecked

fullKKTBlockPerturbationSplitLevel : ProofLevel
fullKKTBlockPerturbationSplitLevel = machineChecked

tiltedKKTConjugatedRightInverseLevel : ProofLevel
tiltedKKTConjugatedRightInverseLevel = machineChecked

physicalKKTBlockTiltNormSmallnessLevel : ProofLevel
physicalKKTBlockTiltNormSmallnessLevel = conditional
