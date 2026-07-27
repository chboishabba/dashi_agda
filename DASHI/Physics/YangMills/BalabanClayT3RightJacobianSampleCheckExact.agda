module DASHI.Physics.YangMills.BalabanClayT3RightJacobianSampleCheckExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 1ℚ; _-_; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Joan Solà, Jérémie Deray and Dinesh Atchuthan,
-- "A micro Lie theory for state estimation in robotics", arXiv:1812.01537.
-- No journal DOI is assigned in the cited arXiv version.
--
-- Timothy D. Barfoot, "State Estimation for Robotics", Cambridge University
-- Press (2017). DOI: 10.1017/9781316671528
--
-- Relationship: independent right-Jacobian convention and numerical
-- cross-check.  This file does not replace the symbolic singular-value proof.
------------------------------------------------------------------------

sampleTheta sampleHalfTheta : ℚ
sampleTheta = + 1 / 2
sampleHalfTheta = + 1 / 4

sampleSincLower sampleInverseUpper : ℚ
sampleSincLower = 1ℚ - (+ 1 / 6) * (sampleHalfTheta * sampleHalfTheta)
sampleInverseUpper = + 96 / 95

sampleSincLowerExact : sampleSincLower ≡ + 95 / 96
sampleSincLowerExact = ℚRing.solve

sampleInverseUpperExact :
  sampleSincLower * sampleInverseUpper ≡ 1ℚ
sampleInverseUpperExact = ℚRing.solve

sampleSincLowerPositive : + 0 / 1 ≤ sampleSincLower
sampleSincLowerPositive = ℚP.≤ᵇ⇒≤ tt

record RightJacobianSampleAuthority (Scalar : Set) : Set₁ where
  field
    rational : ℚ → Scalar
    sine divide multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    planeSingularValue inverseOperatorNorm : Scalar

    planeSingularValueFormula :
      planeSingularValue
      ≡ divide
          (multiply (rational (+ 2 / 1))
            (sine (rational sampleHalfTheta) (rational (+ 1 / 1))))
          (rational sampleTheta)

    planeSingularValueEqualsHalfAngleSinc : Set

    sincLowerAtSample :
      LessEqual (rational sampleSincLower) planeSingularValue

    reciprocalOrderBound :
      LessEqual (rational sampleSincLower) planeSingularValue →
      LessEqual inverseOperatorNorm (rational sampleInverseUpper)

open RightJacobianSampleAuthority public

rightJacobianInverseSampleBound :
  ∀ {Scalar} (dataSet : RightJacobianSampleAuthority Scalar) →
  LessEqual dataSet
    (inverseOperatorNorm dataSet)
    (rational dataSet sampleInverseUpper)
rightJacobianInverseSampleBound dataSet =
  reciprocalOrderBound dataSet (sincLowerAtSample dataSet)

rightJacobianSampleRationalLevel : ProofLevel
rightJacobianSampleRationalLevel = machineChecked

rightJacobianSampleReductionLevel : ProofLevel
rightJacobianSampleReductionLevel = machineChecked

literalSampleSineEvaluationInputsLevel : ProofLevel
literalSampleSineEvaluationInputsLevel = conditional
