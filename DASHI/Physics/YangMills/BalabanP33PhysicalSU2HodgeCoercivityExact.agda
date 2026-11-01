module DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Lift the repository's scalar side-four bond Poincare theorem to the actual
-- three-component su(2) perturbation used by the 3072-coordinate Hessian.
-- The former cancellation lane accidentally paired a total Wilson scalar with
-- one scalar bond field.  Here the physical norm and reference energy are the
-- literal sums over the x, y and z Lie coordinates, and mean zero is required
-- componentwise.
--
-- The theorem proves
--
--   (1/16) ||h||^2_SU2 <= H_diff^SU2(h)
--
-- and preserves the same floor after adding a nonnegative CMP109 penalty.
-- No dimension witness or unspecified component norm is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as ScalarHodge
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL

PhysicalField : Set
PhysicalField = Physical.PhysicalSU2BondField4

physicalReferenceDifferenceEnergy : PhysicalField → ℚ
physicalReferenceDifferenceEnergy fieldValue =
  ScalarHodge.bondReferenceDifferenceEnergy
    (fieldValue Physical.coordinateX)
  + ScalarHodge.bondReferenceDifferenceEnergy
    (fieldValue Physical.coordinateY)
  + ScalarHodge.bondReferenceDifferenceEnergy
    (fieldValue Physical.coordinateZ)

PhysicalBondComponentMeanZero : PhysicalField → Set
PhysicalBondComponentMeanZero fieldValue =
  ScalarHodge.BondComponentMeanZero (fieldValue Physical.coordinateX)
  × (ScalarHodge.BondComponentMeanZero (fieldValue Physical.coordinateY)
  × ScalarHodge.BondComponentMeanZero (fieldValue Physical.coordinateZ))

physicalReferenceDifferencePoincare :
  ∀ fieldValue → PhysicalBondComponentMeanZero fieldValue →
  LDL.oneSixteenth * Physical.physicalSU2BondNormSq fieldValue
  ≤ physicalReferenceDifferenceEnergy fieldValue
physicalReferenceDifferencePoincare fieldValue (meanX , (meanY , meanZ)) =
  let
    boundX = ScalarHodge.path4BondDifferencePoincare
      (fieldValue Physical.coordinateX) meanX
    boundY = ScalarHodge.path4BondDifferencePoincare
      (fieldValue Physical.coordinateY) meanY
    boundZ = ScalarHodge.path4BondDifferencePoincare
      (fieldValue Physical.coordinateZ) meanZ

    summed :
      LDL.oneSixteenth
        * ScalarHodge.bondNormSq (fieldValue Physical.coordinateX)
      + LDL.oneSixteenth
        * ScalarHodge.bondNormSq (fieldValue Physical.coordinateY)
      + LDL.oneSixteenth
        * ScalarHodge.bondNormSq (fieldValue Physical.coordinateZ)
      ≤ physicalReferenceDifferenceEnergy fieldValue
    summed = ℚP.+-mono-≤
      (ℚP.+-mono-≤ boundX boundY) boundZ
  in
  subst
    (λ lower → lower ≤ physicalReferenceDifferenceEnergy fieldValue)
    (ℚRing.solve-∀
      LDL.oneSixteenth
      (ScalarHodge.bondNormSq (fieldValue Physical.coordinateX))
      (ScalarHodge.bondNormSq (fieldValue Physical.coordinateY))
      (ScalarHodge.bondNormSq (fieldValue Physical.coordinateZ)))
    summed

physicalReferenceHodgeEnergy : PhysicalField → ℚ → ℚ
physicalReferenceHodgeEnergy fieldValue constraintPenalty =
  physicalReferenceDifferenceEnergy fieldValue + constraintPenalty

physicalReferenceBelowWithConstraint :
  ∀ fieldValue constraintPenalty →
  0ℚ ≤ constraintPenalty →
  physicalReferenceDifferenceEnergy fieldValue
  ≤ physicalReferenceHodgeEnergy fieldValue constraintPenalty
physicalReferenceBelowWithConstraint fieldValue constraintPenalty nonnegative =
  subst
    (λ lower →
      lower ≤ physicalReferenceDifferenceEnergy fieldValue + constraintPenalty)
    (sym (ℚP.+-identityʳ
      (physicalReferenceDifferenceEnergy fieldValue)))
    (ℚP.+-monoʳ-≤
      (physicalReferenceDifferenceEnergy fieldValue) nonnegative)

physicalReferenceHodgeCoercivity :
  ∀ fieldValue constraintPenalty →
  PhysicalBondComponentMeanZero fieldValue →
  0ℚ ≤ constraintPenalty →
  LDL.oneSixteenth * Physical.physicalSU2BondNormSq fieldValue
  ≤ physicalReferenceHodgeEnergy fieldValue constraintPenalty
physicalReferenceHodgeCoercivity
    fieldValue constraintPenalty meanZero constraintNonnegative =
  ℚP.≤-trans
    (physicalReferenceDifferencePoincare fieldValue meanZero)
    (physicalReferenceBelowWithConstraint
      fieldValue constraintPenalty constraintNonnegative)

physicalSU2HodgeReferenceLevel : ProofLevel
physicalSU2HodgeReferenceLevel = machineChecked

physicalSU2PoincareLiftLevel : ProofLevel
physicalSU2PoincareLiftLevel = machineChecked

physicalSU2ConstraintReferenceLevel : ProofLevel
physicalSU2ConstraintReferenceLevel = machineChecked
