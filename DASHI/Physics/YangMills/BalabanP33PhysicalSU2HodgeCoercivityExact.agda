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
physicalReferenceDifferenceEnergy field =
  ScalarHodge.bondReferenceDifferenceEnergy
    (field Physical.coordinateX)
  + ScalarHodge.bondReferenceDifferenceEnergy
    (field Physical.coordinateY)
  + ScalarHodge.bondReferenceDifferenceEnergy
    (field Physical.coordinateZ)

PhysicalBondComponentMeanZero : PhysicalField → Set
PhysicalBondComponentMeanZero field =
  ScalarHodge.BondComponentMeanZero (field Physical.coordinateX)
  × (ScalarHodge.BondComponentMeanZero (field Physical.coordinateY)
  × ScalarHodge.BondComponentMeanZero (field Physical.coordinateZ))

physicalReferenceDifferencePoincare :
  ∀ field → PhysicalBondComponentMeanZero field →
  LDL.oneSixteenth * Physical.physicalSU2BondNormSq field
  ≤ physicalReferenceDifferenceEnergy field
physicalReferenceDifferencePoincare field (meanX , (meanY , meanZ)) =
  let
    boundX = ScalarHodge.path4BondDifferencePoincare
      (field Physical.coordinateX) meanX
    boundY = ScalarHodge.path4BondDifferencePoincare
      (field Physical.coordinateY) meanY
    boundZ = ScalarHodge.path4BondDifferencePoincare
      (field Physical.coordinateZ) meanZ

    summed :
      LDL.oneSixteenth
        * ScalarHodge.bondNormSq (field Physical.coordinateX)
      + LDL.oneSixteenth
        * ScalarHodge.bondNormSq (field Physical.coordinateY)
      + LDL.oneSixteenth
        * ScalarHodge.bondNormSq (field Physical.coordinateZ)
      ≤ physicalReferenceDifferenceEnergy field
    summed = ℚP.+-mono-≤
      (ℚP.+-mono-≤ boundX boundY) boundZ
  in
  subst
    (λ lower → lower ≤ physicalReferenceDifferenceEnergy field)
    (ℚRing.solve-∀
      LDL.oneSixteenth
      (ScalarHodge.bondNormSq (field Physical.coordinateX))
      (ScalarHodge.bondNormSq (field Physical.coordinateY))
      (ScalarHodge.bondNormSq (field Physical.coordinateZ)))
    summed

physicalReferenceHodgeEnergy : PhysicalField → ℚ → ℚ
physicalReferenceHodgeEnergy field constraintPenalty =
  physicalReferenceDifferenceEnergy field + constraintPenalty

physicalReferenceBelowWithConstraint :
  ∀ field constraintPenalty →
  0ℚ ≤ constraintPenalty →
  physicalReferenceDifferenceEnergy field
  ≤ physicalReferenceHodgeEnergy field constraintPenalty
physicalReferenceBelowWithConstraint field constraintPenalty nonnegative =
  subst
    (λ lower →
      lower ≤ physicalReferenceDifferenceEnergy field + constraintPenalty)
    (sym (ℚP.+-identityʳ
      (physicalReferenceDifferenceEnergy field)))
    (ℚP.+-monoʳ-≤
      (physicalReferenceDifferenceEnergy field) nonnegative)

physicalReferenceHodgeCoercivity :
  ∀ field constraintPenalty →
  PhysicalBondComponentMeanZero field →
  0ℚ ≤ constraintPenalty →
  LDL.oneSixteenth * Physical.physicalSU2BondNormSq field
  ≤ physicalReferenceHodgeEnergy field constraintPenalty
physicalReferenceHodgeCoercivity
    field constraintPenalty meanZero constraintNonnegative =
  ℚP.≤-trans
    (physicalReferenceDifferencePoincare field meanZero)
    (physicalReferenceBelowWithConstraint
      field constraintPenalty constraintNonnegative)

physicalSU2HodgeReferenceLevel : ProofLevel
physicalSU2HodgeReferenceLevel = machineChecked

physicalSU2PoincareLiftLevel : ProofLevel
physicalSU2PoincareLiftLevel = machineChecked

physicalSU2ConstraintReferenceLevel : ProofLevel
physicalSU2ConstraintReferenceLevel = machineChecked
