module DASHI.Physics.YangMills.BalabanP33ThreeComponentCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Lift the scalar side-four P33 estimate to the literal three-coordinate
-- su(2)-valued bond carrier.  The lift is a finite sum over the concrete
-- x/y/z coordinate list and therefore introduces neither a hidden direct-sum
-- theorem nor a second coercivity assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanPath4DirectionalEnergyContractionExact using
  (sumRationalMonotone)
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates

threeComponentEnergy :
  (Coordinates.LieCoordinate3 → ℚ) → ℚ
threeComponentEnergy componentEnergy =
  sumRational Coordinates.lieCoordinates3 componentEnergy

scaledThreeComponentNormExact : ∀ fld →
  P33.p33PhysicalFloor * Coordinates.physicalSU2BondNormSq fld
  ≡ sumRational Coordinates.lieCoordinates3
      (λ coordinate →
        P33.p33PhysicalFloor * Hodge.bondNormSq (fld coordinate))
scaledThreeComponentNormExact fld =
  sym
    (sumRationalScale
      P33.p33PhysicalFloor
      Coordinates.lieCoordinates3
      (λ coordinate → Hodge.bondNormSq (fld coordinate)))

threeComponentP33Floor :
  ∀ fld componentEnergy →
  (∀ coordinate →
    P33.p33PhysicalFloor * Hodge.bondNormSq (fld coordinate)
    ≤ componentEnergy coordinate) →
  P33.p33PhysicalFloor * Coordinates.physicalSU2BondNormSq fld
  ≤ threeComponentEnergy componentEnergy
threeComponentP33Floor fld componentEnergy componentFloor =
  subst
    (λ lower → lower ≤ threeComponentEnergy componentEnergy)
    (sym (scaledThreeComponentNormExact fld))
    (sumRationalMonotone
      Coordinates.lieCoordinates3
      (λ coordinate →
        P33.p33PhysicalFloor * Hodge.bondNormSq (fld coordinate))
      componentEnergy
      componentFloor)

physicalSU2ThreeComponentFloorLevel : ProofLevel
physicalSU2ThreeComponentFloorLevel = machineChecked
