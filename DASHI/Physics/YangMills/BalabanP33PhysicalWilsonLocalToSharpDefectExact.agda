module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLocalToSharpDefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The preceding module sums the actual plaquette-local inequality to
--
--   -(13/24) rho ||h||^2 <= H_W(A;h)-H_W(1;h).
--
-- This module performs the two remaining literal identifications:
--
--   (13/24) rho = 13/196608,
--   H_W(1;h) = H_curl^flat(h).
--
-- It therefore produces exactly the sharp Wilson input required by the
-- physical boundary-assisted terminal coercivity theorem.  The final theorem
-- uses the repository's same-background/same-h perturbation adapter: its
-- literal Wilson fold is definitionally built from `backgroundOf h` and
-- `physicalFieldOf h`.  No independent data-set equality witness is accepted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; -_; _-_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as Flat
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as GaugeBudget
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralPhysicalPerturbationAdapterExact as SameH

sharpWilsonCoefficientFromRho :
  (+ 13 / 24) * GaugeBudget.rho
  ≡ Sharp.sharpSixteenAtomBudget
sharpWilsonCoefficientFromRho = ℚRing.solve []

physicalWilsonDefectIsBackgroundMinusFlat : ∀ background field →
  Physical.physicalWilsonDefect background field
  ≡ Physical.physicalWilsonSecondVariation background field
      - Flat.flatWilsonEnergy field
physicalWilsonDefectIsBackgroundMinusFlat background field =
  trans refl
    (cong
      (Physical.physicalWilsonSecondVariation background field -_)
      (Physical.identityPhysicalWilsonIsFlatCurl field))

physicalWilsonLocalImpliesSharpDefect :
  ∀ background field →
  Global.PhysicalWilsonSignedLocal background field →
  - (Sharp.sharpSixteenAtomBudget
      * Coordinates.physicalSU2BondNormSq field)
  ≤ Physical.physicalWilsonSecondVariation background field
      - Flat.flatWilsonEnergy field
physicalWilsonLocalImpliesSharpDefect background field local =
  let
    summed = Global.physicalWilsonSignedGlobalThirteenTwentyFourths
      background field local

    sharpCoefficientLower :
      - (Sharp.sharpSixteenAtomBudget
          * Coordinates.physicalSU2BondNormSq field)
      ≤ Physical.physicalWilsonDefect background field
    sharpCoefficientLower =
      subst
        (λ coefficient →
          - (coefficient * Coordinates.physicalSU2BondNormSq field)
          ≤ Physical.physicalWilsonDefect background field)
        sharpWilsonCoefficientFromRho
        summed
  in
  subst
    (λ upper →
      - (Sharp.sharpSixteenAtomBudget
          * Coordinates.physicalSU2BondNormSq field)
      ≤ upper)
    (physicalWilsonDefectIsBackgroundMinusFlat background field)
    sharpCoefficientLower

samePhysicalPerturbationWLocalImpliesSharpDefect :
  ∀ {Perturbation GaugeIndex ConstraintIndex}
    (model : SameH.LiteralPhysicalPerturbationModel
      Perturbation GaugeIndex ConstraintIndex)
    h →
  Global.PhysicalWilsonSignedLocal
    (SameH.backgroundOf model h) (SameH.physicalFieldOf model h) →
  - (Sharp.sharpSixteenAtomBudget
      * Coordinates.physicalSU2BondNormSq (SameH.physicalFieldOf model h))
  ≤ Jets.wilsonSecondVariation (SameH.literalSecondVariationOf model h)
      - Flat.flatWilsonEnergy (SameH.physicalFieldOf model h)
samePhysicalPerturbationWLocalImpliesSharpDefect model h local =
  subst
    (λ selectedWilson →
      - (Sharp.sharpSixteenAtomBudget
          * Coordinates.physicalSU2BondNormSq (SameH.physicalFieldOf model h))
      ≤ selectedWilson - Flat.flatWilsonEnergy (SameH.physicalFieldOf model h))
    (sym (SameH.literalWilsonIsPhysicalWilson model h))
    (physicalWilsonLocalImpliesSharpDefect
      (SameH.backgroundOf model h) (SameH.physicalFieldOf model h) local)

physicalWLocalToSharpWilsonLevel : ProofLevel
physicalWLocalToSharpWilsonLevel = machineChecked

samePhysicalPerturbationWilsonTransportLevel : ProofLevel
samePhysicalPerturbationWilsonTransportLevel = machineChecked
