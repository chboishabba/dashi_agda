module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonNamedAtomSumExact where

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
-- Prove that the literal physical Wilson defect is exactly the finite sum of
-- the sixteen named placement defects on every plaquette.  The chain is
--
--   named placements
--     = generated second-product atoms
--     = Wilson second variation,
--
-- first plaquettewise and then over all 1,536 physical plaquettes.
--
-- Consequently a signed bound proved for each named placement can be summed
-- directly into `physicalWilsonDefect`; no anonymous atom total or independently
-- supplied aggregation theorem remains between W-local and W-global.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonPlacementTelescopeExact as Named
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope

sumMap : ∀ {A : Set} (values : List A) (term : A → ℚ) → ℚ
sumMap values term = Q.sumRational (map term values)

sumMapDifference :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  sumMap values (λ value → left value - right value)
  ≡ sumMap values left - sumMap values right
sumMapDifference [] left right = ℚRing.solve []
sumMapDifference (value ∷ values) left right =
  trans
    (cong (left value - right value +_)
      (sumMapDifference values left right))
    (ℚRing.solve-∀
      (left value) (right value)
      (sumMap values left) (sumMap values right))

physicalPlacementWilsonAtomSum :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → ℚ
physicalPlacementWilsonAtomSum background fieldValue plaquette =
  sumMap Placement.plaquetteSecondVariationPlacements4
    (λ placement →
      Telescope.wilsonScalar
        (Named.physicalNamedPlacementAtom
          background fieldValue plaquette placement))

physicalPlacementWilsonAtomSumIsPlaquetteVariation :
  ∀ background fieldValue plaquette →
  physicalPlacementWilsonAtomSum background fieldValue plaquette
  ≡ Physical.plaquetteWilsonSecondVariation background fieldValue plaquette
physicalPlacementWilsonAtomSumIsPlaquetteVariation
    background fieldValue plaquette =
  let
    factors = Physical.plaquetteFactorJets background fieldValue plaquette

    atomListExact :
      Named.physicalPlacementAtoms background fieldValue plaquette
      ≡ Q.secondVariationTerms factors
    atomListExact =
      Named.physicalPlacementAtomsMatchGeneratedProductRule
        background fieldValue plaquette
  in
  trans
    (cong
      (λ atoms → Q.sumRational (map Telescope.wilsonScalar atoms))
      atomListExact)
    (sym (Q.wilsonSecondVariationIsAtomSum factors))

physicalPlacementWilsonDefectSum :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → ℚ
physicalPlacementWilsonDefectSum background fieldValue plaquette =
  sumMap Placement.plaquetteSecondVariationPlacements4
    (Named.physicalPlacementWilsonScalarDefect
      background fieldValue plaquette)

physicalPlacementWilsonDefectSumExact :
  ∀ background fieldValue plaquette →
  physicalPlacementWilsonDefectSum background fieldValue plaquette
  ≡ Physical.plaquetteWilsonSecondVariation background fieldValue plaquette
    - Physical.plaquetteWilsonSecondVariation
        Physical.identityBackground fieldValue plaquette
physicalPlacementWilsonDefectSumExact background fieldValue plaquette =
  trans
    (sumMapDifference
      Placement.plaquetteSecondVariationPlacements4
      (λ placement →
        Telescope.wilsonScalar
          (Named.physicalNamedPlacementAtom
            background fieldValue plaquette placement))
      (λ placement →
        Telescope.wilsonScalar
          (Named.physicalNamedPlacementAtom
            Physical.identityBackground fieldValue plaquette placement)))
    (cong₂ _-_
      (physicalPlacementWilsonAtomSumIsPlaquetteVariation
        background fieldValue plaquette)
      (physicalPlacementWilsonAtomSumIsPlaquetteVariation
        Physical.identityBackground fieldValue plaquette))

physicalNamedWilsonDefectSum :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
physicalNamedWilsonDefectSum background fieldValue =
  Sums.sumRational Physical.plaquettes4
    (physicalPlacementWilsonDefectSum background fieldValue)

physicalNamedWilsonDefectSumIsPhysicalDefect :
  ∀ background fieldValue →
  physicalNamedWilsonDefectSum background fieldValue
  ≡ Physical.physicalWilsonDefect background fieldValue
physicalNamedWilsonDefectSumIsPhysicalDefect background fieldValue =
  trans
    (Sums.sumRationalCong
      Physical.plaquettes4
      (physicalPlacementWilsonDefectSum background fieldValue)
      (λ plaquette →
        Physical.plaquetteWilsonSecondVariation background fieldValue plaquette
        - Physical.plaquetteWilsonSecondVariation
            Physical.identityBackground fieldValue plaquette)
      (physicalPlacementWilsonDefectSumExact background fieldValue))
    (trans
      (Sums.sumRationalSubtract
        Physical.plaquettes4
        (Physical.plaquetteWilsonSecondVariation background fieldValue)
        (Physical.plaquetteWilsonSecondVariation
          Physical.identityBackground fieldValue))
      refl)

physicalWilsonNamedAtomPlaquetteSumLevel : ProofLevel
physicalWilsonNamedAtomPlaquetteSumLevel = machineChecked

physicalWilsonNamedAtomGlobalSumLevel : ProofLevel
physicalWilsonNamedAtomGlobalSumLevel = machineChecked
