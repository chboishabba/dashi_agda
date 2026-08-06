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
physicalPlacementWilsonAtomSum background field plaquette =
  sumMap Placement.plaquetteSecondVariationPlacements4
    (λ placement →
      Telescope.wilsonScalar
        (Named.physicalNamedPlacementAtom
          background field plaquette placement))

physicalPlacementWilsonAtomSumIsPlaquetteVariation :
  ∀ background field plaquette →
  physicalPlacementWilsonAtomSum background field plaquette
  ≡ Physical.plaquetteWilsonSecondVariation background field plaquette
physicalPlacementWilsonAtomSumIsPlaquetteVariation
    background field plaquette =
  let
    factors = Physical.plaquetteFactorJets background field plaquette

    atomListExact :
      Named.physicalPlacementAtoms background field plaquette
      ≡ Q.secondVariationTerms factors
    atomListExact =
      Named.physicalPlacementAtomsMatchGeneratedProductRule
        background field plaquette
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
physicalPlacementWilsonDefectSum background field plaquette =
  sumMap Placement.plaquetteSecondVariationPlacements4
    (Named.physicalPlacementWilsonScalarDefect
      background field plaquette)

physicalPlacementWilsonDefectSumExact :
  ∀ background field plaquette →
  physicalPlacementWilsonDefectSum background field plaquette
  ≡ Physical.plaquetteWilsonSecondVariation background field plaquette
    - Physical.plaquetteWilsonSecondVariation
        Physical.identityBackground field plaquette
physicalPlacementWilsonDefectSumExact background field plaquette =
  trans
    (sumMapDifference
      Placement.plaquetteSecondVariationPlacements4
      (λ placement →
        Telescope.wilsonScalar
          (Named.physicalNamedPlacementAtom
            background field plaquette placement))
      (λ placement →
        Telescope.wilsonScalar
          (Named.physicalNamedPlacementAtom
            Physical.identityBackground field plaquette placement)))
    (cong₂ _-_
      (physicalPlacementWilsonAtomSumIsPlaquetteVariation
        background field plaquette)
      (physicalPlacementWilsonAtomSumIsPlaquetteVariation
        Physical.identityBackground field plaquette))

physicalNamedWilsonDefectSum :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
physicalNamedWilsonDefectSum background field =
  Sums.sumRational Physical.plaquettes4
    (physicalPlacementWilsonDefectSum background field)

physicalNamedWilsonDefectSumIsPhysicalDefect :
  ∀ background field →
  physicalNamedWilsonDefectSum background field
  ≡ Physical.physicalWilsonDefect background field
physicalNamedWilsonDefectSumIsPhysicalDefect background field =
  trans
    (Sums.sumRationalCong
      Physical.plaquettes4
      (physicalPlacementWilsonDefectSum background field)
      (λ plaquette →
        Physical.plaquetteWilsonSecondVariation background field plaquette
        - Physical.plaquetteWilsonSecondVariation
            Physical.identityBackground field plaquette)
      (physicalPlacementWilsonDefectSumExact background field))
    (trans
      (Sums.sumRationalSubtract
        Physical.plaquettes4
        (Physical.plaquetteWilsonSecondVariation background field)
        (Physical.plaquetteWilsonSecondVariation
          Physical.identityBackground field))
      refl)

physicalWilsonNamedAtomPlaquetteSumLevel : ProofLevel
physicalWilsonNamedAtomPlaquetteSumLevel = machineChecked

physicalWilsonNamedAtomGlobalSumLevel : ProofLevel
physicalWilsonNamedAtomGlobalSumLevel = machineChecked
