module DASHI.Physics.YangMills.BalabanP33PlaquetteSubsetProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Construct the ACTUAL sixteen Boolean-four-cube localizations of the literal
-- plaquette-boundary projector.  A Subset4 selects any subset of the four
-- oriented boundary bonds of
--
--   U_mu(x) U_nu(x+mu) U_mu(x+nu)^-1 U_nu(x)^-1.
--
-- The empty subset is the zero projector and the full subset is definitionally
-- the existing four-bond boundary projector.  Consequently the raw singleton
-- extractor now has literal 16 partial evaluations with empty=0 and full=raw;
-- no arbitrary family of partial values is required for the defect lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical

infixr 5 _and_
infixr 4 _or_

_and_ : Bool → Bool → Bool
false and right = false
true and right = right

_or_ : Bool → Bool → Bool
false or right = right
true or right = true

slotMatch :
  Cube.BondSlot4 → Cube.Subset4 →
  Plaquette.Plaquette4 → Projector.Coordinate → Bool
slotMatch Cube.slot0 subset plaquette coordinate =
  Cube.contains Cube.slot0 subset
  and Boundary.bondCellEqual
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell0 plaquette)
slotMatch Cube.slot1 subset plaquette coordinate =
  Cube.contains Cube.slot1 subset
  and Boundary.bondCellEqual
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell1 plaquette)
slotMatch Cube.slot2 subset plaquette coordinate =
  Cube.contains Cube.slot2 subset
  and Boundary.bondCellEqual
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell2 plaquette)
slotMatch Cube.slot3 subset plaquette coordinate =
  Cube.contains Cube.slot3 subset
  and Boundary.bondCellEqual
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell3 plaquette)

subsetBoundaryMask :
  Cube.Subset4 → Plaquette.Plaquette4 → Projector.PhysicalCoordinateMask
subsetBoundaryMask subset plaquette coordinate =
  slotMatch Cube.slot0 subset plaquette coordinate
  or
  (slotMatch Cube.slot1 subset plaquette coordinate
  or
  (slotMatch Cube.slot2 subset plaquette coordinate
  or slotMatch Cube.slot3 subset plaquette coordinate))

emptySubsetMaskFalse : ∀ plaquette coordinate →
  subsetBoundaryMask Cube.empty plaquette coordinate ≡ false
emptySubsetMaskFalse plaquette coordinate = refl

fullSubsetMaskIsBoundary : ∀ plaquette coordinate →
  subsetBoundaryMask Cube.s0123 plaquette coordinate
  ≡ Boundary.plaquetteBoundaryMask plaquette coordinate
fullSubsetMaskIsBoundary plaquette coordinate = refl

subsetBoundaryProject :
  Cube.Subset4 → Plaquette.Plaquette4 →
  Projector.PhysicalVector → Projector.PhysicalVector
subsetBoundaryProject subset plaquette =
  Projector.physicalCoordinateProject (subsetBoundaryMask subset plaquette)

emptySubsetProjectZero : ∀ plaquette vector coordinate →
  subsetBoundaryProject Cube.empty plaquette vector coordinate ≡ 0ℚ
emptySubsetProjectZero plaquette vector coordinate =
  trans
    (cong
      (λ selected → Projector.maskSelect selected (vector coordinate))
      (emptySubsetMaskFalse plaquette coordinate))
    (ℚRing.solve-∀ (vector coordinate))

fullSubsetProjectIsBoundaryProject : ∀ plaquette vector coordinate →
  subsetBoundaryProject Cube.s0123 plaquette vector coordinate
  ≡ Boundary.plaquetteBoundaryProject plaquette vector coordinate
fullSubsetProjectIsBoundaryProject plaquette vector coordinate =
  cong
    (λ selected → Projector.maskSelect selected (vector coordinate))
    (fullSubsetMaskIsBoundary plaquette coordinate)

rawSubsetExtractor :
  Physical.PhysicalSU2BondField4 → Plaquette.Plaquette4 →
  Cube.Subset4 → Projector.PhysicalVector
rawSubsetExtractor field plaquette subset =
  subsetBoundaryProject subset plaquette
    (Physical.encodePhysicalSU2 field)

rawSubsetExtractorEmptyZero : ∀ field plaquette coordinate →
  rawSubsetExtractor field plaquette Cube.empty coordinate ≡ 0ℚ
rawSubsetExtractorEmptyZero field plaquette =
  emptySubsetProjectZero plaquette (Physical.encodePhysicalSU2 field)

rawSubsetExtractorFullExact : ∀ field plaquette coordinate →
  rawSubsetExtractor field plaquette Cube.s0123 coordinate
  ≡ Boundary.rawPlaquetteSingletonExtractor field plaquette coordinate
rawSubsetExtractorFullExact field plaquette =
  fullSubsetProjectIsBoundaryProject
    plaquette (Physical.encodePhysicalSU2 field)

subsetBoundaryProjectorConstructionLevel : ProofLevel
subsetBoundaryProjectorConstructionLevel = machineChecked

rawSixteenSubsetExtractorConstructionLevel : ProofLevel
rawSixteenSubsetExtractorConstructionLevel = machineChecked
