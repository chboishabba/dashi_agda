module DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the source-support seam at the correct carrier.  The differential of
-- one Wilson plaquette is first evaluated on the literal constrained
-- coordinate basis of its four boundary bonds.  Its coordinate covector is
-- then the canonical zero-extension of that LOCAL differential to the full
-- 3072-coordinate physical carrier.  Consequently the resulting source lies
-- in the image of the exact plaquette-boundary projector by construction, but
-- the coefficients themselves are not arbitrary: every retained coefficient
-- is the exact four-factor Wilson first variation on the corresponding
-- physical basis direction.
--
-- This is the finite-coordinate statement of
--
--   supp (D S_p) subset boundary(p).
--
-- It immediately instantiates the Round58 LiteralSourceDefectSubsetProducer;
-- hence the sixteen source partials and their Mobius atoms are generated from
-- this same literal Wilson differential rather than from a support receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFirstVariationExact as First
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33FiniteGaugeOrbitPathWitnessExact as Orbit
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlExact as Flat
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedSourceSubsetConstraintPartialExact as Source
open Source.PlaquetteSupportedSource using (support)
open Source.LiteralSourceDefectSubsetProducer using (sourceSupported)

plaquetteWilsonFirstVariation :
  Orbit.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 →
  Flat.Plaquette4 → ℚ
plaquetteWilsonFirstVariation background direction plaquette =
  First.wilsonFirstVariationNumerator
    (Plaquette.plaquetteFactorJets background direction plaquette)

plaquetteWilsonFirstVariationIsFourAtoms :
  ∀ background direction plaquette →
  plaquetteWilsonFirstVariation background direction plaquette
  ≡ First.wilsonFirstVariationAtomSum
      (Plaquette.plaquetteFactorJets background direction plaquette)
plaquetteWilsonFirstVariationIsFourAtoms background direction plaquette =
  First.wilsonFirstVariationIsAtomSum
    (Plaquette.plaquetteFactorJets background direction plaquette)

localBasisDirection :
  Flat.Plaquette4 →
  Physical.PhysicalSU2Coordinate4 →
  Physical.PhysicalSU2BondField4
localBasisDirection plaquette coordinate =
  Physical.decodePhysicalSU2
    (Projector.physicalConstrainedCoordinateBasis
      (Boundary.plaquetteBoundaryMask plaquette) coordinate)

localWilsonFirstVariationCoordinates :
  Orbit.RationalSU2Background4 →
  Flat.Plaquette4 →
  Projector.PhysicalVector
localWilsonFirstVariationCoordinates background plaquette coordinate =
  plaquetteWilsonFirstVariation background
    (localBasisDirection plaquette coordinate) plaquette

selectedWilsonFirstVariationCovector :
  Orbit.RationalSU2Background4 →
  Flat.Plaquette4 → KKT.StateVector
selectedWilsonFirstVariationCovector background plaquette =
  Boundary.plaquetteBoundaryProject plaquette
    (localWilsonFirstVariationCoordinates background plaquette)

selectedWilsonFirstVariationPlaquetteSupport :
  ∀ background plaquette →
  Source.PlaquetteSupportedSource plaquette
    (selectedWilsonFirstVariationCovector background plaquette)
selectedWilsonFirstVariationPlaquetteSupport background plaquette =
  record
    { support =
        Projector.physicalCoordinateProjectLiesInImage
          (Boundary.plaquetteBoundaryMask plaquette)
          (localWilsonFirstVariationCoordinates background plaquette)
    }

selectedWilsonFirstVariationBoundaryFixed :
  ∀ background plaquette coordinate →
  Boundary.plaquetteBoundaryProject plaquette
    (selectedWilsonFirstVariationCovector background plaquette) coordinate
  ≡ selectedWilsonFirstVariationCovector background plaquette coordinate
selectedWilsonFirstVariationBoundaryFixed background plaquette =
  Source.boundaryProjectFixesSupportedSource
    (selectedWilsonFirstVariationPlaquetteSupport background plaquette)

literalSelectedWilsonSourceDefectProducer :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    background bondField plaquette →
  Source.LiteralSourceDefectSubsetProducer
    pseudoData
    (selectedWilsonFirstVariationCovector background plaquette)
    bondField plaquette
literalSelectedWilsonSourceDefectProducer
    pseudoData background bondField plaquette =
  record
    { sourceSupported =
        selectedWilsonFirstVariationPlaquetteSupport background plaquette
    }

selectedWilsonFirstVariationFourAtomLevel : ProofLevel
selectedWilsonFirstVariationFourAtomLevel = machineChecked

selectedWilsonFirstVariationPlaquetteSupportLevel : ProofLevel
selectedWilsonFirstVariationPlaquetteSupportLevel = machineChecked

literalSelectedWilsonSourceDefectProducerLevel : ProofLevel
literalSelectedWilsonSourceDefectProducerLevel = machineChecked
