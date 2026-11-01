module DASHI.Physics.YangMills.BalabanSelectedRawExtractorSubsetDefectPartialExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- Push the literal sixteen plaquette subset projectors through the ACTUAL KKT
-- constraint matrix.  This constructs the raw-extractor defect partial values
--
--       delta_S = L (P_S w)
--
-- for every S subset {0,1,2,3}.  Linearity of the concrete rectangular matrix
-- gives delta_empty=0, while P_full=P_boundary gives exactly the existing
-- raw constraint defect.  Hence the defect half of the Round-54 sixteen-point
-- producer is no longer conditional.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PlaquetteSubsetProjectorExact as Subset
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect

rawSubsetConstraintDefect :
  ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  Physical.PhysicalSU2BondField4 → Plaquette.Plaquette4 →
  Cube.Subset4 → Multiplier → ℚ
rawSubsetConstraintDefect pseudoData field plaquette subset =
  Pseudo.constraintApply pseudoData
    (Subset.rawSubsetExtractor field plaquette subset)

rawSubsetConstraintDefectEmptyZero :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    field plaquette row →
  rawSubsetConstraintDefect pseudoData field plaquette Cube.empty row ≡ 0ℚ
rawSubsetConstraintDefectEmptyZero pseudoData field plaquette row =
  trans
    (Rect.applyRectangularVectorCong
      KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Subset.rawSubsetExtractorEmptyZero field plaquette)
      row)
    (Rect.applyRectangularZero
      KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      row)

rawSubsetConstraintDefectFullExact :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    field plaquette row →
  rawSubsetConstraintDefect pseudoData field plaquette Cube.s0123 row
  ≡ Pseudo.constraintApply pseudoData
      (Boundary.rawPlaquetteSingletonExtractor field plaquette) row
rawSubsetConstraintDefectFullExact pseudoData field plaquette row =
  Rect.applyRectangularVectorCong
    KKT.physicalStateCarrier
    (Pseudo.constraintMatrix pseudoData)
    (Subset.rawSubsetExtractorFullExact field plaquette)
    row

rawSubsetConstraintDefectConstructionLevel : ProofLevel
rawSubsetConstraintDefectConstructionLevel = machineChecked

rawSubsetConstraintDefectEndpointLevel : ProofLevel
rawSubsetConstraintDefectEndpointLevel = machineChecked
