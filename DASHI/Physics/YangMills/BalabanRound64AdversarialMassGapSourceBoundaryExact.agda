module DASHI.Physics.YangMills.BalabanRound64AdversarialMassGapSourceBoundaryExact where

------------------------------------------------------------------------
-- ROUND64 ADVERSARIAL SOURCE BOUNDARY
--
-- These sources were supplied as lemma mines while constructing the literal
-- ten-master backwards proof.  This module keeps the useful mathematical
-- scopes and blocks the exact promotions that would shortcut the continuum
-- construction incorrectly.
--
-- SOURCES
--
-- Oliver Odusanya,
-- "Lattice Mass Gap for Four-Dimensional SU(2) Yang-Mills Theory: Certified
-- Spectral Gap via Transfer Matrix Analysis", 7 April 2026.
-- No DOI is recorded in the supplied manuscript.
-- Useful scope: finite periodic Wilson lattices / transfer-matrix gap route.
-- The manuscript itself defers thermodynamic and continuum limits.
--
-- Puskar Mondal,
-- "A Geometric Approach to the Yang-Mills Mass Gap",
-- arXiv:2301.06996v7 (2023).  No DOI is recorded in the supplied manuscript.
-- Useful scope: Bakry-Emery/configuration-space curvature as an alternative
-- spectral producer shape.  The article assumes existence of the quantized
-- Yang-Mills theory and describes the 3+1 dimensional scale calculation as
-- heuristic / requiring further rigorous renormalization.
--
-- Lautaro Fesembeck,
-- "Proof of the Yang-Mills Mass Gap via Energy Minimization", April 2025.
-- No DOI is recorded in the supplied manuscript.
-- Useful scope: classical gauge-fixed energy/coercivity questions.  A lower
-- bound for the classical energy or the linearized classical elliptic operator
-- is not by itself a continuum quantum Hamiltonian mass gap.
--
-- Thiago M. Nobrega,
-- "A Comprehensive Framework for Solving the Yang-Mills Existence and Mass
-- Gap Problem", 29 July 2024.  No DOI is recorded in the supplied manuscript.
-- Useful scope: checklist of functional-analytic ingredients.  The supplied
-- text states key path-integral/OS/spectral steps at theorem-outline level and
-- is not imported as proof authority for those constructions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data MassGapScope : Set where
  classicalEnergyCoercivity : MassGapScope
  linearizedClassicalOperatorGap : MassGapScope
  finiteVolumeLatticeTransferGap : MassGapScope
  assumedQuantumOrbitGeometryGap : MassGapScope
  continuumQuantumHamiltonianGap : MassGapScope
  literalClayConstruction : MassGapScope

classicalEnergyIsNotQuantumHamiltonianGap :
  classicalEnergyCoercivity ≡ continuumQuantumHamiltonianGap → ⊥
classicalEnergyIsNotQuantumHamiltonianGap ()

linearizedClassicalGapIsNotQuantumHamiltonianGap :
  linearizedClassicalOperatorGap ≡ continuumQuantumHamiltonianGap → ⊥
linearizedClassicalGapIsNotQuantumHamiltonianGap ()

finiteLatticeGapIsNotContinuumGap :
  finiteVolumeLatticeTransferGap ≡ continuumQuantumHamiltonianGap → ⊥
finiteLatticeGapIsNotContinuumGap ()

assumedQuantumGeometryIsNotExistenceConstruction :
  assumedQuantumOrbitGeometryGap ≡ literalClayConstruction → ⊥
assumedQuantumGeometryIsNotExistenceConstruction ()

continuumGapAloneIsNotLiteralClayConstruction :
  continuumQuantumHamiltonianGap ≡ literalClayConstruction → ⊥
continuumGapAloneIsNotLiteralClayConstruction ()

data SuppliedSource : Set where
  odusanya2026 : SuppliedSource
  mondal2023 : SuppliedSource
  fesembeck2025 : SuppliedSource
  nobrega2024 : SuppliedSource

data SourceUse : Set where
  finiteLatticeAnchorOnly : SourceUse
  alternativeConditionalSpectralMechanism : SourceUse
  classicalCoercivityLemmaMine : SourceUse
  requirementsChecklistOnly : SourceUse

sourceUse : SuppliedSource → SourceUse
sourceUse odusanya2026 = finiteLatticeAnchorOnly
sourceUse mondal2023 = alternativeConditionalSpectralMechanism
sourceUse fesembeck2025 = classicalCoercivityLemmaMine
sourceUse nobrega2024 = requirementsChecklistOnly

sourceUseOdusanyaExact : sourceUse odusanya2026 ≡ finiteLatticeAnchorOnly
sourceUseOdusanyaExact = refl

sourceUseMondalExact :
  sourceUse mondal2023 ≡ alternativeConditionalSpectralMechanism
sourceUseMondalExact = refl

sourceUseFesembeckExact :
  sourceUse fesembeck2025 ≡ classicalCoercivityLemmaMine
sourceUseFesembeckExact = refl

sourceUseNobregaExact : sourceUse nobrega2024 ≡ requirementsChecklistOnly
sourceUseNobregaExact = refl

odusanyaContinuumPromotionLevel : ProofLevel
odusanyaContinuumPromotionLevel = conditional

mondalExistencePromotionLevel : ProofLevel
mondalExistencePromotionLevel = conditional

fesembeckQuantumPromotionLevel : ProofLevel
fesembeckQuantumPromotionLevel = conditional

nobregaConstructiveQFTPromotionLevel : ProofLevel
nobregaConstructiveQFTPromotionLevel = conditional
