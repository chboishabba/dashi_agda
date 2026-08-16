module DASHI.Moonshine.OggRepresentationReductionEverything where

------------------------------------------------------------------------
-- Aggregate surface for the corrected SSP research direction:
--
-- continuous irrep -> finite restriction -> branching/fixed-space spectrum
--                    ||
--                    vv
-- independent modular/Hecke column -> explicit intertwiner obligation.
--
-- The old Ogg 7+7+1/nonary surfaces remain downstream comparison data.
-- The phase-quotient/jCoarse/jFine/Fricke weld is imported here because it
-- supplies an independently constructed finite reduction chain rather than an
-- SSP selector assumption.
------------------------------------------------------------------------

import DASHI.Foundations.FiniteRepresentationRestrictionCore
import DASHI.Foundations.SU2SO3IrrepDimensionExact
import DASHI.Foundations.D4SO3NineIrrepRestrictionExact
import DASHI.Foundations.D4SO3RestrictionJ0To35Exact
import DASHI.Foundations.D4SO3RestrictionCharacterJ0To35Exact
import DASHI.Foundations.TetrahedralSO3RestrictionJ0To35Exact
import DASHI.Foundations.TetrahedralSO3RestrictionCharacterJ0To35Exact
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact
import DASHI.Foundations.OctahedralSO3RestrictionCharacterJ0To35Exact
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact
import DASHI.Foundations.IcosahedralSO3RestrictionCharacterJ0To35Exact
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact
import DASHI.Foundations.PolyhedralFixedSpaceDerivedNonaryExact
import DASHI.Foundations.PolyhedralRestrictionCriticalCharacterExact
import DASHI.Foundations.PolyhedralRegularRepresentationShiftExact
import DASHI.Foundations.TernaryPhaseShapeIncidenceExact
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact
import DASHI.Biology.D4NineCellOrbitCompressionExact
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact
import DASHI.Biology.TernaryPhaseQuotientJCoarseBridgeExact
import DASHI.Biology.JFinePhaseQuotientFieldExact
import DASHI.Biology.D4IrrepFiniteFrickeEquivariantExact
import DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact
import DASHI.Moonshine.D4IrrepModularFrickeDescentExact
import DASHI.Moonshine.Monster3BC3RepresentationRingEvaluationExact
import DASHI.Moonshine.OggPolyhedralReductionControlExact
import DASHI.Moonshine.OggTetrahedralReductionControlExact
import DASHI.Moonshine.SSPRepresentationHeckeIntertwinerBoundaryExact
import DASHI.Moonshine.TernarySevenOggSSPComparisonExact
import DASHI.Moonshine.OggPhaseFrickeSynthesisRegression
import DASHI.Physics.Closure.PhysicalSSPHeckeModelClosureReceipt
import DASHI.Physics.Closure.SSPZ3EigenspaceClassificationReceipt
import DASHI.Physics.Moonshine.SupersingularPrimeLaneBridge
import Ontology.Hecke.CorrespondenceRepresentation
