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
-- SSP selector assumption.  Direct Aristotle arithmetic/Hecke/q-series
-- theorems and the complete candidate tau fingerprint are independent control
-- columns, not selector premises.  The prime Fricke coupling imports below
-- make the first exact representation/modular defect bridge: SO(3) characters
-- reconstruct the elliptic-point part of g(X0(p)); class-number Fricke fixed
-- points close the quotient defect, orbit saturation, and finite
-- supersingular/Frobenius two-orbit spectrum.  p=2 stays a separate SU(2)
-- spinor boundary rather than being forced through the odd SO(3) lane.
-- Cyclic C2/C3 elliptic stabilisers are embedded as proper subgroups of the
-- existing ternary S3 permutation carrier rather than conflated with S3.
------------------------------------------------------------------------

import DASHI.Analysis.FiniteRealQSeriesReflectionExact
import DASHI.Arithmetic.AristotleArithmeticEverything
import DASHI.Foundations.FiniteRepresentationRestrictionCore
import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact
import DASHI.Foundations.FiniteInvolutionCorrespondenceDescentExact
import DASHI.Foundations.PolyhedralFiniteRestrictionInstancesExact
import DASHI.Foundations.CandidateIndexedFiniteRestrictionFamilyExact
import DASHI.Foundations.SU2SO3IrrepDimensionExact
import DASHI.Foundations.CubicSO3OrbitalBranchingExact
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
import DASHI.Foundations.PolyhedralInvariantFixedSpaceSignatureExact
import DASHI.Foundations.PolyhedralRestrictionCriticalCharacterExact
import DASHI.Foundations.PolyhedralRegularRepresentationShiftExact
import DASHI.Foundations.BinaryPolyhedralMcKayDimensionExact
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact
import DASHI.Foundations.TernaryPhaseShapeIncidenceExact
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact
import DASHI.Biology.D4NineCellOrbitCompressionExact
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact
import DASHI.Biology.TernaryPhaseQuotientJCoarseBridgeExact
import DASHI.Biology.JFinePhaseQuotientFieldExact
import DASHI.Biology.D4IrrepFiniteFrickeEquivariantExact
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact
import DASHI.Moonshine.Hecke23AntiparallelExact
import DASHI.Moonshine.AristotleHeckeRecurrenceCoreExact
import DASHI.Moonshine.AristotleHecke23Smooth3ParityExact
import DASHI.Moonshine.AristotleHeckeWordsSourceParityExact
import DASHI.Moonshine.AristotleHeckeGeneralPrimePowerDecompositionExact
import DASHI.Moonshine.AristotleHeckeGeneralZeroUpdateExact
import DASHI.Moonshine.AristotleDeltaWordT2T3FiniteParityExact
import DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact
import DASHI.Moonshine.CandidateLevelExternalOggPredicateExact
import DASHI.Moonshine.RamanujanTauHecke23Exact
import DASHI.Moonshine.RamanujanTauCandidateFingerprintJ0To35Exact
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact
import DASHI.Moonshine.D4IrrepModularFrickeDescentExact
import DASHI.Moonshine.Monster3BC3RepresentationRingEvaluationExact
import DASHI.Moonshine.OggPolyhedralReductionControlExact
import DASHI.Moonshine.OggTetrahedralReductionControlExact
import DASHI.Moonshine.OggPrimeControlMatrixExact
import DASHI.Moonshine.PrimeFrickeGenusControlExact
import DASHI.Moonshine.PrimeFrickeOrbitSaturationExact
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact
import DASHI.Moonshine.PrimeRepresentationFrickeCouplingExact
import DASHI.Moonshine.PrimeRepresentationFrickeOrbitSaturationExact
import DASHI.Moonshine.PrimeRepresentationSupersingularOrbitCouplingExact
import DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact
import DASHI.Moonshine.SSPRepresentationHeckeIntertwinerBoundaryExact
import DASHI.Moonshine.TernarySevenOggSSPComparisonExact
import DASHI.Moonshine.OggPhaseFrickeSynthesisRegression
import DASHI.Moonshine.AristotleCrossPollinationRegression
import DASHI.Moonshine.OggRepresentationFrickeCouplingRegression
import DASHI.Moonshine.OggPrimeModularControlRegression
import DASHI.Physics.Closure.PhysicalSSPHeckeModelClosureReceipt
import DASHI.Physics.Closure.SSPZ3EigenspaceClassificationReceipt
import DASHI.Physics.Moonshine.SupersingularPrimeLaneBridge
import Ontology.Hecke.CorrespondenceRepresentation
