module DASHI.Moonshine.OggRepresentationReductionEverything where

------------------------------------------------------------------------
-- Aggregate surface for the corrected SSP research direction:
--
-- continuous irrep -> finite restriction -> branching/fixed-space spectrum
--                    ||
--                    vv
-- independent modular/Hecke column -> quotient-induced intertwiner obligation.
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
--
-- The matched-dihedral extension is a candidate-indexed restriction
-- H_j = D_(2j+1).  It gives the literal five-irrep decomposition
-- 9 = 1+2+2+2+2 at j=4, while proving multiplicity-freeness itself is too weak
-- to select Ogg.  Its sector count j+1 replaces the raw p+1 term in the modular
-- genus formula, so the non-Fricke part of the prime-level genus is now read
-- from reduced-representation observables plus the exact C2/C3 characters.
--
-- The Hecke frontier is now sharpened by exact quotient descent on the actual
-- PrimeCorrespondenceHeckeOn API.  FactorVec -> SupportMask supplies a complete
-- nontrivial model in which the existing support-mask correspondence is proved
-- to be the canonical induced quotient correspondence.  A count-only quotient
-- is then explicitly falsified: equal support cardinality can hide a
-- Hecke-relevant difference.  The still-open SSP theorem is therefore the
-- domain-specific SO(3)/reduction -> arithmetic Hecke quotient identification,
-- not generic commuting-square algebra.
--
-- A strengthened representation falsifier proves even the C2/C3/C4/C5
-- fixed-space signature collides between dimension 13 (Ogg control) and
-- dimension 15 (non-Ogg), so operator/branching information is required beyond
-- four cyclic dimensions.
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
import DASHI.Foundations.MatchedDihedralSO3RestrictionExact
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
import DASHI.Moonshine.AristotleDeltaWordT2T3FiniteParityExact
import DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact
import DASHI.Moonshine.CandidateLevelExternalOggPredicateExact
import DASHI.Moonshine.RamanujanTauHecke23Exact
import DASHI.Moonshine.RamanujanTauCandidateFingerprintJ0To35Exact
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact
import DASHI.Moonshine.D4IrrepModularFrickeDescentExact
import DASHI.Moonshine.Monster3BC3RepresentationRingEvaluationExact
import DASHI.Moonshine.SO3CyclicFixedSpaceScanExact
import DASHI.Moonshine.SO3CyclicBranchingControlExact
import DASHI.Moonshine.SO3CyclicFixedSpaceFormulaExact
import DASHI.Moonshine.SO3C5FiveIrrepNineExact
import DASHI.Moonshine.OggFixedSpaceSelectorNoGoExact
import DASHI.Moonshine.OggCyclicFixedSpaceFourProbeNoGoExact
import DASHI.Moonshine.OggPolyhedralReductionControlExact
import DASHI.Moonshine.OggTetrahedralReductionControlExact
import DASHI.Moonshine.OggPrimeControlMatrixExact
import DASHI.Moonshine.PrimeFrickeGenusControlExact
import DASHI.Moonshine.PrimeFrickeOrbitSaturationExact
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact
import DASHI.Moonshine.PrimeRepresentationFrickeCouplingExact
import DASHI.Moonshine.MatchedDihedralFrickeGenusBridgeExact
import DASHI.Moonshine.PrimeRepresentationFrickeOrbitSaturationExact
import DASHI.Moonshine.PrimeRepresentationSupersingularOrbitCouplingExact
import DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact
import DASHI.Moonshine.FactorVecSupportMaskHeckeQuotientExact
import DASHI.Moonshine.SupportMaskCountHeckeCompressionNoGoExact
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
import Ontology.Hecke.LevelCorrespondenceRepresentation
import Ontology.Hecke.QuotientRepresentation
import Ontology.Hecke.FactorVecCorrespondence
import Ontology.Hecke.FactorVecInstances
