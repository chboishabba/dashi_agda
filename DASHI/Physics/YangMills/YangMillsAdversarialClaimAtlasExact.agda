module DASHI.Physics.YangMills.YangMillsAdversarialClaimAtlasExact where

------------------------------------------------------------------------
-- SOURCE ATLAS
--
-- Jenny Lorraine Nielsen and Lu Semita,
-- "The Proof of the Yang Mills Mass Gap" / earlier title "Topological
-- Enforcement of the Yang Mills Mass Gap".  PhilArchive record NIETEO-12.
-- No DOI was located for the cited manuscript record.
--
-- Daniel Toupin,
-- "The Yang-Mills Mass Gap: Proof via Celestial Holography and Haar Measure".
-- Zenodo DOI: 10.5281/zenodo.19939019.
--
-- Philipp Rietz,
-- "Vacuum Information Density as the Fundamental Geometric Scalar: UIDT
-- v3.6: A Proposed Theoretical Framework for the Yang-Mills Mass Gap and
-- Gamma-Scaling Unification".
-- DOI: 10.2139/ssrn.5807202.  Related deposit DOI:
-- 10.5281/zenodo.17835200.
--
-- D. C. Jacobsen,
-- "A Constructive Proof of Existence and Mass Gap for Pure SU(3) Yang-Mills
-- in Four-Dimensional Space-Time".
-- DOI: 10.48550/arXiv.2506.00284.
--
-- Yuta Agawa,
-- "[Theoretical Hypothesis] A Rigorous Proof of the Mass Gap in SU(N)
-- Yang-Mills Theory".
-- DOI: 10.5281/zenodo.14975444.
--
-- Yuta Agawa,
-- "Quantum Corrections and Finite Gribov Uniqueness in a Non-local Gauge
-- Theory: An Essential Addendum to the Proof of the Yang-Mills Mass Gap".
-- DOI: 10.33774/coe-2025-3jmcf-v2.  The source is marked retracted by its
-- author on Cambridge Open Engage.
--
-- Kaoru Aguilera Katayama,
-- "Existence and Mass Gap of Pure Yang-Mills Theory in Four Dimensions: A
-- Complete Proof via Renormalization, Sobolev Inequalities, and Logarithmic
-- Sobolev Inequalities".
-- DOI: 10.13140/RG.2.2.32667.43041.
--
-- Lucian Randolph,
-- "The Yang-Mills Mass Gap: Existence and Positivity from Instanton Cascade
-- Architecture and the Discrete Spectrum of the Transfer Matrix".
-- DOI: 10.5281/zenodo.19456988.
--
-- Henry Watt et al.,
-- "The Yang-Mills Mass Gap: From Proof Attempts to Dissolution by
-- Holographic Finiteness".
-- DOI: 10.5281/zenodo.19699784.
--
-- These records are formalised as claims to audit, never as theorem receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)

import DASHI.Physics.YangMills.YangMillsPaperClaimAuditCarrierExact as Audit

data ClaimSource : Set where
  nielsenSemitaTopological : ClaimSource
  toupinCelestialHaar : ClaimSource
  rietzUIDTScalar : ClaimSource
  jacobsenFiveDimensionalOrbifold : ClaimSource
  agawaNonlocalHolonomy : ClaimSource
  agawaRetractedAddendum : ClaimSource
  katayamaContinuumLSI : ClaimSource
  randolphCascadeTransfer : ClaimSource
  wattAllBetaSketch : ClaimSource

data FirstOpenDependency : Set where
  topologicalTheoryToPureYM : FirstOpenDependency
  beltramiToHamiltonianIntertwiner : FirstOpenDependency
  celestialToFourDimensionalLocalQFT : FirstOpenDependency
  conformalWeightToEnergySpectrum : FirstOpenDependency
  scalarExtensionDecouplesExactly : FirstOpenDependency
  exactRegulatorIndependentFRG : FirstOpenDependency
  fiveDimensionalZeroModeEquivalence : FirstOpenDependency
  jointPolymerUniformInSpacingAndVolume : FirstOpenDependency
  nonlocalTheoryEquivalentToLocalYM : FirstOpenDependency
  globalGaugeSliceCompatibleWithGribovObstruction : FirstOpenDependency
  continuumMeasureActuallyConstructed : FirstOpenDependency
  infiniteDimensionalLSIUniformInCutoffs : FirstOpenDependency
  returnMapConstructedFromYangMillsFlow : FirstOpenDependency
  cascadeSpectrumIntertwinesTransferHamiltonian : FirstOpenDependency
  nonAbelianPolchinskiFlowIdentity : FirstOpenDependency
  multiscaleLSIInputNoncircular : FirstOpenDependency

sourceVenue : ClaimSource → Audit.VenueStatus
sourceVenue nielsenSemitaTopological = Audit.selfArchivedManuscript
sourceVenue toupinCelestialHaar = Audit.repositoryDeposit
sourceVenue rietzUIDTScalar = Audit.workingPaper
sourceVenue jacobsenFiveDimensionalOrbifold = Audit.academicPreprint
sourceVenue agawaNonlocalHolonomy = Audit.repositoryDeposit
sourceVenue agawaRetractedAddendum = Audit.retractedSource
sourceVenue katayamaContinuumLSI = Audit.repositoryDeposit
sourceVenue randolphCascadeTransfer = Audit.repositoryDeposit
sourceVenue wattAllBetaSketch = Audit.repositoryDeposit

sourceTheory : ClaimSource → Audit.TheorySignature
sourceTheory nielsenSemitaTopological = Audit.topologicalHopfFibrationTheory
sourceTheory toupinCelestialHaar = Audit.celestialConformalConstruction
sourceTheory rietzUIDTScalar = Audit.yangMillsWithAdditionalScalar
sourceTheory jacobsenFiveDimensionalOrbifold = Audit.fiveDimensionalOrbifoldGaugeTheory
sourceTheory agawaNonlocalHolonomy = Audit.nonlocalHolonomyGaugeTheory
sourceTheory agawaRetractedAddendum = Audit.nonlocalHolonomyGaugeTheory
sourceTheory katayamaContinuumLSI = Audit.pureFourDimensionalYangMills
sourceTheory randolphCascadeTransfer = Audit.effectivePolyakovLoopDynamics
sourceTheory wattAllBetaSketch = Audit.latticeYangMillsFixedSpacing

sourceOperator : ClaimSource → Audit.OperatorSignature
sourceOperator nielsenSemitaTopological = Audit.beltramiOperator
sourceOperator toupinCelestialHaar = Audit.conformalWeightOperator
sourceOperator rietzUIDTScalar = Audit.functionalRGLinearization
sourceOperator jacobsenFiveDimensionalOrbifold = Audit.sturmLiouvilleRegulatorOperator
sourceOperator agawaNonlocalHolonomy = Audit.latticeTransferOperator
sourceOperator agawaRetractedAddendum = Audit.latticeTransferOperator
sourceOperator katayamaContinuumLSI = Audit.stochasticLangevinGenerator
sourceOperator randolphCascadeTransfer = Audit.periodDoublingReturnMap
sourceOperator wattAllBetaSketch = Audit.stochasticLangevinGenerator

sourceEvidence : ClaimSource → Audit.EvidenceKind
sourceEvidence nielsenSemitaTopological = Audit.conditionalDerivation
sourceEvidence toupinCelestialHaar = Audit.conditionalDerivation
sourceEvidence rietzUIDTScalar = Audit.numericalResidual
sourceEvidence jacobsenFiveDimensionalOrbifold = Audit.conditionalDerivation
sourceEvidence agawaNonlocalHolonomy = Audit.proofSketch
sourceEvidence agawaRetractedAddendum = Audit.proofSketch
sourceEvidence katayamaContinuumLSI = Audit.conditionalDerivation
sourceEvidence randolphCascadeTransfer = Audit.conditionalDerivation
sourceEvidence wattAllBetaSketch = Audit.proofSketch

sourceOutcome : ClaimSource → Audit.AuditOutcome
sourceOutcome nielsenSemitaTopological = Audit.firstDependencyOpen
sourceOutcome toupinCelestialHaar = Audit.firstDependencyOpen
sourceOutcome rietzUIDTScalar = Audit.differentTheoryStatement
sourceOutcome jacobsenFiveDimensionalOrbifold = Audit.firstDependencyOpen
sourceOutcome agawaNonlocalHolonomy = Audit.firstDependencyOpen
sourceOutcome agawaRetractedAddendum = Audit.withdrawnClaim
sourceOutcome katayamaContinuumLSI = Audit.firstDependencyOpen
sourceOutcome randolphCascadeTransfer = Audit.firstDependencyOpen
sourceOutcome wattAllBetaSketch = Audit.conditionalTheorem

firstOpen : ClaimSource → FirstOpenDependency
firstOpen nielsenSemitaTopological = topologicalTheoryToPureYM
firstOpen toupinCelestialHaar = celestialToFourDimensionalLocalQFT
firstOpen rietzUIDTScalar = scalarExtensionDecouplesExactly
firstOpen jacobsenFiveDimensionalOrbifold = fiveDimensionalZeroModeEquivalence
firstOpen agawaNonlocalHolonomy = nonlocalTheoryEquivalentToLocalYM
firstOpen agawaRetractedAddendum = globalGaugeSliceCompatibleWithGribovObstruction
firstOpen katayamaContinuumLSI = continuumMeasureActuallyConstructed
firstOpen randolphCascadeTransfer = returnMapConstructedFromYangMillsFlow
firstOpen wattAllBetaSketch = nonAbelianPolchinskiFlowIdentity

claimSources : List ClaimSource
claimSources =
  nielsenSemitaTopological
  ∷ toupinCelestialHaar
  ∷ rietzUIDTScalar
  ∷ jacobsenFiveDimensionalOrbifold
  ∷ agawaNonlocalHolonomy
  ∷ agawaRetractedAddendum
  ∷ katayamaContinuumLSI
  ∷ randolphCascadeTransfer
  ∷ wattAllBetaSketch
  ∷ []

claimSourceCountExact : length claimSources ≡ 9
claimSourceCountExact = refl

noAuditedClaimIsKernelProof :
  ∀ source → sourceEvidence source ≡ Audit.formalKernelProof → ⊥
noAuditedClaimIsKernelProof nielsenSemitaTopological ()
noAuditedClaimIsKernelProof toupinCelestialHaar ()
noAuditedClaimIsKernelProof rietzUIDTScalar ()
noAuditedClaimIsKernelProof jacobsenFiveDimensionalOrbifold ()
noAuditedClaimIsKernelProof agawaNonlocalHolonomy ()
noAuditedClaimIsKernelProof agawaRetractedAddendum ()
noAuditedClaimIsKernelProof katayamaContinuumLSI ()
noAuditedClaimIsKernelProof randolphCascadeTransfer ()
noAuditedClaimIsKernelProof wattAllBetaSketch ()

noAuditedClaimIsCheckedClayTheorem :
  ∀ source → sourceOutcome source ≡ Audit.checkedTheorem → ⊥
noAuditedClaimIsCheckedClayTheorem nielsenSemitaTopological ()
noAuditedClaimIsCheckedClayTheorem toupinCelestialHaar ()
noAuditedClaimIsCheckedClayTheorem rietzUIDTScalar ()
noAuditedClaimIsCheckedClayTheorem jacobsenFiveDimensionalOrbifold ()
noAuditedClaimIsCheckedClayTheorem agawaNonlocalHolonomy ()
noAuditedClaimIsCheckedClayTheorem agawaRetractedAddendum ()
noAuditedClaimIsCheckedClayTheorem katayamaContinuumLSI ()
noAuditedClaimIsCheckedClayTheorem randolphCascadeTransfer ()
noAuditedClaimIsCheckedClayTheorem wattAllBetaSketch ()

agawaAddendumRetractionRecorded :
  sourceVenue agawaRetractedAddendum ≡ Audit.retractedSource
agawaAddendumRetractionRecorded = refl

uidtDifferentTheoryRecorded :
  sourceOutcome rietzUIDTScalar ≡ Audit.differentTheoryStatement
uidtDifferentTheoryRecorded = refl

wattSketchRemainsConditional :
  sourceOutcome wattAllBetaSketch ≡ Audit.conditionalTheorem
wattSketchRemainsConditional = refl
