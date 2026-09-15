module DASHI.Chemistry.Everything where

import DASHI.Chemistry.TransitionKernel
import DASHI.Chemistry.MechanismDiscriminationExact
import DASHI.Chemistry.MechanismDiscriminationCoreBridgeExact
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact
import DASHI.Chemistry.TGO93PhEurPesticideMembershipExact
import DASHI.Chemistry.RegulatoryAnalyteCoverageBidiExact
import DASHI.Chemistry.AssayDetectionEnvelopeExact
import DASHI.Chemistry.SpeciesMethodDetectionCrossPollinationExact
import DASHI.Chemistry.DefensiveRegulatoryAssayStressAuditExact
import DASHI.Chemistry.RegulatoryAssayExperimentProofSearchExact
import DASHI.Chemistry.RegulatoryAnalytePanelRefinementExact
import DASHI.Chemistry.ExistingContentBridge
import DASHI.Chemistry.Photography.InstantFilmSurface
import DASHI.Chemistry.ChemistryTransitionKernelTests
import DASHI.Chemistry.ChlorAlkaliSaltIndustryExact
import DASHI.Chemistry.ChlorAlkaliHalfReactionExact
import DASHI.Chemistry.ChlorAlkaliCanonicalHalfReactionsExact
import DASHI.Chemistry.DrinkingWaterChlorineSpeciationExact
import DASHI.Chemistry.DrinkingWaterChloramineDBPBoundaryExact
import DASHI.Chemistry.DrinkingWaterDistributionResidualCorrosionBidiExact
import DASHI.Chemistry.DrinkingWaterChloramineNitrificationBiofilmBidiExact
import DASHI.Chemistry.DrinkingWaterCorrosionMetalReleaseExact
import DASHI.Chemistry.DrinkingWaterTapMetalObservationBidiExact

-- Refinery/feedstock composition lane: salt/chloride/process constraints remain
-- distinct from crude grade, effective throughput and downstream economics.
import DASHI.Chemistry.RefineryFeedstockSaltConstraintBidiExact

-- Integrated industrial-chemistry lane: salt-derived chlor-alkali co-products
-- and hydrocarbon cracker/refinery products meet only through explicit
-- downstream reaction, inventory, quality and provenance receipts.
import DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact

-- Carbon suitability lane: periodic/valence structure, rich carbon chemistry,
-- stellar production abundance and abiogenesis remain separately receipted.
import DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact
import DASHI.Chemistry.CarbonBackboneReachableChemistryConeExact

-- Ocean biogeochemistry lane: salinity, temperature, CO2/carbonate chemistry,
-- oxygen and nutrient state remain separate coordinates for ecological use.
import DASHI.Chemistry.OceanCarbonateSaltTemperatureStressBidiExact

-- Deep-time carbon-cycle balance: explicit atmosphere/ocean/biosphere/
-- sediment/fossil reservoirs, transfer conservation, residence-time receipts,
-- path residuals, and cumulative-transfer versus forcing-rate separation.
import DASHI.Chemistry.DeepTimeCarbonReservoirFluxBalanceExact
import DASHI.Chemistry.DeepTimeCarbonPathResidualBidiExact
import DASHI.Chemistry.CarbonForcingRateBidiExact

------------------------------------------------------------------------
-- Garlic/Allium organosulfur chemistry: molecular identity, exact finite
-- composition coordinates, source-backed small-molecule pathway balances,
-- allicin thiol reactivity, ajoene quorum-regulation evidence, preparation-time
-- sulfur trajectories, and mechanism-completeness firewalls.
import DASHI.Chemistry.AlliumMolecularIdentityExact
import DASHI.Chemistry.AlliumOrganosulfurMechanismExact
import DASHI.Chemistry.AlliumReactionNetworkCrossPollinationExact
import DASHI.Chemistry.AlliumMolecularTrajectoryExact

------------------------------------------------------------------------
-- Atomic-periodic-table cross-pollination: consumes the existing atom/valence,
-- molecular-assembly, admissible-reaction, temporal-trajectory and industrial
-- material-lineage owners as one fibre-over-time bridge.  The petrochemical
-- specialization keeps atomic chlorine, molecular chlorine, ethylene/VCM
-- identity, exact chlor-alkali stoichiometry and plant-process receipts apart.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact
import DASHI.Physics.Chemistry.AtomicPeriodicTable369PetrochemicalIdentityBridgeExact

-- Symmetry-resolved 3-D continuation: rich state is reconstructed from an
-- admissible coarse surface plus retained residual; chirality supplies the
-- first finite same-coarse/nonfactorability fixture; protein and DNA reuse the
-- existing stereochemistry, attractor, dihedral and rigid-motion owners.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdmissibleReconstructionEquivalenceExact
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChiralMolecularSeparatingPairExact
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinDNA3DAdapterExact

-- First same-object empirical chiral witness: D/L alanine share molecular
-- formula while stereochemical identity and measured optical response separate;
-- phase/environment remains part of the observation fibre.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AlanineChiralEmpiricalExact

-- Protein continuation: residue stereochemistry and peptide-backbone torsion
-- are retained as local residual coordinates over the primary-sequence chart;
-- Ramachandran geometry and PDB acquisition do not collapse into a unique-fold
-- or protein-function theorem.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinBackboneStereochemistryExact

-- Same-sequence empirical protein pair: E. coli adenylate kinase 4AKE/1AKE
-- supplies experimentally resolved open/unligated and closed/Ap5A-bound
-- conformations of the same polypeptide chain. Sequence alone therefore does
-- not determine the observed conformation in this fixture; context remains a
-- required fibre coordinate.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact

-- NDim geometric continuation: source-paid NMP--CORE and LID--CORE endpoint
-- coordinates replace the binary open/closed label with a retained two-axis
-- residual while preserving the NDim rule that extra axes are not automatic
-- consumer improvement or a complete transition mechanism.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNDimGeometricResidualExact

-- Four-corner structural reference continuation: 4AKE/1AKE plus 2AK3/1DVR
-- instantiate open/open, closed/closed and the two mixed domain labels.  The
-- mixed references are cross-homolog, so the square is explicitly blocked from
-- promotion to same-sequence NMP/LID independence evidence.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMixedStateReferenceSquareExact

-- Same-sequence computational refinement: the Ping et al. E. coli MD carrier
-- reports both off-diagonal NMP/LID combinations as simulated clusters.  This
-- pays a same-sequence computational four-corner carrier while remaining
-- distinct from four experimental PDB structures, thermodynamic independence,
-- kinetic independence, equilibrium populations, or a unique transition path.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSameSequenceSimulatedMixedStatesExact

-- Dynamical coupling refinement: Li, Liu & Ji 2015 pay both ligand-free closure
-- orders and an approximate 5.7:1 pathway-flux asymmetry favouring LID-first
-- closure.  Reachability and flux asymmetry are kept distinct from equilibrium
-- independence, universal rate constants, or an experimentally closed mechanism.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCouplingResidualExact

-- Weighted NDim state graph: equation-level alpha/beta/gamma/delta/epsilon/xi
-- states are connected into the source-paid primary and alternative routes,
-- weighted by the 5.7:1 path-flux receipt and paired with the two-angle free-
-- energy surface. Figure-level zeta and equation-level xi remain distinct
-- source labels until a same-object notation repair is explicitly paid.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact

-- Context-indexed landscape: the same LID--CORE / NMP--CORE axes carry distinct
-- ligand-free and ligand-bound free-energy surfaces. The bound landscape pays
-- an approx 8.0 kcal/mol open-to-closed delta G and strongly disfavors the
-- NMP-first region; ligand-free path weights are not transferred across context.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandConditionedLandscapeExact

-- Rate-observer adequacy: route topology can answer reachability but cannot
-- manufacture transition-rate answers.  The repaired observer retains a rate
-- coordinate, while source-paid Kramers diffusion calibrations remain distinct
-- from still-unacquired per-edge Figure 5/6 numeric labels and experiment.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseRateObserverAdequacyExact

-- FRET observer-axis refinement: two ligand-free single-molecule FRET studies
-- observe different residue/domain axes (LID--NMP versus LID--CORE) and report
-- different population summaries. Axis-erased observation is inadequate for
-- that query; retaining the measurement axis repairs the finite collision.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverAxisExact

-- Observer-axis join: either single FRET coordinate can collide while the
-- transverse coordinate changes.  The joined LID--NMP × LID--CORE observer
-- retains both declared axes by the generic required-axis join theorem, without
-- claiming complete protein-state recovery or simultaneous historical readout.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverJoinExact

-- Third-axis boundary: the joined two-distance observer remains query-relative.
-- Li-Liu-Ji use a three-CV AdK description (theta1, theta2, dLN); a repository-
-- local same-two-axis/different-third-axis collision proves that two declared
-- FRET axes cannot be promoted to complete NDim state recovery. A three-axis
-- observer repairs only the declared third-coordinate query.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisExact

-- Consumer-indexed Pareto selection: the two-axis join is the minimal eligible
-- observer for a declared two-axis consumer, while the third-coordinate query
-- excludes it and promotes the three-axis observer.  Description length and
-- NDim design costs are applied only after adequacy, never as physical truth.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverParetoExact

-- Counterexample-to-repair closure: the third-axis inadequacy witness now drives
-- the declared local refinement joinedTwo -> threeAxis.  The repo-native local
-- repair theorem constructs eligibility inside the same observer family before
-- minimal-description/Pareto ranking resumes; no new experiment is manufactured.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverLocalRepairExact

-- Generic promotion instantiation: the AdK local repair, minimal-eligible proof,
-- and Pareto selection are packaged through the domain-neutral Core theorem.
-- Li-Liu-Ji remain attributed only to the three-CV AdK premise; the generic
-- counterexample->repair->selection theorem is DASHI synthesis.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConsumerSafePromotionExact

-- Static-to-future promotion weld: the Pareto-selected three-axis model is
-- explicitly related to a query-adequate, frozen, dynamically safe joined
-- observer.  The included no-action dynamics is only a repository interface
-- fixture and is blocked from promotion to physical AdK kinetics or rates.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConsumerSafeFuturePromotionExact

-- Preferred nontrivial future-dynamics continuation: the six source-owned
-- alpha/beta/gamma/delta/epsilon/xi route edges become typed admissible actions.
-- The graph coordinate moves while the independent third-axis consumer world is
-- preserved, so dynamic safety is proved without identifying the two carriers.
-- Route topology remains computational/source-bounded, not experimental kinetics.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceBoundedFutureDynamicsExact

-- Composite source-bounded future promotion: the Pareto-selected three-axis
-- model is now welded to the non-empty graph action system through an explicit
-- application realisation relation.  Static selection, query adequacy, frozen
-- selection and dynamic safety remain independent payments; source attribution
-- is not transferred into the DASHI composition theorem.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceBoundedConsumerSafeFuturePromotionExact

-- Partial state-coordinate alignment: Figure-5 named states are related only to
-- source-paid theta1/theta2 regions.  Alpha/zeta inherit composed open/closed
-- endpoint angles; beta/gamma/delta/epsilon remain qualitative semi-open/semi-
-- closed regions; eta/lambda remain near-closed; per-state dLN stays unpaid.
-- Equation-level xi is deliberately not identified with Figure-level zeta.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialStateCoordinateAlignmentExact

-- Dynamics on the paid alignment fibre: states exist only when a graph node has
-- a retained Figure-state alignment.  This supports alpha->beta->gamma->delta
-- and alpha->beta->epsilon prefixes while refusing delta/epsilon->xi until the
-- xi/zeta seam is paid.  Partiality remains explicit rather than totalized.
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialAlignedDynamicsExact
