module DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.YMAristotleOperatorReturn2026Exact as LeanReturn
import DASHI.Physics.YangMills.YMOperatorDomainContinuumSources2026Exact as Src
import DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact as DenseGap
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as VacuumRecovery
import DASHI.Physics.Closure.YMSprint129MoscoLiminfStrongResolventClosure as Sprint129
import DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt as SelfAdjointReceipt

------------------------------------------------------------------------
-- BIDI return: existing Agda theorems -> Lean.
--
-- This is not a parallel implementation.  The current YM frontier consumes
-- the pre-existing theorem owners directly and returns their theorem shapes to
-- the Lean lane.  The older Sprint129 boolean/evidence receipt is retained as
-- provenance, but is not confused with a kernel theorem about actual closed
-- forms or resolvents.
------------------------------------------------------------------------

record AgdaToLeanInterface : Set where
  constructor agda-to-lean-interface
  field
    interfaceName : String
    motivatingSource : String
    requiredShape : String
    closedAsGenericCompiler : Bool
    closedForPhysicalYMProducer : Bool
    boundedReading : String

open AgdaToLeanInterface public

domainAwareHamiltonianInterface : AgdaToLeanInterface
domainAwareHamiltonianInterface = agda-to-lean-interface
  "DomainAwareHamiltonian"
  "Tosio Kato, Perturbation Theory for Linear Operators, DOI 10.1007/978-3-642-66282-9"
  "carrier H; domain D(H); operator H : D(H) -> carrier; common invariant dense core; gauge-action invariance; symmetry/self-adjointness on the stated domain; quotient compatibility of domain and action"
  false false
  "Current Lean uniqueness allows total H -> H generators with no boundedness hypothesis. Existing Agda SchrodingerSelfAdjointEvolutionReceipt explicitly remains an obligation surface rather than a physical self-adjoint Hamiltonian construction."

vacuumRecoveryGapInterface : AgdaToLeanInterface
vacuumRecoveryGapInterface = agda-to-lean-interface
  "VacuumOrthogonalRecoveryGapTransport"
  "Umberto Mosco, Convergence of Convex Sets and of Solutions of Variational Inequalities, DOI 10.1016/0001-8708(69)90009-7; Kazuhiro Kuwae and Takashi Shioya, Convergence of Spectral Structures: A Functional Analytic Theory and Its Applications to Spectral Geometry, DOI 10.4310/cag.2003.v11.n4.a1"
  "for each limiting vacuum-orthogonal vector, provide a finite vacuum-orthogonal recovery vector with norm domination, the finite uniform gap, and recovery-energy upper bound"
  true false
  "BalabanVacuumOrthogonalMoscoRecoveryExact already proves the generic recovery-system compiler in Agda. What remains is the physical YM recovery-system producer."

denseCoreGapInterface : AgdaToLeanInterface
denseCoreGapInterface = agda-to-lean-interface
  "DenseCoreSpectralExclusion"
  "Konrad Osterwalder and Robert Schrader, Axioms for Euclidean Green's Functions I/II, DOI 10.1007/BF01645738 and 10.1007/BF01608978"
  "clustering kills the positive-subgap projection on every vector of a dense centered core; continuity extends zero projection to the whole vacuum-orthogonal carrier"
  true false
  "BalabanClayDenseCoreSpectralGapExact is a genuine Agda theorem schema. Its physical dense-core/clustering/continuity producer remains conditional."

osReconstructionIdentificationInterface : AgdaToLeanInterface
osReconstructionIdentificationInterface = agda-to-lean-interface
  "OSReconstructedEvolutionIdentification"
  "Konrad Osterwalder and Robert Schrader, Axioms for Euclidean Green's Functions I/II, DOI 10.1007/BF01645738 and 10.1007/BF01608978"
  "construct continuum Schwinger functions satisfying the required OS package; reconstruct Hilbert-space dynamics; identify that evolution with the selected Yang--Mills Hamiltonian evolution on the physical carrier/common core"
  false false
  "Generator uniqueness can consume equality of evolutions once supplied; it does not prove equality of Yang--Mills and OS-reconstructed evolutions."

agdaToLeanInterfaces : List AgdaToLeanInterface
agdaToLeanInterfaces =
  domainAwareHamiltonianInterface ∷
  vacuumRecoveryGapInterface ∷
  denseCoreGapInterface ∷
  osReconstructionIdentificationInterface ∷ []

------------------------------------------------------------------------
-- Actual Agda theorem terms exported back to Lean-side work.
------------------------------------------------------------------------

denseCoreGapCompilerReturned :
  ∀ {CoreVector HilbertVector}
    (dataSet : DenseGap.DenseCoreProjectionData CoreVector HilbertVector) →
  DenseGap.UniformDenseCoreClustering dataSet →
  DenseGap.DenseCoreSpectralExclusion dataSet
denseCoreGapCompilerReturned = DenseGap.denseLocalClusteringImpliesGap

vacuumRecoveryGapCompilerReturned :
  (system : VacuumRecovery.VacuumOrthogonalRecoverySystem) →
  VacuumRecovery.PhysicalVacuumGapAfterRecovery system
vacuumRecoveryGapCompilerReturned = VacuumRecovery.physicalVacuumGapAfterRecovery

------------------------------------------------------------------------
-- Exact frontier ledger.
------------------------------------------------------------------------

record YMOperatorContinuumFrontier : Set where
  constructor ym-operator-continuum-frontier
  field
    representationIdentificationClosed : Bool
    defectTelescopeClosed : Bool
    principalChartAdmissionClosed : Bool
    nullQuotientSeparationClosed : Bool
    symmetryImpliesNullPreservationClosedForTotalLinearMaps : Bool
    generatorUniquenessClosedWithoutBoundednessHypothesisOnTotalMaps : Bool
    gaugeInvariantL2CarrierClosed : Bool
    carrierNonVacuityClosed : Bool
    boundedStrongLimitFormGapTransportClosed : Bool

    -- Existing Agda generic theorem compilers now explicitly consumed.
    denseCoreSpectralExclusionCompilerClosed : Bool
    vacuumOrthogonalRecoveryGapCompilerClosed : Bool

    -- Historical Sprint129 route is an evidence/Bool receipt, not the same
    -- object as an analytic theorem over closed forms/resolvents.
    sprint129MoscoEvidenceReceiptClosed : Bool
    sprint129AnalyticClosedFormKernelTheoremClosed : Bool

    -- Physical producers still required.
    balabanSelectedBackgroundAndStoredBondBudgetClosed : Bool
    literalYMActionVariationHamiltonianIdentificationClosed : Bool
    genuinePartialDomainHamiltonianFormalized : Bool
    commonInvariantDensePhysicalCoreConstructed : Bool
    physicalDenseCoreClusteringContinuityProducerClosed : Bool
    physicalVacuumRecoverySystemConstructed : Bool
    ymEvolutionEqualsOSReconstructedEvolutionClosed : Bool
    physicalClosedFormOrResolventIdentificationClosed : Bool
    finiteToContinuumYMConstructionClosed : Bool
    continuumOSWightmanPackageClosed : Bool
    clayPromotionClosed : Bool

open YMOperatorContinuumFrontier public

canonicalYMOperatorContinuumFrontier : YMOperatorContinuumFrontier
canonicalYMOperatorContinuumFrontier = ym-operator-continuum-frontier
  true true true true true true true true true
  true true
  Sprint129.mc1TheoremProvedHere false
  false false false false false false false false false false false

------------------------------------------------------------------------
-- Regression theorems.
------------------------------------------------------------------------

boundedGapTransportClosedIsTrue :
  boundedStrongLimitFormGapTransportClosed canonicalYMOperatorContinuumFrontier ≡ true
boundedGapTransportClosedIsTrue = refl

vacuumRecoveryCompilerClosedIsTrue :
  vacuumOrthogonalRecoveryGapCompilerClosed canonicalYMOperatorContinuumFrontier ≡ true
vacuumRecoveryCompilerClosedIsTrue = refl

denseCoreCompilerClosedIsTrue :
  denseCoreSpectralExclusionCompilerClosed canonicalYMOperatorContinuumFrontier ≡ true
denseCoreCompilerClosedIsTrue = refl

sprint129ReceiptClosedIsTrue :
  sprint129MoscoEvidenceReceiptClosed canonicalYMOperatorContinuumFrontier ≡ true
sprint129ReceiptClosedIsTrue = refl

sprint129ReceiptIsNotAnalyticKernelTheorem :
  sprint129AnalyticClosedFormKernelTheoremClosed canonicalYMOperatorContinuumFrontier ≡ false
sprint129ReceiptIsNotAnalyticKernelTheorem = refl

physicalVacuumRecoveryProducerClosedIsFalse :
  physicalVacuumRecoverySystemConstructed canonicalYMOperatorContinuumFrontier ≡ false
physicalVacuumRecoveryProducerClosedIsFalse = refl

genuinePartialDomainHamiltonianFormalizedIsFalse :
  genuinePartialDomainHamiltonianFormalized canonicalYMOperatorContinuumFrontier ≡ false
genuinePartialDomainHamiltonianFormalizedIsFalse = refl

physicalClosedFormOrResolventIdentificationClosedIsFalse :
  physicalClosedFormOrResolventIdentificationClosed canonicalYMOperatorContinuumFrontier ≡ false
physicalClosedFormOrResolventIdentificationClosedIsFalse = refl

clayPromotionClosedIsFalse :
  clayPromotionClosed canonicalYMOperatorContinuumFrontier ≡ false
clayPromotionClosedIsFalse = refl

------------------------------------------------------------------------
-- Cross-prover ownership firewalls inherited from the Lean return.
------------------------------------------------------------------------

leanGeneratorReturnNotTransported :
  LeanReturn.transportedIntoAgda LeanReturn.generatorUniquenessStatus ≡ false
leanGeneratorReturnNotTransported = refl

leanMassGapReturnIsBoundedOperatorTheorem :
  LeanReturn.boundedContinuousOperatorTheorem LeanReturn.massGapStrongLimitStatus ≡ true
leanMassGapReturnIsBoundedOperatorTheorem = refl

leanMassGapReturnIsNotFullUnboundedDomainTheorem :
  LeanReturn.fullUnboundedDomainTheorem LeanReturn.massGapStrongLimitStatus ≡ false
leanMassGapReturnIsNotFullUnboundedDomainTheorem = refl

------------------------------------------------------------------------
-- Existing Agda obligation-surface firewall.
------------------------------------------------------------------------

selfAdjointEvolutionReceiptStillStartsOpen :
  SelfAdjointReceipt.defaultSchrodingerSelfAdjointEvolutionFirstMissingTheorem ≡
  SelfAdjointReceipt.missingHilbertQuotientCarrier
selfAdjointEvolutionReceiptStillStartsOpen = refl

------------------------------------------------------------------------
-- Source-presence witnesses: metadata inhabitants, not physical proofs.
------------------------------------------------------------------------

katoSourcePresent : Src.LiteratureSource
katoSourcePresent = Src.katoPerturbationTheory

moscoSourcePresent : Src.LiteratureSource
moscoSourcePresent = Src.moscoVariationalConvergence
