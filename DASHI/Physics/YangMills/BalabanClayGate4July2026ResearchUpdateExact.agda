module DASHI.Physics.YangMills.BalabanClayGate4July2026ResearchUpdateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayMassGapClaimEcosystemQuarantineExact as Quarantine

------------------------------------------------------------------------
-- July 2026 source-normalization update.
--
-- This file deliberately distinguishes:
--   * peer-reviewed methodological authority;
--   * primary-paper metadata/abstract confirmation;
--   * secondary locators whose equation claims still require the primary text;
--   * claimed complete solutions admitted only under the standing quarantine rule.
------------------------------------------------------------------------

record LiteratureAuditEntry : Set where
  constructor literatureEntry
  field
    authors : String
    title : String
    venueYearPages : String
    identifier : String
    peerReviewed : Bool
    admissibleAsMethodAuthority : Bool
    admissibleAsPhysicalYangMillsTheorem : Bool
    usableAsMechanismLocator : Bool
    auditNote : String

open LiteratureAuditEntry public

froehlich1974OSAxiomAuthority : LiteratureAuditEntry
froehlich1974OSAxiomAuthority = literatureEntry
  "Jürg Fröhlich"
  "Verification of Axioms for Euclidean and Relativistic Fields and Haag's Theorem in a Class of P(phi)2-Models"
  "Annales de l'Institut Henri Poincaré, Section A 21 (1974), 271--317"
  "NUMDAM AIHPA_1974__21_4_271_0; no DOI recorded"
  true
  true
  false
  true
  "legitimate source for model-level OS-axiom verification and reconstruction methodology; not a four-dimensional Yang--Mills mass-gap theorem"

balabanPartIIAbstractConfirmation : LiteratureAuditEntry
balabanPartIIAbstractConfirmation = literatureEntry
  "Tadeusz Bałaban"
  "Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation"
  "Communications in Mathematical Physics 122 (1989), 355--392"
  "DOI 10.1007/BF01238433"
  true
  true
  true
  false
  "the publisher/indexing abstract explicitly says the R-operation bounds complete ultraviolet stability as formulated in Theorem 1; this verifies the capstone architecture, but not the unviewed text or constants of equations (1.75), (1.89), or (1.100)"

harrisGhoussoub1975Authority : LiteratureAuditEntry
harrisGhoussoub1975Authority = literatureEntry
  "N. Ghoussoub"
  "Processus de Harris abstraits"
  "Annales de l'Institut Henri Poincaré, Section B 11 (1975), 381--395"
  "NUMDAM AIHPB_1975__11_4_381_0; no DOI recorded"
  true
  true
  false
  true
  "legitimate Harris-process provenance; applying drift/minorization or an equivalent contraction theorem to the physical boundary dynamics remains a separate theorem"

davoudiSavage2012Authority : LiteratureAuditEntry
davoudiSavage2012Authority = literatureEntry
  "Zohreh Davoudi and Martin J. Savage"
  "Restoration of Rotational Symmetry in the Continuum Limit of Lattice Field Theories"
  "Physical Review D 86 (2012), 054505"
  "DOI 10.1103/PhysRevD.86.054505; arXiv:1204.4146"
  true
  true
  false
  true
  "legitimate perturbative precedent for O(a^2) rotational-anisotropy suppression; it does not establish the nonperturbative Yang--Mills OS1 theorem"

philArchiveDefinitiveProofQuarantine : Quarantine.ClaimedSolutionRiskEntry
philArchiveDefinitiveProofQuarantine = Quarantine.claimedSolutionRisk
  "PhilArchive author/metadata to be preserved from the retrieved document"
  "The Definitive Proof of the Four-Dimensional Yang--Mills Mass Gap"
  "PhilArchive preprint repository"
  "PhilArchive locator NIETEO-12v11"
  false
  false
  true
  "apply the standing quarantine rule: no global theorem premise; independently reproduce any isolated lemma in DASHI conventions"

record LocatorTarget : Set where
  constructor locatorTarget
  field
    source : String
    claimedLocation : String
    claimedMechanism : String
    primaryVerificationRequired : Bool
    admissibleAsAuthority : Bool
    repositoryTarget : String

open LocatorTarget public

balabanEquation175Locator : LocatorTarget
balabanEquation175Locator = locatorTarget
  "Lluis Eriksson, Large-Field Suppression for Lattice Gauge Theories, viXra:2602.0056"
  "Bałaban Part II, equation (1.75)"
  "uniformity in slow-field/background dependence contributes only an O(1) multiplicative constant"
  true
  false
  "T-operation enlarged-region locality, admissible-background uniformity, and compensated six-factor budget"

balabanEquation189IndependentLocator : LocatorTarget
balabanEquation189IndependentLocator = locatorTarget
  "Lluis Eriksson, Large-Field Suppression for Lattice Gauge Theories, viXra:2602.0056"
  "Bałaban Part II, equation (1.89)"
  "uniform T-operation small-factor bound on admissible backgrounds"
  true
  false
  "BalabanClayGate4CanonicalCompensatedEquation189Exact"

nonperturbativeAnisotropyLocator : LocatorTarget
nonperturbativeAnisotropyLocator = locatorTarget
  "From Lattice Mass Gap to Continuum SU(2) Yang--Mills, Zenodo record 18824739"
  "locator paper, February 2026"
  "Dobrushin--Shlosman complete analyticity reduces OS1 restoration to finitely many per-polymer anisotropy coefficients bounded by O(a^2)"
  true
  false
  "OS1 per-polymer anisotropy coefficient target; use Davoudi--Savage only as perturbative precedent"

------------------------------------------------------------------------
-- Reconstruction cyclicity normalization.
------------------------------------------------------------------------

record OSReconstructionCyclicOutput (Hilbert Observable Vector : Set) : Set₁ where
  field
    hilbertCarrier : Hilbert
    vacuum : Vector
    positiveTimeVector : Observable → Vector
    PositiveTimeObservable : Observable → Set
    NonzeroVector : Vector → Set
    Overlap : Vector → Vector → Set
    cyclicVacuumDetects : ∀ vector → NonzeroVector vector →
      Σ Observable (λ observable →
        PositiveTimeObservable observable ×
        Overlap (positiveTimeVector observable) vector)

open OSReconstructionCyclicOutput public

-- The mathematical reconstruction theorem includes a cyclic vacuum. DASHI's
-- explicit adapter remains necessary because the older reconstructed-theory
-- carrier did not store this output field.
osReconstructionIncludesCyclicVacuumLevel : ProofLevel
osReconstructionIncludesCyclicVacuumLevel = verifiedLiterature

osCyclicityAdapterEngineeringCorrectionLevel : ProofLevel
osCyclicityAdapterEngineeringCorrectionLevel = machineChecked

------------------------------------------------------------------------
-- Finite BFS construction target.
------------------------------------------------------------------------

record FiniteBFSConstructionTarget : Set where
  field
    finiteVertexEnumeration : Set
    decidableVertexEquality : Set
    decidableAdjacency : Set
    nonemptyConnectedPolymer : Set
    frontierLayersByVisitedSetRecursion : Set
    recursionStrictlyShrinksUndiscoveredSet : Set
    terminatesWithinVertexCount : Set
    eachNonRootGetsOnePreviousLayerParent : Set
    leastPreviousLayerParentByFiniteOrder : Set
    parentDistanceDropsByOne : Set
    parentPointersAcyclic : Set
    parentPointersSpanExactlyPolymer : Set
    bfsDistanceIsShortestPathDistance : Set

open FiniteBFSConstructionTarget public

bfsFiniteAlgorithmSourceNote : String
bfsFiniteAlgorithmSourceNote =
  "standard finite BFS: V0={root}; Vi contains undiscovered neighbours of V(i-1); assign each newly discovered vertex the least previous-layer neighbour; terminate because the undiscovered finite set strictly shrinks"

-- The literature confirms the proof template and that no analytic or choice
-- principle is needed. The repository must still implement the visited-set
-- recursion and its invariants for the concrete periodic polymer carrier.
bfsAlgorithmAndCorrectnessMethodLevel : ProofLevel
bfsAlgorithmAndCorrectnessMethodLevel = verifiedLiterature

periodicVisitedSetBFSImplementationLevel : ProofLevel
periodicVisitedSetBFSImplementationLevel = conditional

------------------------------------------------------------------------
-- OS1 anisotropy target refinement.
------------------------------------------------------------------------

record PerPolymerAnisotropyTarget : Set₁ where
  field
    AnisotropyCoefficient Polymer Scale Bound : Set
    latticeSpacing : Scale → Bound
    coefficient : Polymer → Scale → AnisotropyCoefficient
    Norm : AnisotropyCoefficient → Bound
    square : Bound → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    polymerMajorant : Polymer → Bound
    perPolymerA2Bound : ∀ polymer scale →
      LessEqual (Norm (coefficient polymer scale))
        (multiply (polymerMajorant polymer)
          (square (latticeSpacing scale)))

open PerPolymerAnisotropyTarget public

os1PerPolymerA2MechanismLevel : ProofLevel
os1PerPolymerA2MechanismLevel = conditional

------------------------------------------------------------------------
-- Audit receipts.
------------------------------------------------------------------------

july2026SourceClassificationLevel : ProofLevel
july2026SourceClassificationLevel = machineChecked

balabanTheoremOneAbstractArchitectureLevel : ProofLevel
balabanTheoremOneAbstractArchitectureLevel = verifiedLiterature

balabanEquation175PrimaryTextLevel : ProofLevel
balabanEquation175PrimaryTextLevel = conditional

philArchiveDefinitiveProofAcceptedAsAuthority : ProofLevel
philArchiveDefinitiveProofAcceptedAsAuthority = quarantined

zenodoAnisotropyClaimAcceptedAsAuthority : ProofLevel
zenodoAnisotropyClaimAcceptedAsAuthority = quarantined

harrisPhysicalBoundaryApplicationLevel : ProofLevel
harrisPhysicalBoundaryApplicationLevel = conditional
