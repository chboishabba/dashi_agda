{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Physics.YangMills.YMOperatorDomainContinuumSources2026Exact as CanonicalSources

------------------------------------------------------------------------
-- Attribution boundary
--
-- This owner records two different things and does not collapse them:
--
--   * primary literature identity (DOI-bearing where independently verified),
--   * exact theorem artifacts supplied by the Aristotle Lean donor archive.
--
-- A paper citation does not import a theorem.  A verified Lean theorem does not
-- become an Agda kernel proof merely because its path/name is recorded here.
------------------------------------------------------------------------

wilson1974 : Attr.AttributedSource
wilson1974 = Attr.mkDOISource
  "Kenneth G. Wilson"
  "Confinement of quarks"
  "Physical Review D 10, 2445"
  "1974"
  "10.1103/PhysRevD.10.2445"
  "https://journals.aps.org/prd/abstract/10.1103/PhysRevD.10.2445"
  Attr.academicArticleSource
  "primary lattice-gauge provenance for the Wilson action; does not itself prove the DASHI/Aristotle finite-gap or continuum claims"
  Attr.publicAttribution

aristotleYMLiteratureAtlas : Attr.AttributedSourceAtlas
aristotleYMLiteratureAtlas = Attr.mkSourceAtlas
  "Yang-Mills Aristotle donor literature atlas"
  "DASHI Yang-Mills cross-prover parity"
  (wilson1974 ∷ [])
  "Wilson lattice-action provenance. Kato, Mosco, Kuwae-Shioya and Osterwalder-Schrader DOI-bearing sources remain canonical in YMOperatorDomainContinuumSources2026Exact and are imported rather than duplicated here."

canonicalOperatorContinuumSources : List CanonicalSources.LiteratureSource
canonicalOperatorContinuumSources = CanonicalSources.operatorDomainContinuumSources

record LeanTheoremArtifact : Set where
  constructor lean-theorem-artifact
  field
    project : String
    path : String
    stableIdentifier : String
    theoremRole : String
    suppliedWorkerReceipt : String
    theoremArtifactIsAgdaKernelProof : Bool
    theoremArtifactIsAgdaKernelProofIsFalse : theoremArtifactIsAgdaKernelProof ≡ false
    citationCreatesPhysicalAuthority : Bool
    citationCreatesPhysicalAuthorityIsFalse : citationCreatesPhysicalAuthority ≡ false

open LeanTheoremArtifact public

mkAristotleArtifact : String → String → String → LeanTheoremArtifact
mkAristotleArtifact file theorem role = lean-theorem-artifact
  "Aristotle Yang-Mills donor tar / output-final_aristotle"
  file
  theorem
  role
  "supplied archive reports lake build RequestProject green; retain this as donor provenance, not as an Agda kernel receipt"
  false refl false refl

mkAristotle8220Artifact : String → String → String → LeanTheoremArtifact
mkAristotle8220Artifact file theorem role = lean-theorem-artifact
  "Aristotle Yang-Mills varying-carrier tranche / 2026-09-17 worker return"
  file
  theorem
  role
  "supplied worker reports lake build RequestProject: 8220 jobs, zero errors, zero warnings; no sorry/axiom/postulate/@[implemented_by] in new material; headline #print axioms exactly propext, Classical.choice, Quot.sound. Donor receipt only; not an Agda kernel receipt."
  false refl false refl

vacuumSectorUniqueSolutionLean : LeanTheoremArtifact
vacuumSectorUniqueSolutionLean = mkAristotleArtifact
  "RequestProject/YangMills/VacuumSectorSpectralGap.lean"
  "VacuumGapDatum.exists_unique_solution_vacuumSector"
  "self-adjoint zero-vacuum form-gap datum -> unique vacuum-sector solution for every real lambda below the gap"

vacuumSectorResolventBoundLean : LeanTheoremArtifact
vacuumSectorResolventBoundLean = mkAristotleArtifact
  "RequestProject/YangMills/VacuumSectorSpectralGap.lean"
  "VacuumGapDatum.resolvent_bound_vacuumSector"
  "quantitative vacuum-sector bound ||psi|| <= (Delta-lambda)^-1 ||(H-lambda)psi||"

vacuumSectorEigenvalueExclusionLean : LeanTheoremArtifact
vacuumSectorEigenvalueExclusionLean = mkAristotleArtifact
  "RequestProject/YangMills/VacuumSectorSpectralGap.lean"
  "VacuumGapDatum.eigenvalue_eq_zero_of_lt_gap"
  "no nonzero excited eigenvalue below the vacuum gap"

continuumGapTransportLean : LeanTheoremArtifact
continuumGapTransportLean = mkAristotleArtifact
  "RequestProject/YangMills/ContinuumGapTransport.lean"
  "ContinuumGapTransport.continuumDatum"
  "uniform cutoff vacuum-form gap + vacuum-sector graph limit + limit self-adjoint/vacuum data -> continuum VacuumGapDatum"

sameEvolutionGapTransferLean : LeanTheoremArtifact
sameEvolutionGapTransferLean = mkAristotleArtifact
  "RequestProject/YangMills/SameObjectGapTransfer.lean"
  "SameObjectGapTransfer.vacuumGapDatum_of_same_evolution"
  "same evolution on a common core -> equality of unbounded Hamiltonians including domains -> transport the complete vacuum-gap datum"

literalSU2HamiltonianLean : LeanTheoremArtifact
literalSU2HamiltonianLean = mkAristotleArtifact
  "RequestProject/YangMills/Lattice/SU2YangMills.lean"
  "Lattice.ymHamiltonian_isSelfAdjoint / Lattice.ymHamiltonian_vacuum"
  "literal four-dimensional SU(2) Wilson-Gibbs energy form -> self-adjoint finite-spacing Hamiltonian with zero-energy vacuum"

literalSU2MassGapFromCoercivityLean : LeanTheoremArtifact
literalSU2MassGapFromCoercivityLean = mkAristotleArtifact
  "RequestProject/YangMills/Lattice/SU2YangMills.lean"
  "Lattice.lattice_massGap_of_coercivity"
  "literal finite-spacing SU(2) Wilson coercivity -> full MassGapConclusion"

literalSU2StrongCouplingGapLean : LeanTheoremArtifact
literalSU2StrongCouplingGapLean = mkAristotleArtifact
  "RequestProject/YangMills/Lattice/PhysicalStrongCoupling.lean"
  "Lattice.ym_phys_massGap_of_coupling_le"
  "gauge-invariant literal SU(2) Wilson theory has a positive fixed-spacing vacuum-sector gap when 64|beta|(n+1)^4 <= 1/10"

varyingCarrierTransportLean : LeanTheoremArtifact
varyingCarrierTransportLean = mkAristotle8220Artifact
  "RequestProject/YangMills/VaryingCarrierTransport.lean"
  "RequestProject.YangMills.VaryingCarrierTransport theorem family"
  "uniform intrinsic cutoff vacuum gaps transport through linear isometric embeddings from genuinely varying cutoff Hilbert spaces; no separate Hamiltonian/vacuum compatibility hypothesis is primitive"

literalSU2ContinuumWeldLean : LeanTheoremArtifact
literalSU2ContinuumWeldLean = mkAristotle8220Artifact
  "RequestProject/YangMills/Lattice/ContinuumWeld.lean"
  "RequestProject.YangMills.Lattice.ContinuumWeld theorem family"
  "literal four-dimensional SU(2) Wilson family + uniform positive gap + isometric embeddings + embedded vacuum-sector graph limit -> continuum mass-gap conclusion; OS variant additionally consumes same evolution on a common core"

literalSU2UniformGapReductionLean : LeanTheoremArtifact
literalSU2UniformGapReductionLean = mkAristotle8220Artifact
  "RequestProject/YangMills/Lattice/UniformGapReduction.lean"
  "RequestProject.YangMills.Lattice.UniformGapReduction theorem family"
  "literal Wilson transfer-form coercivity follows from |<P0 psi,P1 psi>| <= c ||psi||^2 on the vacuum complement, with finite gap a^-1(1-c); a trajectory-uniform c and Delta <= a_k^-1(1-c) supply the continuum-weld uniform gap"

literalSU2ZeroCouplingUniformGapLean : LeanTheoremArtifact
literalSU2ZeroCouplingUniformGapLean = mkAristotle8220Artifact
  "RequestProject/YangMills/Lattice/UniformGapReduction.lean"
  "zero-coupling c=0 uniform-volume witness"
  "at zero coupling the decorrelation estimate holds with c=0 for every volume, proving that unbounded volume alone is not the interacting continuum obstruction"

aristotleYMDonorArtifacts : List LeanTheoremArtifact
aristotleYMDonorArtifacts =
  vacuumSectorUniqueSolutionLean ∷
  vacuumSectorResolventBoundLean ∷
  vacuumSectorEigenvalueExclusionLean ∷
  continuumGapTransportLean ∷
  sameEvolutionGapTransferLean ∷
  literalSU2HamiltonianLean ∷
  literalSU2MassGapFromCoercivityLean ∷
  literalSU2StrongCouplingGapLean ∷
  varyingCarrierTransportLean ∷
  literalSU2ContinuumWeldLean ∷
  literalSU2UniformGapReductionLean ∷
  literalSU2ZeroCouplingUniformGapLean ∷ []

donorLeanTheoremIsAgdaKernelProof : Bool
donorLeanTheoremIsAgdaKernelProof = false

donorLeanTheoremIsAgdaKernelProofIsFalse : donorLeanTheoremIsAgdaKernelProof ≡ false
donorLeanTheoremIsAgdaKernelProofIsFalse = refl

fixedSpacingGapIsContinuumClayProof : Bool
fixedSpacingGapIsContinuumClayProof = false

fixedSpacingGapIsContinuumClayProofIsFalse : fixedSpacingGapIsContinuumClayProof ≡ false
fixedSpacingGapIsContinuumClayProofIsFalse = refl
