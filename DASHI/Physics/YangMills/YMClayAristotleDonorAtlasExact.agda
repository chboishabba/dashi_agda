{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Physics.YangMills.YMOperatorDomainContinuumSources2026Exact as CanonicalSources
import DASHI.Physics.YangMills.YMClayAristotleRouteSLiteralWilsonDonorExact as RouteS20260919

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

mkAristotleSecondRoundArtifact : String → String → String → LeanTheoremArtifact
mkAristotleSecondRoundArtifact file theorem role = lean-theorem-artifact
  "Aristotle Yang-Mills transfer-operator/frontier-recut tranche / 2026-09-17 second worker return"
  file
  theorem
  role
  "supplied second-round worker status reports lake build RequestProject green and no sorry/axiom/postulate/@[implemented_by] in the new material; retained as Lean donor provenance only, not as an Agda kernel receipt or a physical F1 inhabitant"
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
literalSU2UniformGapReductionLean = mkAristotleSecondRoundArtifact
  "RequestProject/YangMills/Lattice/UniformGapReduction.lean"
  "ym_uniform_gap_of_trajectory_decorrelation / trajectory_gap_bound_of_defect"
  "literal Wilson transfer-form coercivity is reduced to per-step decorrelation constants c_k with Delta*a_k <= 1-c_k; one trajectory-uniform c<1 is not required"

literalSU2TransferOperatorGapLean : LeanTheoremArtifact
literalSU2TransferOperatorGapLean = mkAristotleSecondRoundArtifact
  "RequestProject/YangMills/Lattice/TransferOperatorGap.lean"
  "decorrelation_iff_phase_separated and literal transfer-operator gap identities"
  "defines the literal Euclidean transfer operator T=P1*P0, identifies q(psi,psi)=||psi||^2-Re<Tpsi,psi>, and equates the two-slice correlation payment with phase separation of the slice embeddings"

literalSU2FrontierF1F3F4Lean : LeanTheoremArtifact
literalSU2FrontierF1F3F4Lean = mkAristotleSecondRoundArtifact
  "RequestProject/YangMills/Lattice/FrontierF1F3F4.lean"
  "clay_massGap_of_F1_F3 / clay_massGap_os_of_F1_F3_F4 / clay_massGap_of_transfer_defect_F3"
  "recut literal endpoint: F1+F3 gives the continuum mass-gap conclusion; F4 adds the OS same-object endpoint; transfer-defect F1 is accepted directly"

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
  literalSU2TransferOperatorGapLean ∷
  literalSU2FrontierF1F3F4Lean ∷
  literalSU2ZeroCouplingUniformGapLean ∷ []

donorLeanTheoremIsAgdaKernelProof : Bool
donorLeanTheoremIsAgdaKernelProof = false

donorLeanTheoremIsAgdaKernelProofIsFalse : donorLeanTheoremIsAgdaKernelProof ≡ false
donorLeanTheoremIsAgdaKernelProofIsFalse = refl

fixedSpacingGapIsContinuumClayProof : Bool
fixedSpacingGapIsContinuumClayProof = false

fixedSpacingGapIsContinuumClayProofIsFalse : fixedSpacingGapIsContinuumClayProof ≡ false
fixedSpacingGapIsContinuumClayProofIsFalse = refl

------------------------------------------------------------------------
-- 2026-09-19 literal Route-S tranche.
------------------------------------------------------------------------

routeS20260919ArchiveSHA256 : String
routeS20260919ArchiveSHA256 =
  "95bb6c4c2613a4dff9750940757094354d9344f78e63a3db7ded36cf08567137"

routeS20260919LeanKernelRevalidated : Bool
routeS20260919LeanKernelRevalidated =
  RouteS20260919.routeSLeanKernelRevalidatedAtSuppliedProject

routeS20260919LeanKernelRevalidatedIsTrue :
  routeS20260919LeanKernelRevalidated ≡ true
routeS20260919LeanKernelRevalidatedIsTrue =
  RouteS20260919.routeSLeanKernelRevalidatedAtSuppliedProjectIsTrue

routeS20260919IsAgdaKernelProof : Bool
routeS20260919IsAgdaKernelProof =
  RouteS20260919.routeSLeanTheoremIsAgdaKernelProof

routeS20260919IsAgdaKernelProofIsFalse :
  routeS20260919IsAgdaKernelProof ≡ false
routeS20260919IsAgdaKernelProofIsFalse =
  RouteS20260919.routeSLeanTheoremIsAgdaKernelProofIsFalse
