module DASHI.Governance.SituatedBiomarkerPNFSourceWeldExact where

-- Actual DASHI PNF/ITIR interface weld (no new PNF ontology).
-- Authorship: original DASHI bridge; Alice Brown corpus and John Anthony
-- Brown study design are imported PRIOR ART, never endorsements of these
-- biological conclusions. Personal permission is scoped to OPTIONAL
-- biometric processing. Public testimony and separately authorised legal
-- procedures are not silenced by this type.
open import DASHI.Core.Prelude
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Interop.PNFSpectralNumericABICore as NumericABI
import DASHI.Interop.SensibLawSemanticPromotionPolicy as Semantic
import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Governance.SituatedBiomarkerObserverAgencyExact as Agency
import DASHI.Governance.SituatedCortisolPNFAdmissibilityExact as Causal
import DASHI.Governance.SituatedCortisolAssayGluingExact as Assay
import DASHI.Governance.SituatedDevelopmentalUltrametricExact as Dev

-- This is an OPTIONAL-use source contract; PNF validity/semantic fit are
-- further distinct requirements. In particular 'admissible' is the
-- internal candidate status, not legal or clinical authority.
record CandidateWithSubjectPermission
  {Subject : Set}
  (verification : Agency.ConsentVerification Subject)
  (person : Subject)
  (candidate : PNF.CandidatePNF) : Set where
  constructor candidate-with-subject-permission
  field
    permittedUse : Agency.ScopedBiomarkerUse Subject verification person
    pnfAdmissible : PNF.AdmissiblePNF
    selectedCandidateIsOriginal :
      PNF.AdmissiblePNF.candidate pnfAdmissible ≡ candidate
    sourceAndScopeReviewed : Set
    originalSourcePaid : sourceAndScopeReviewed

open CandidateWithSubjectPermission public

-- A PNF candidate is not upgraded by its source label, high-confidence
-- heuristic, person-specific inference, or assent to optional use.
admittedCandidateNeedsActualPNFStatus :
  ∀ {Subject : Set}
    {verification : Agency.ConsentVerification Subject}
    {person : Subject}
    {candidate : PNF.CandidatePNF} →
  CandidateWithSubjectPermission verification person candidate →
  PNF.validity candidate ≡ PNF.admissible
admittedCandidateNeedsActualPNFStatus receipt =
  subst
    (λ c → PNF.validity c ≡ PNF.admissible)
    (selectedCandidateIsOriginal receipt)
    (PNF.AdmissiblePNF.candidateIsAdmissible
      (pnfAdmissible receipt))

-- Existing canonical policy ignores the heuristic bits (including an
-- inferred high biomarker likelihood): only structural evidence can
-- change the tetralemma result.
heuristicOnlyCortisolClaimAbstains :
  (heuristicFor heuristicAgainst : Bool)
  (target provenance : String) →
  Semantic.promote
    (Semantic.heuristicCandidate heuristicFor heuristicAgainst target provenance)
  ≡ Tetralemma.neither
heuristicOnlyCortisolClaimAbstains =
  Semantic.heuristic-only-abstains

-- No downstream numeric-ABI promotion can be forged in this seam.
noNumericAbiTruthPromotion :
  NumericABI.PNFSpectralNumericABIPromotion → ⊥
noNumericAbiTruthPromotion =
  NumericABI.pnfSpectralNumericABIPromotionImpossible

-- A precise biometric readout does not identify causal source. This is
-- the prerequisite counterexample to every attempted mind-reading claim.
preciseCortisolAloneCannotIdentifyInstitutionalCause :
  Causal.measurementValue Causal.independentlyOccurred
  ≡ Causal.measurementValue Causal.institutionContributed
  × (Causal.causalAttribution Causal.independentlyOccurred
    ≡ Causal.causalAttribution Causal.institutionContributed → ⊥)
preciseCortisolAloneCannotIdentifyInstitutionalCause =
  refl , (λ ())

-- An ungluable pair of assays only means the *selected model* supplies
-- no common latent history; it is not evidence of contamination or lying.
incompatibleToyAssaysNeedModelReview :
  Assay.JointAssayExplanation 2 0 → ⊥
incompatibleToyAssaysNeedModelReview =
  Assay.noCommonHistoryForContradictoryReadings

-- The actual developmental leaf geometry is a source-level property
-- of the finite candidate tree and not an independently established
-- biological relationship.
finiteDevelopmentalUltrametric :
  (x y z : Dev.DevelopmentalLeaf) →
  Dev.treeDistance x z ≤
  (Dev.treeDistance x y ⊔ Dev.treeDistance y z)
finiteDevelopmentalUltrametric = Dev.treeDistanceStrongTriangle

-- No legalized harm coordinate is constructed by this module.
