module DASHI.Core.ClaimRelativeVerificationSOTAAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-BOUNDED SOTA ATLAS
--
-- These are external research references only.  The papers/authors retain
-- authority for their own reported methods and measurements.  DASHI owns only
-- this claim-relative role/ceiling classification and downstream adapters.
------------------------------------------------------------------------

data ExternalResearchRole : Set where
  specificationCompilationRole : ExternalResearchRole
  weakStrongVerificationRole : ExternalResearchRole
  abstentionBenchmarkRole : ExternalResearchRole
  constrainedDecodingRole : ExternalResearchRole
  specificationEvaluationRole : ExternalResearchRole

record ExternalResearchReference : Set where
  constructor external-research-reference
  field
    title : String
    authors : String
    venueOrStatus : String
    year : Nat
    sourceURL : String
    role : ExternalResearchRole
    supportedUse : String
    evidenceCeiling : String
    importedAsDASHITheorem : Bool
    importedAsDASHITheoremIsFalse : importedAsDASHITheorem ≡ false

open ExternalResearchReference public

formalJudge2026 : ExternalResearchReference
formalJudge2026 = external-research-reference
  "FormalJudge: A Neuro-Symbolic Paradigm for Agentic Oversight"
  "Jiayi Zhou; Yang Sheng; Hantao Lou; Yaodong Yang; Jie Fu"
  "ICML 2026 / PMLR 306"
  2026
  "https://proceedings.mlr.press/v306/zhou26ao.html"
  specificationCompilationRole
  "external evidence that natural-language intent -> formal specification is a material systems bottleneck and that Dafny/Z3-backed checking can be evaluated separately from probabilistic judging"
  "supports the authors' architecture and reported benchmark results only; does not prove DASHI specification fidelity, universal safety, or general truth"
  false refl

cheapCheck2026 : ExternalResearchReference
cheapCheck2026 = external-research-reference
  "When to Trust the Cheap Check: Weak and Strong Verification for Reasoning"
  "Shayan Kiyani; Sima Noorani; George J. Pappas; Hamed Hassani"
  "ICML 2026 / PMLR 306"
  2026
  "https://proceedings.mlr.press/v306/kiyani26a.html"
  weakStrongVerificationRole
  "external motivation for measuring incorrect acceptance, incorrect rejection, and strong-verification frequency under selective escalation"
  "supports the paper's formal policy analysis and experiments; does not make the DASHI escalation policy optimal or calibrated"
  false refl

agentAbstain2026 : ExternalResearchReference
agentAbstain2026 = external-research-reference
  "AgentAbstain: Do LLM Agents Know When Not to Act?"
  "Xun Liu; Yi Evie Zhang; Vira Kasprova; Parisa Rabbani; Pardis Sadat Zahraei; Tianyu Zhang; Ali Ebrahimpour-Boroojeny; Varun Chandrasekaran"
  "arXiv:2607.10059 (2026 preprint)"
  2026
  "https://arxiv.org/abs/2607.10059"
  abstentionBenchmarkRole
  "external motivation for paired should-act/should-abstain cases and for distinguishing pre-action abstention from post-hoc abstention"
  "preprint benchmark/report only; does not establish a universal abstention taxonomy or any DASHI agent performance"
  false refl

dccd2026 : ExternalResearchReference
dccd2026 = external-research-reference
  "The Hidden Cost of Structured Generation in LLMs: Draft-Conditioned Constrained Decoding"
  "Avinash Reddy; Thayne T. Walker; Jaime S. Ide; Amrit Singh Bedi"
  "ICML 2026 / PMLR 306"
  2026
  "https://proceedings.mlr.press/v306/reddy26a.html"
  constrainedDecodingRole
  "external evidence that token-level hard constraints can distort generation and that semantic planning can be separated from structural enforcement"
  "supports the paper's decoding analysis and experiments only; does not imply every constrained decoder harms every consumer"
  false refl

coins2026 : ExternalResearchReference
coins2026 = external-research-reference
  "How Powerful are LLMs in Generating Formal Program Specifications?"
  "Fanpeng Yang; Xing Li; Shuling Wang; Jie An; Zeyu Sun; Shenghua Feng; Wenhan Wang; Weiyi Wang; Naijun Zhan; Fanjiang Xu"
  "ICML 2026 / PMLR 306"
  2026
  "https://proceedings.mlr.press/v306/yang26am.html"
  specificationEvaluationRole
  "external motivation for evaluating specification quality on trusted cases rather than identifying proof success with specification quality"
  "supports Coins and its reported specification-evaluation results; does not certify DASHI-generated specifications or implementations"
  false refl

record ClaimRelativeVerificationSOTABoundary : Set where
  constructor claim-relative-verification-sota-boundary
  field
    externalSourceMentionCreatesDASHITheorem : Bool
    externalSourceMentionCreatesDASHITheoremIsFalse :
      externalSourceMentionCreatesDASHITheorem ≡ false
    reportedMetricCreatesGeneralLaw : Bool
    reportedMetricCreatesGeneralLawIsFalse :
      reportedMetricCreatesGeneralLaw ≡ false
    architectureSimilarityCreatesSameSystemIdentity : Bool
    architectureSimilarityCreatesSameSystemIdentityIsFalse :
      architectureSimilarityCreatesSameSystemIdentity ≡ false
    externalResultMayMotivateDeclaredExperiment : Bool
    externalResultMayMotivateDeclaredExperimentIsTrue :
      externalResultMayMotivateDeclaredExperiment ≡ true
    sourceAuthorshipRetained : Bool
    sourceAuthorshipRetainedIsTrue :
      sourceAuthorshipRetained ≡ true

canonicalClaimRelativeVerificationSOTABoundary :
  ClaimRelativeVerificationSOTABoundary
canonicalClaimRelativeVerificationSOTABoundary =
  claim-relative-verification-sota-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
