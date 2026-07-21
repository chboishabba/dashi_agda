module DASHI.Provenance.AIAssistedMathematicsProvenance where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Discovery, prompting, announcement, verification and formalisation are
-- distinct provenance roles.

data ProvenanceRole : Set where
  questionSource : ProvenanceRole
  promptingAgent : ProvenanceRole
  generationSystem : ProvenanceRole
  publicAnnouncer : ProvenanceRole
  executableVerifier : ProvenanceRole
  independentVerifier : ProvenanceRole
  kernelFormaliser : ProvenanceRole
  consequenceAuthor : ProvenanceRole

record AgentCredit : Set where
  constructor agentCredit
  field
    role : ProvenanceRole
    name : String
    qualification : String

open AgentCredit public

record DiscoveryProvenance : Set where
  constructor discoveryProvenance
  field
    publicDate : String
    credits : List AgentCredit
    sourceNote : String
    discoveryPriorityClaimedByDASHI : Bool
    discoveryPriorityClaimedByDASHIIsFalse :
      discoveryPriorityClaimedByDASHI ≡ false

alpogeFableProvenance : DiscoveryProvenance
alpogeFableProvenance =
  discoveryProvenance
    "2026-07-20"
    ( agentCredit questionSource "Akhil Mathew" "credited in the public announcement for posing the question"
    ∷ agentCredit promptingAgent "Levent Alpöge" "prompted and publicly announced the displayed map"
    ∷ agentCredit generationSystem "Fable" "credited in the public announcement for producing the example"
    ∷ agentCredit publicAnnouncer "Levent Alpöge" "public mathematical announcement"
    ∷ agentCredit executableVerifier "DASHI exact sparse-polynomial diagnostic" "independently recomputes the determinant and rational fibre"
    ∷ agentCredit kernelFormaliser "DASHI Agda verification tranche" "checks the polynomial syntax, differentiation, determinant, collision and logical consequence"
    ∷ [] )
    "roles are recorded from the public attribution and repository verification history; later independent verifiers and consequence authors should be appended rather than collapsed into discovery credit"
    false
    refl

record ProvenanceStageBoundary : Set where
  constructor mkProvenanceStageBoundary
  field
    generatedCandidateIsKernelProof : Bool
    generatedCandidateIsKernelProofIsFalse :
      generatedCandidateIsKernelProof ≡ false
    publicAnnouncementIsIndependentVerification : Bool
    publicAnnouncementIsIndependentVerificationIsFalse :
      publicAnnouncementIsIndependentVerification ≡ false
    executableCheckIsKernelNormalization : Bool
    executableCheckIsKernelNormalizationIsFalse :
      executableCheckIsKernelNormalization ≡ false
    kernelFormalisationSeparatelyNamed : Bool
    interpretation : String

provenanceStageBoundary : ProvenanceStageBoundary
provenanceStageBoundary =
  mkProvenanceStageBoundary
    false refl
    false refl
    false refl
    true
    "question, prompt, generation, announcement, executable verification, kernel formalisation and downstream consequences are separate provenance stages"
