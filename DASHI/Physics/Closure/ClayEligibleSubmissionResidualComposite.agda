module DASHI.Physics.Closure.ClayEligibleSubmissionResidualComposite where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Clay-eligible submission residual composite.
--
-- This lane intentionally avoids importing sibling candidate/math surfaces.
-- Other workers are editing those modules concurrently, so this receipt
-- records the cross-domain submission state with independent Bool/String
-- fields and keeps every Clay/terminal promotion fail-closed.

data SubmissionDomain : Set where
  NSDomain :
    SubmissionDomain
  YMDomain :
    SubmissionDomain
  Paper8UCTDomain :
    SubmissionDomain

data FirstResidual : Set where
  NSATheoremAcceptanceResidual :
    FirstResidual
  NSA6TheoremAcceptanceResidual :
    FirstResidual
  YMSelfAdjointQuotientResidual :
    FirstResidual
  YMH3aAuthorityResidual :
    FirstResidual
  YMExternalAcceptanceResidual :
    FirstResidual
  UCT1PromotionEvidenceResidual :
    FirstResidual
  UCT2PromotionEvidenceResidual :
    FirstResidual
  UCT3PromotionEvidenceResidual :
    FirstResidual
  UCT4PromotionEvidenceResidual :
    FirstResidual

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

domainLabel : SubmissionDomain → String
domainLabel NSDomain =
  "NS"
domainLabel YMDomain =
  "YM"
domainLabel Paper8UCTDomain =
  "Paper8/UCT"

firstResidualLabel : FirstResidual → String
firstResidualLabel NSATheoremAcceptanceResidual =
  "NS-A theorem acceptance"
firstResidualLabel NSA6TheoremAcceptanceResidual =
  "NS-A6 theorem acceptance"
firstResidualLabel YMSelfAdjointQuotientResidual =
  "YM self-adjoint quotient"
firstResidualLabel YMH3aAuthorityResidual =
  "YM H3a authority"
firstResidualLabel YMExternalAcceptanceResidual =
  "YM external acceptance"
firstResidualLabel UCT1PromotionEvidenceResidual =
  "UCT.1 promotion evidence"
firstResidualLabel UCT2PromotionEvidenceResidual =
  "UCT.2 promotion evidence"
firstResidualLabel UCT3PromotionEvidenceResidual =
  "UCT.3 promotion evidence"
firstResidualLabel UCT4PromotionEvidenceResidual =
  "UCT.4 promotion evidence"

submissionDomains : List SubmissionDomain
submissionDomains =
  NSDomain ∷ YMDomain ∷ Paper8UCTDomain ∷ []

submissionDomainCount : Nat
submissionDomainCount =
  listLength submissionDomains

submissionDomainCountIs3 :
  submissionDomainCount ≡ 3
submissionDomainCountIs3 = refl

firstResiduals : List FirstResidual
firstResiduals =
  NSATheoremAcceptanceResidual
  ∷ NSA6TheoremAcceptanceResidual
  ∷ YMSelfAdjointQuotientResidual
  ∷ YMH3aAuthorityResidual
  ∷ YMExternalAcceptanceResidual
  ∷ UCT1PromotionEvidenceResidual
  ∷ UCT2PromotionEvidenceResidual
  ∷ UCT3PromotionEvidenceResidual
  ∷ UCT4PromotionEvidenceResidual
  ∷ []

firstResidualCount : Nat
firstResidualCount =
  listLength firstResiduals

firstResidualCountIs9 :
  firstResidualCount ≡ 9
firstResidualCountIs9 = refl

localArithmeticDone : Bool
localArithmeticDone = true

localArithmeticDoneIsTrue :
  localArithmeticDone ≡ true
localArithmeticDoneIsTrue = refl

localArithmeticSource : String
localArithmeticSource =
  "YM-A arithmetic recorded done as input flag: existing sibling modules may supply it, but this composite does not import them."

clayEligibleDomains : Nat
clayEligibleDomains = zero

clayEligibleDomainsIsZero :
  clayEligibleDomains ≡ zero
clayEligibleDomainsIsZero = refl

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

paper8UCTPromoted : Bool
paper8UCTPromoted = false

terminalClaySubmissionPromoted : Bool
terminalClaySubmissionPromoted = false

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

paper8UCTPromotedIsFalse :
  paper8UCTPromoted ≡ false
paper8UCTPromotedIsFalse = refl

terminalClaySubmissionPromotedIsFalse :
  terminalClaySubmissionPromoted ≡ false
terminalClaySubmissionPromotedIsFalse = refl

record ClayEligibleSubmissionResidualComposite : Set where
  constructor mkClayEligibleSubmissionResidualComposite
  field
    domains :
      List SubmissionDomain
    domainCount :
      Nat
    domainCountIs3 :
      domainCount ≡ 3
    localArithmeticDoneField :
      Bool
    localArithmeticDoneFieldIsTrue :
      localArithmeticDoneField ≡ true
    clayEligibleDomainCount :
      Nat
    clayEligibleDomainCountIsZero :
      clayEligibleDomainCount ≡ zero
    residuals :
      List FirstResidual
    residualCount :
      Nat
    residualCountIs9 :
      residualCount ≡ 9
    navierStokesClayStillFalse :
      clayNavierStokesPromoted ≡ false
    yangMillsClayStillFalse :
      clayYangMillsPromoted ≡ false
    paper8UCTStillFalse :
      paper8UCTPromoted ≡ false
    terminalClaySubmissionStillFalse :
      terminalClaySubmissionPromoted ≡ false
    summary :
      String

open ClayEligibleSubmissionResidualComposite public

canonicalClayEligibleSubmissionResidualComposite :
  ClayEligibleSubmissionResidualComposite
canonicalClayEligibleSubmissionResidualComposite =
  mkClayEligibleSubmissionResidualComposite
    submissionDomains
    submissionDomainCount
    refl
    localArithmeticDone
    refl
    clayEligibleDomains
    refl
    firstResiduals
    firstResidualCount
    refl
    refl
    refl
    refl
    refl
    "O: Clay-eligible submission residual composite. R: domains are NS, YM, and Paper8/UCT. C: YM-A localArithmeticDone=true is a recorded input flag. S: clayEligibleDomains=zero. L: first residuals are NS-A/A6 theorem acceptance, YM self-adjoint quotient/H3a authority/external acceptance, and UCT.1-UCT.4 promotion evidence. P: all Clay and terminal promotion flags remain false. G: no sibling imports are required while concurrent lanes are unstable. F: residual ledger only; no Clay-eligible domain is promoted."
