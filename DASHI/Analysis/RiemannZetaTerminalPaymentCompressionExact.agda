module DASHI.Analysis.RiemannZetaTerminalPaymentCompressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact as Off
import DASHI.Analysis.RiemannG2PoleQuotientGammaAllowanceDirectCompilerExact as Gamma
import DASHI.Analysis.RiemannAristotleRHFinalAllowanceLeafSchedulerExact as RH

------------------------------------------------------------------------
-- RH/ZETA TERMINAL PAYMENT COMPRESSION
--
-- The two final payments are not opaque leaves. Existing direct compilers expose
-- their smallest currently-live producer obligations. This owner records those
-- obligations so the scheduler attacks them directly instead of re-opening
-- already-owned near/far, Gamma-source discovery, or final contradiction code.
------------------------------------------------------------------------

data TerminalSubleaf : Set where
  offSignedNearAtCommonCutoff : TerminalSubleaf
  offNearPlusFarFitsAssignedAllowance : TerminalSubleaf
  gammaCandidateEqualsFinalProducer : TerminalSubleaf
  gammaBudgetFitsAssignedAllowance : TerminalSubleaf


data SubleafKind : Set where
  sameObjectOrProvenance : SubleafKind
  signedAnalyticPayment : SubleafKind
  assignedAllowanceFit : SubleafKind


subleafKind : TerminalSubleaf → SubleafKind
subleafKind offSignedNearAtCommonCutoff = signedAnalyticPayment
subleafKind offNearPlusFarFitsAssignedAllowance = assignedAllowanceFit
subleafKind gammaCandidateEqualsFinalProducer = sameObjectOrProvenance
subleafKind gammaBudgetFitsAssignedAllowance = assignedAllowanceFit

subleafReference : TerminalSubleaf → String
subleafReference offSignedNearAtCommonCutoff =
  "Off: signed near response at the same quarter-period crossing cutoff used by the final producer"
subleafReference offNearPlusFarFitsAssignedAllowance =
  "Off: B_near(J) + owned B_far(J) <= downstream-assigned A_off"
subleafReference gammaCandidateEqualsFinalProducer =
  "Gamma: recovered epsGamma/gammaConeEnvelope lineage is the exact final 8889 pole-quotient producer"
subleafReference gammaBudgetFitsAssignedAllowance =
  "Gamma: actual same-taper final B_Gamma <= downstream-assigned A_Gamma"

------------------------------------------------------------------------
-- Exact current-state pins from the direct compilers.
------------------------------------------------------------------------

offNearFarCompositionAlreadyOwned :
  Off.PoleQuotientOffAllowanceDirectCompilerBoundary.nearFarCompilerAlreadyOwnsFullComposition
    Off.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
offNearFarCompositionAlreadyOwned = refl

offFarShellNeedsNoFreshAnalysis :
  Off.PoleQuotientOffAllowanceDirectCompilerBoundary.farShellNeedsFreshAnalysis
    Off.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ false
offFarShellNeedsNoFreshAnalysis = refl

offSignedNearLeafLive :
  Off.PoleQuotientOffAllowanceDirectCompilerBoundary.signedNearEvaluationAtCommonCutoffRemainsAnalyticLeaf
    Off.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
offSignedNearLeafLive = refl

offAllowanceFitLive :
  Off.PoleQuotientOffAllowanceDirectCompilerBoundary.chosenNearPlusFarMustFitAssignedAllowance
    Off.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
offAllowanceFitLive = refl

offFinalPaymentIsCompilerOutput :
  Off.PoleQuotientOffAllowanceDirectCompilerBoundary.finalOffTargetAndAllowancePaymentCompile
    Off.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
offFinalPaymentIsCompilerOutput = refl

gammaCandidateFamilyAlreadyRecovered :
  Gamma.PoleQuotientGammaAllowanceDirectCompilerBoundary.concreteCandidateGammaLineageRecovered
    Gamma.canonicalPoleQuotientGammaAllowanceDirectCompilerBoundary ≡ true
gammaCandidateFamilyAlreadyRecovered = refl

gammaFinalProducerIdentityStillOpen :
  Gamma.PoleQuotientGammaAllowanceDirectCompilerBoundary.candidateLineageAlreadyIdentifiedWithFinal8889Producer
    Gamma.canonicalPoleQuotientGammaAllowanceDirectCompilerBoundary ≡ false
gammaFinalProducerIdentityStillOpen = refl

gammaAllowancePaymentCompilesAfterInput :
  Gamma.PoleQuotientGammaAllowanceDirectCompilerBoundary.finalGammaAllowancePaymentCompiles
    Gamma.canonicalPoleQuotientGammaAllowanceDirectCompilerBoundary ≡ true
gammaAllowancePaymentCompilesAfterInput = refl

rhStillNotDerived :
  RH.FinalRHAllowanceSchedulerBoundary.rhDerived
    RH.canonicalFinalRHAllowanceSchedulerBoundary ≡ false
rhStillNotDerived = refl

------------------------------------------------------------------------
-- Shortest-path scheduler reading.
--
-- Gamma has one source/same-object seam ahead of its terminal analytic allowance
-- fit. Off has no analogous source-discovery seam: its near/far composition and
-- far shell are already owned, so work begins immediately at the signed-near
-- common-cutoff payment and assigned-allowance fit.
------------------------------------------------------------------------

data TerminalPhase : Set where
  representationFirst : TerminalPhase
  analyticPayment : TerminalPhase


phase : TerminalSubleaf → TerminalPhase
phase gammaCandidateEqualsFinalProducer = representationFirst
phase offSignedNearAtCommonCutoff = analyticPayment
phase offNearPlusFarFitsAssignedAllowance = analyticPayment
phase gammaBudgetFitsAssignedAllowance = analyticPayment

record TerminalPaymentCompressionBoundary : Set where
  constructor terminal-payment-compression-boundary
  field
    offFarShellShouldBeReproved : Bool
    offFarShellShouldBeReprovedIsFalse : offFarShellShouldBeReproved ≡ false
    gammaGenericSourceDiscoveryStillLive : Bool
    gammaGenericSourceDiscoveryStillLiveIsFalse : gammaGenericSourceDiscoveryStillLive ≡ false
    gammaSameConsumerProducerIdentityStillLive : Bool
    gammaSameConsumerProducerIdentityStillLiveIsTrue : gammaSameConsumerProducerIdentityStillLive ≡ true
    finalPaymentRecordsShouldBeHandBuiltAfterInputs : Bool
    finalPaymentRecordsShouldBeHandBuiltAfterInputsIsFalse : finalPaymentRecordsShouldBeHandBuiltAfterInputs ≡ false
    fourSubleavesAreClaimsOfProof : Bool
    fourSubleavesAreClaimsOfProofIsFalse : fourSubleavesAreClaimsOfProof ≡ false

canonicalTerminalPaymentCompressionBoundary : TerminalPaymentCompressionBoundary
canonicalTerminalPaymentCompressionBoundary =
  terminal-payment-compression-boundary false refl false refl true refl false refl false refl
