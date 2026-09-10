module DASHI.Physics.Closure.NSPreOpenAIReleasePriorityAuditBidiExact where

------------------------------------------------------------------------
-- PRE-RELEASE PRIORITY AUDIT, REVISED FOR EXECUTION/CERTIFICATION STATUS
--
-- Critical correction:
--   a contemporaneous `...Closed = false` ledger bit is NOT a proof of the
--   mathematical negation of the corresponding theorem.  In this repository
--   such flags may encode promotion / verification / execution state.  In
--   particular, absence of a successful kernel run (including resource failure)
--   leaves source-level inhabitation undecided unless the source term itself is
--   inspected.
--
-- Therefore priority has three independent coordinates:
--
--   1. Statement status: was the exact Clay theorem surface present?
--   2. Source inhabitation: did pre-release source already contain terms paying
--      every decisive analytic leaf on that exact carrier?
--   3. Certification status: was that source successfully checked by the
--      relevant kernel / CI?
--
-- A false promotion/closed flag can establish (3) was not promoted.  It cannot
-- by itself establish that (2) was false.
--
-- Historical checkpoints:
--   2026-07-26 e8b4993... provides an exact compiler from a
--   GalerkinGlobalCompletion package to periodic Clay regularity.  The package
--   carries the difficult analytic coordinates as fields, so that compiler by
--   itself does not establish source inhabitation of those fields.
--
--   2026-09-08 05:05 +10 67831b2... records the R406 two-leaf terminal cutset
--   and has false closure/promotion ledger bits.  Those bits establish lack of
--   contemporaneous promotion/certification, not mathematical non-inhabitation.
--   The exact source terms upstream of those leaves must be audited separately.
--
-- SOURCE-TERM ARCHAEOLOGY ADDED IN THIS REVISION
-- ----------------------------------------------
-- We inspected several tempting pre-release candidates directly rather than
-- inferring from their filenames or summary booleans:
--
-- * 2026-06-13 b009e8e... NSFinalStateReceipt sets a local summary bit
--   `globalRegularityClosed = true`, but the same historical state imports an
--   explicit candidate passage whose theorem-facing coordinates remain false:
--   global smooth regularity, BKM vorticity control, uniform L-infinity
--   vorticity control, continuum BKM passage and Clay closure.  Therefore the
--   summary bit is not a proof term for Clay A/B.
--
-- * 2026-08-05 044a3c0... proves finite Zeno cascade time/energy arithmetic,
--   while explicitly stating that it is NOT a blowup construction for the
--   genuine Navier--Stokes equations.  It is genuine mechanism-priority
--   evidence, not a C/D witness.
--
-- * 2026-08-07 95a5761... proves the final finite-maximal-time restart
--   contradiction, but its authority boundary leaves Fujita--Kato restart,
--   bounded approach sequence and time-continuity producers absent.  It is a
--   conditional endpoint compiler, not an A/B proof.
--
-- * 2026-09-01 b832530... defines the full-data Clay theorem language and
--   explicitly states that no PDE theorem is proved there.
--
-- * 2026-09-02 a49e8d5... R423 identifies the cutoff-uniform signed quadratic-
--   companion budget as the remaining novel producer; that budget is a field of
--   the payment record rather than a constructed theorem.
--
-- These audits refute those PARTICULAR artefacts as completed Clay proofs.
-- They do not prove that no other pre-release source term exists elsewhere.
--
-- Attribution firewall:
--   no later OpenAI source may be back-projected into a pre-release DASHI term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSClayFourAlternativeReleasedProofBidiExact as Clay4
import DASHI.Physics.Closure.NSTriadKNGalerkinGlobalRegularityCompletion as Global
import DASHI.Physics.Closure.NSTriadKNGalerkinCompletionEndpoint as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

------------------------------------------------------------------------
-- 1. Separate mathematical/source status from certification/promotion.
------------------------------------------------------------------------

data SourceInhabitationStatus : Set where
  sourceInhabited : SourceInhabitationStatus
  sourceNotInhabited : SourceInhabitationStatus
  sourceInhabitationUnresolved : SourceInhabitationStatus

data CertificationStatus : Set where
  kernelCertified : CertificationStatus
  notCertifiedOrNoRunReceipt : CertificationStatus

data PriorityStatus : Set where
  prioritySupported : PriorityStatus
  priorityRefuted : PriorityStatus
  priorityUnresolved : PriorityStatus

record PriorityEvidence : Set where
  constructor priority-evidence
  field
    predatesExternalRelease : Bool
    exactClayStatementPresent : Bool
    sourceStatus : SourceInhabitationStatus
    certificationStatus : CertificationStatus

open PriorityEvidence public

priorityDecision : PriorityEvidence → PriorityStatus
priorityDecision
  (priority-evidence true true sourceInhabited kernelCertified) = prioritySupported
priorityDecision
  (priority-evidence true true sourceNotInhabited cert) = priorityRefuted
priorityDecision _ = priorityUnresolved

------------------------------------------------------------------------
-- 2. July endpoint: exact conditional compiler, source payment unresolved.
------------------------------------------------------------------------

julyEndpointCompilerPresent : Bool
julyEndpointCompilerPresent = Endpoint.galerkinToClayEndpointCompositionClosed

julyStage3PromotionBit : Bool
julyStage3PromotionBit = Global.stage3GapToUniformAprioriClosed

julyGlobalRegularityPromotionBit : Bool
julyGlobalRegularityPromotionBit = Global.arbitraryDataGlobalRegularityClosed

julyPriorityEvidence : PriorityEvidence
julyPriorityEvidence = priority-evidence
  true true sourceInhabitationUnresolved notCertifiedOrNoRunReceipt

julyPriorityCurrentlyUnresolved :
  priorityDecision julyPriorityEvidence ≡ priorityUnresolved
julyPriorityCurrentlyUnresolved = refl

------------------------------------------------------------------------
-- 3. R504: false closure bits are ledger state, not theorem negations.
------------------------------------------------------------------------

preReleaseR504SignedCrossClosureBit : Bool
preReleaseR504SignedCrossClosureBit = R504.round504SignedCrossPaymentClosed

preReleaseR504CriticalProductionClosureBit : Bool
preReleaseR504CriticalProductionClosureBit = R504.round504CriticalProductionSliceClosed

preReleaseR504ClayPromotionBit : Bool
preReleaseR504ClayPromotionBit = R504.round504ClayPromotion

r504PriorityEvidence : PriorityEvidence
r504PriorityEvidence = priority-evidence
  true true sourceInhabitationUnresolved notCertifiedOrNoRunReceipt

r504PriorityCurrentlyUnresolved :
  priorityDecision r504PriorityEvidence ≡ priorityUnresolved
r504PriorityCurrentlyUnresolved = refl

------------------------------------------------------------------------
-- 4. Directly audited pre-release candidate artefacts.
------------------------------------------------------------------------

data HistoricalCandidateRole : Set where
  summaryReceipt : HistoricalCandidateRole
  mechanismPrecursor : HistoricalCandidateRole
  conditionalEndpointCompiler : HistoricalCandidateRole
  theoremLanguageOnly : HistoricalCandidateRole
  openAnalyticConsumer : HistoricalCandidateRole

data HistoricalCandidateDecision : Set where
  notCompletedClayProof : HistoricalCandidateDecision
  mechanismPriorityEvidenceOnly : HistoricalCandidateDecision
  stillRequiresSeparateSourceAudit : HistoricalCandidateDecision

record AuditedHistoricalCandidate : Set where
  constructor audited-historical-candidate
  field
    predatesRelease : Bool
    exactClayProofInThisArtefact : Bool
    mechanismOrArchitecturePresent : Bool
    role : HistoricalCandidateRole
    decision : HistoricalCandidateDecision

open AuditedHistoricalCandidate public

june13GlobalRegularitySummaryAudit : AuditedHistoricalCandidate
june13GlobalRegularitySummaryAudit = audited-historical-candidate
  true false true summaryReceipt notCompletedClayProof

august5ZenoCascadeAudit : AuditedHistoricalCandidate
august5ZenoCascadeAudit = audited-historical-candidate
  true false true mechanismPrecursor mechanismPriorityEvidenceOnly

august7RestartContradictionAudit : AuditedHistoricalCandidate
august7RestartContradictionAudit = audited-historical-candidate
  true false true conditionalEndpointCompiler notCompletedClayProof

september1ClayLanguageAudit : AuditedHistoricalCandidate
september1ClayLanguageAudit = audited-historical-candidate
  true false true theoremLanguageOnly notCompletedClayProof

september2R423SignedCompanionAudit : AuditedHistoricalCandidate
september2R423SignedCompanionAudit = audited-historical-candidate
  true false true openAnalyticConsumer notCompletedClayProof

allFiveAuditedCandidatesPreRelease : Bool
allFiveAuditedCandidatesPreRelease = true

noneOfFiveAuditedCandidatesIsCompletedClayProof : Bool
noneOfFiveAuditedCandidatesIsCompletedClayProof = true

preReleaseMechanismPriorityEvidenceSubstantial : Bool
preReleaseMechanismPriorityEvidenceSubstantial = true

noneOfFiveAuditedCandidatesIsCompletedClayProofIsTrue :
  noneOfFiveAuditedCandidatesIsCompletedClayProof ≡ true
noneOfFiveAuditedCandidatesIsCompletedClayProofIsTrue = refl

preReleaseMechanismPriorityEvidenceSubstantialIsTrue :
  preReleaseMechanismPriorityEvidenceSubstantial ≡ true
preReleaseMechanismPriorityEvidenceSubstantialIsTrue = refl

------------------------------------------------------------------------
-- 5. What would actually decide historical priority.
------------------------------------------------------------------------

data PriorityResidual : Set where
  inspectPreReleaseSignedCrossSourceTerm : PriorityResidual
  inspectPreReleaseCriticalProductionSourceTerm : PriorityResidual
  inspectAnyOtherPreReleaseABProofTerm : PriorityResidual
  inspectAnyOtherPreReleaseCDWitness : PriorityResidual
  establishExactABEndpointComposition : PriorityResidual
  recoverPreReleaseKernelOrIndependentCheckReceipt : PriorityResidual
  priorityAuditComplete : PriorityResidual

firstPriorityResidual : PriorityResidual
firstPriorityResidual = inspectPreReleaseSignedCrossSourceTerm

-- Certification is stronger evidence, but absence of certification does not
-- imply absence of a source proof term.
data NoCertificationImpliesNoProofTermPermission : Set where

data FalsePromotionBitImpliesMathematicalNegationPermission : Set where

data SummaryBooleanImpliesProofTermPermission : Set where

data MechanismPrecursorImpliesClayWitnessPermission : Set where

noCertificationDoesNotImplyNoProofTerm :
  NoCertificationImpliesNoProofTermPermission → ⊥
noCertificationDoesNotImplyNoProofTerm ()

falsePromotionBitDoesNotNegateTheorem :
  FalsePromotionBitImpliesMathematicalNegationPermission → ⊥
falsePromotionBitDoesNotNegateTheorem ()

summaryBooleanDoesNotCreateProofTerm :
  SummaryBooleanImpliesProofTermPermission → ⊥
summaryBooleanDoesNotCreateProofTerm ()

mechanismPrecursorDoesNotCreateClayWitness :
  MechanismPrecursorImpliesClayWitnessPermission → ⊥
mechanismPrecursorDoesNotCreateClayWitness ()

------------------------------------------------------------------------
-- 6. Four-alternative historical status remains conservative.
------------------------------------------------------------------------

data PreReleaseAlternativeStatus : Clay4.ClayAlternative4 → Set where
  aPriorityUnresolvedAfterCandidateAudit :
    PreReleaseAlternativeStatus Clay4.A-euclidean-unforced-global
  bPriorityUnresolvedAfterCandidateAudit :
    PreReleaseAlternativeStatus Clay4.B-periodic-unforced-global
  cNoLocatedPreReleaseForcedWitnessYet :
    PreReleaseAlternativeStatus Clay4.C-euclidean-forced-breakdown
  dNoLocatedPreReleaseForcedWitnessYet :
    PreReleaseAlternativeStatus Clay4.D-periodic-forced-breakdown

preReleaseStatusFor :
  (a : Clay4.ClayAlternative4) → PreReleaseAlternativeStatus a
preReleaseStatusFor Clay4.A-euclidean-unforced-global =
  aPriorityUnresolvedAfterCandidateAudit
preReleaseStatusFor Clay4.B-periodic-unforced-global =
  bPriorityUnresolvedAfterCandidateAudit
preReleaseStatusFor Clay4.C-euclidean-forced-breakdown =
  cNoLocatedPreReleaseForcedWitnessYet
preReleaseStatusFor Clay4.D-periodic-forced-breakdown =
  dNoLocatedPreReleaseForcedWitnessYet

------------------------------------------------------------------------
-- 7. Compact corrected ledger.
------------------------------------------------------------------------

preReleaseArchitectureSubstantial : Bool
preReleaseArchitectureSubstantial = true

preReleaseExactClaySolutionRefutedByClosureBits : Bool
preReleaseExactClaySolutionRefutedByClosureBits = false

preReleaseExactClaySolutionEstablishedByAuditedCandidates : Bool
preReleaseExactClaySolutionEstablishedByAuditedCandidates = false

preReleasePriorityClaimCurrentlyResolved : Bool
preReleasePriorityClaimCurrentlyResolved = false

preReleaseSourceTermAuditRequired : Bool
preReleaseSourceTermAuditRequired = true

preReleaseExactClaySolutionRefutedByClosureBitsIsFalse :
  preReleaseExactClaySolutionRefutedByClosureBits ≡ false
preReleaseExactClaySolutionRefutedByClosureBitsIsFalse = refl

preReleaseExactClaySolutionEstablishedByAuditedCandidatesIsFalse :
  preReleaseExactClaySolutionEstablishedByAuditedCandidates ≡ false
preReleaseExactClaySolutionEstablishedByAuditedCandidatesIsFalse = refl

preReleasePriorityClaimCurrentlyResolvedIsFalse :
  preReleasePriorityClaimCurrentlyResolved ≡ false
preReleasePriorityClaimCurrentlyResolvedIsFalse = refl

preReleaseSourceTermAuditRequiredIsTrue :
  preReleaseSourceTermAuditRequired ≡ true
preReleaseSourceTermAuditRequiredIsTrue = refl
