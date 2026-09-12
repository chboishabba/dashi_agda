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
-- 4. What would actually decide historical priority.
------------------------------------------------------------------------

data PriorityResidual : Set where
  inspectPreReleaseSignedCrossSourceTerm : PriorityResidual
  inspectPreReleaseCriticalProductionSourceTerm : PriorityResidual
  establishExactABEndpointComposition : PriorityResidual
  recoverPreReleaseKernelOrIndependentCheckReceipt : PriorityResidual
  priorityAuditComplete : PriorityResidual

firstPriorityResidual : PriorityResidual
firstPriorityResidual = inspectPreReleaseSignedCrossSourceTerm

-- Certification is stronger evidence, but absence of certification does not
-- imply absence of a source proof term.
data NoCertificationImpliesNoProofTermPermission : Set where

data FalsePromotionBitImpliesMathematicalNegationPermission : Set where

noCertificationDoesNotImplyNoProofTerm :
  NoCertificationImpliesNoProofTermPermission → ⊥
noCertificationDoesNotImplyNoProofTerm ()

falsePromotionBitDoesNotNegateTheorem :
  FalsePromotionBitImpliesMathematicalNegationPermission → ⊥
falsePromotionBitDoesNotNegateTheorem ()

------------------------------------------------------------------------
-- 5. Four-alternative historical status is now deliberately conservative.
------------------------------------------------------------------------

data PreReleaseAlternativeStatus : Clay4.ClayAlternative4 → Set where
  aPriorityUnresolvedPendingSourceAudit :
    PreReleaseAlternativeStatus Clay4.A-euclidean-unforced-global
  bPriorityUnresolvedPendingSourceAudit :
    PreReleaseAlternativeStatus Clay4.B-periodic-unforced-global
  cNoLocatedPreReleaseForcedWitnessYet :
    PreReleaseAlternativeStatus Clay4.C-euclidean-forced-breakdown
  dNoLocatedPreReleaseForcedWitnessYet :
    PreReleaseAlternativeStatus Clay4.D-periodic-forced-breakdown

preReleaseStatusFor :
  (a : Clay4.ClayAlternative4) → PreReleaseAlternativeStatus a
preReleaseStatusFor Clay4.A-euclidean-unforced-global =
  aPriorityUnresolvedPendingSourceAudit
preReleaseStatusFor Clay4.B-periodic-unforced-global =
  bPriorityUnresolvedPendingSourceAudit
preReleaseStatusFor Clay4.C-euclidean-forced-breakdown =
  cNoLocatedPreReleaseForcedWitnessYet
preReleaseStatusFor Clay4.D-periodic-forced-breakdown =
  dNoLocatedPreReleaseForcedWitnessYet

------------------------------------------------------------------------
-- 6. Compact corrected ledger.
------------------------------------------------------------------------

preReleaseArchitectureSubstantial : Bool
preReleaseArchitectureSubstantial = true

preReleaseExactClaySolutionRefutedByClosureBits : Bool
preReleaseExactClaySolutionRefutedByClosureBits = false

preReleasePriorityClaimCurrentlyResolved : Bool
preReleasePriorityClaimCurrentlyResolved = false

preReleaseSourceTermAuditRequired : Bool
preReleaseSourceTermAuditRequired = true

preReleaseExactClaySolutionRefutedByClosureBitsIsFalse :
  preReleaseExactClaySolutionRefutedByClosureBits ≡ false
preReleaseExactClaySolutionRefutedByClosureBitsIsFalse = refl

preReleasePriorityClaimCurrentlyResolvedIsFalse :
  preReleasePriorityClaimCurrentlyResolved ≡ false
preReleasePriorityClaimCurrentlyResolvedIsFalse = refl

preReleaseSourceTermAuditRequiredIsTrue :
  preReleaseSourceTermAuditRequired ≡ true
preReleaseSourceTermAuditRequiredIsTrue = refl
