module DASHI.Biology.DrosophilaSymbolicRateLearningCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.DrosophilaEligibilityTraceLearningAuthorityExact as Eligibility
import DASHI.Biology.DrosophilaSymbolicInterfaceLearningExact as Symbolic
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Continuous-rate symbolic-learning cross-pollination.
--
-- This owner combines existing programme disciplines without importing their
-- claims wholesale:
--   * real-data / held-out promotion gates from the MaleCNS benchmark lane;
--   * finite-run-only stability receipts from the BIDI kernel lane;
--   * explicit dynamics/type separation from the threshold/margin lane;
--   * sparse MaleCNS execution with an explicit adjacency-orientation weld.
--
-- Continuous RateRNN dynamics are a specialization beside the ternary DASHI
-- kernel.  They do not replace it and do not identify the viral demo's hidden
-- learning mechanism.
------------------------------------------------------------------------

rateRuntimeSource : Source.AttributedSource
rateRuntimeSource = Source.mkNoDOISource
  "NSSIL"
  "Energy-efficient information processing and eligibility-trace plasticity: released RateRNN and Part-E supplement"
  "GitHub source revision"
  "2026"
  "https://github.com/NSSIL/Energy-efficient-information-processing-and-eligibility/tree/19bcd7d83a044f90ad691bff5bfe1df636b7150a"
  (Source.namedSourceKind "software implementation")
  "source locator for the released ReLU RateRNN recurrence and archived Part-E EProp-labelled supplementary recurrence; software source does not identify the viral Python/FizzBuzz training law"
  Source.publicAttribution

rateRuntimeCitationImportsNoProof :
  Source.citationImportsProof rateRuntimeSource ≡ false
rateRuntimeCitationImportsNoProof =
  Source.citationImportsProofIsFalse rateRuntimeSource

record SymbolicRateLearningCrossPollinationStatus : Set where
  constructor symbolicRateLearningCrossPollinationStatus
  field
    continuousRateSpecializationImplemented : Bool
    archivedPartETraceRuleLocated : Bool
    paperFactorizationLocated : Bool
    heldOutPromotionGateImplemented : Bool
    finiteRunStabilityOnly : Bool
    globalStabilityClaimed : Bool
    globalContractionClaimed : Bool
    -- This specifically means a ternary-kernel -> paper-level eligibility
    -- constructor.  The separate sparse RateRNN -> archived Part-E adapter
    -- below does not pay this stronger seam.
    kernelEligibilityAdapterImplemented : Bool
    maleCNSOrientationAdapterImplemented : Bool
    sparseRateArchivedTraceAdapterImplemented : Bool
    paperEligibilityConstructorRecovered : Bool
    viralDemoTrainingRuleLocated : Bool
    generalProgrammingPromotable : Bool

open SymbolicRateLearningCrossPollinationStatus public

canonicalSymbolicRateLearningStatus : SymbolicRateLearningCrossPollinationStatus
canonicalSymbolicRateLearningStatus = symbolicRateLearningCrossPollinationStatus
  true
  true
  true
  true
  true
  false
  false
  false
  true
  true
  false
  false
  false

continuousRateSpecializationIsPaid :
  continuousRateSpecializationImplemented canonicalSymbolicRateLearningStatus
  ≡ true
continuousRateSpecializationIsPaid = refl

archivedPartETraceRuleIsLocated :
  archivedPartETraceRuleLocated canonicalSymbolicRateLearningStatus ≡ true
archivedPartETraceRuleIsLocated = refl

heldOutPromotionGateIsPaid :
  heldOutPromotionGateImplemented canonicalSymbolicRateLearningStatus ≡ true
heldOutPromotionGateIsPaid = refl

maleCNSOrientationAdapterIsPaid :
  maleCNSOrientationAdapterImplemented canonicalSymbolicRateLearningStatus ≡ true
maleCNSOrientationAdapterIsPaid = refl

sparseRateArchivedTraceAdapterIsPaid :
  sparseRateArchivedTraceAdapterImplemented canonicalSymbolicRateLearningStatus
  ≡ true
sparseRateArchivedTraceAdapterIsPaid = refl

kernelEligibilityAdapterStillUnpaid :
  kernelEligibilityAdapterImplemented canonicalSymbolicRateLearningStatus ≡ false
kernelEligibilityAdapterStillUnpaid = refl

paperEligibilityConstructorStillUnpaid :
  paperEligibilityConstructorRecovered canonicalSymbolicRateLearningStatus
  ≡ false
paperEligibilityConstructorStillUnpaid = refl

globalStabilityStillUnclaimed :
  globalStabilityClaimed canonicalSymbolicRateLearningStatus ≡ false
globalStabilityStillUnclaimed = refl

generalProgrammingStillNotPromotable :
  generalProgrammingPromotable canonicalSymbolicRateLearningStatus ≡ false
generalProgrammingStillNotPromotable = refl

------------------------------------------------------------------------
-- WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data RateDynamicsTernaryKernelCollapsePermission : Set where

data FiniteRunGlobalStabilityPromotionPermission : Set where

data ArchivedTraceViralTrainingPromotionPermission : Set where

data PaperArchivedTraceCollapsePermission : Set where

data HeldOutGeneralProgrammingPromotionPermission : Set where

data SourceTargetPostPreCollapsePermission : Set where

data SparseArchivedPaysPaperEligibilityPermission : Set where

rateDynamicsDoNotReplaceTernaryKernel :
  RateDynamicsTernaryKernelCollapsePermission → ⊥
rateDynamicsDoNotReplaceTernaryKernel ()

finiteRunBoundDoesNotProveGlobalStability :
  FiniteRunGlobalStabilityPromotionPermission → ⊥
finiteRunBoundDoesNotProveGlobalStability ()

archivedTraceRuleDoesNotPayViralTrainingRule :
  ArchivedTraceViralTrainingPromotionPermission → ⊥
archivedTraceRuleDoesNotPayViralTrainingRule ()

paperFactorizationDoesNotCollapseToArchivedTraceRule :
  PaperArchivedTraceCollapsePermission → ⊥
paperFactorizationDoesNotCollapseToArchivedTraceRule ()

heldOutLearningDoesNotEstablishGeneralProgramming :
  HeldOutGeneralProgrammingPromotionPermission → ⊥
heldOutLearningDoesNotEstablishGeneralProgramming ()

-- MaleCNS stores A[pre,post], whereas the released RateRNN multiplies
-- W[post,pre] by the presynaptic rate vector.  The orientation weld is an
-- explicit transpose and may not be erased as a notational coincidence.
maleCNSSourceTargetRequiresExplicitTranspose :
  SourceTargetPostPreCollapsePermission → ⊥
maleCNSSourceTargetRequiresExplicitTranspose ()

-- The sparse adapter executes the archived supplementary recurrence on the
-- source-exact continuous RateRNN carrier.  It does not reconstruct the
-- paper-level information/energy eligibility constructor.
sparseArchivedAdapterDoesNotPayPaperEligibilityConstructor :
  SparseArchivedPaysPaperEligibilityPermission → ⊥
sparseArchivedAdapterDoesNotPayPaperEligibilityConstructor ()

------------------------------------------------------------------------
-- Existing authority/debt remains authoritative.
------------------------------------------------------------------------

paperEligibilityAuthority : Eligibility.EligibilityTraceAuthorityReceipt
paperEligibilityAuthority = Eligibility.canonicalEligibilityTraceAuthorityReceipt

viralImplementationDebtStillOpen :
  Symbolic.primaryImplementationLocated
    Symbolic.canonicalPythonDemoImplementationDebt
  ≡ false
viralImplementationDebtStillOpen = Symbolic.primaryImplementationStillUnpaid
