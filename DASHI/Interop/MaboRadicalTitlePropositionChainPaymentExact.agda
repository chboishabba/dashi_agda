module DASHI.Interop.MaboRadicalTitlePropositionChainPaymentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.MaboRadicalTitleExactSourcePaymentExact as Exact

------------------------------------------------------------------------
-- ONE-PROPOSITION EXPLANATION-CONE PAYMENT
--
-- Intended runtime counterpart:
--   slr/crates/sl-evidence-payment
--
-- This owner is deliberately narrower than a holding/truth proof. It answers:
-- can the reader open one bounded Why? cone for the radical-title proposition?
--
-- Support cannot be replaced by a residual. It requires both a retained PNF
-- observation and independent source-span provenance on the observation and
-- graph-revision sides. Qualifier/defeater/comparator coordinates may be paid
-- observations or explicit retained residuals, so the cone can expose what is
-- unresolved without silently closing it.
------------------------------------------------------------------------

and : Bool → Bool → Bool
and false _ = false
and true b = b

record PropositionRoleCoordinate : Set where
  constructor propositionRoleCoordinate
  field
    observationPresent : Bool
    pnfRevisionPresent : Bool
    observationProvenanceHasExactSpan : Bool
    graphRevisionHasExactSpan : Bool
    explicitResidualRetained : Bool

open PropositionRoleCoordinate public

observationPaid : PropositionRoleCoordinate → Bool
observationPaid r =
  and (observationPresent r)
    (and (pnfRevisionPresent r)
      (and (observationProvenanceHasExactSpan r)
           (graphRevisionHasExactSpan r)))

roleCovered : PropositionRoleCoordinate → Bool
roleCovered r with observationPaid r
... | true = true
... | false = explicitResidualRetained r

record RadicalTitlePropositionPayment : Set where
  constructor radicalTitlePropositionPayment
  field
    propositionReference : String
    exactSourcePayment : Exact.ExactRadicalTitlePayment
    supportRole : PropositionRoleCoordinate
    qualifierRole : PropositionRoleCoordinate
    defeaterRole : PropositionRoleCoordinate
    comparatorRole : PropositionRoleCoordinate
    applicabilityPaid : Bool
    claimTruthPaid : Bool

open RadicalTitlePropositionPayment public

propositionChainPaid : RadicalTitlePropositionPayment → Bool
propositionChainPaid p =
  and (Exact.exactRadicalTitleSourceReady (exactSourcePayment p))
    (and (observationPaid (supportRole p))
      (and (roleCovered (qualifierRole p))
        (and (roleCovered (defeaterRole p))
             (roleCovered (comparatorRole p)))))

data WhyDisposition : Set where
  executeBoundedWhy : WhyDisposition
  deferDetailedPropositionChain : WhyDisposition

whyDisposition : RadicalTitlePropositionPayment → WhyDisposition
whyDisposition p with propositionChainPaid p
... | true = executeBoundedWhy
... | false = deferDetailedPropositionChain

------------------------------------------------------------------------
-- Canonical finite fixtures.
------------------------------------------------------------------------

paidObservation : PropositionRoleCoordinate
paidObservation = propositionRoleCoordinate true true true true false

explicitResidual : PropositionRoleCoordinate
explicitResidual = propositionRoleCoordinate false false false false true

pnfOnlyWithoutGraphSpan : PropositionRoleCoordinate
pnfOnlyWithoutGraphSpan = propositionRoleCoordinate true true true false false

missingRole : PropositionRoleCoordinate
missingRole = propositionRoleCoordinate false false false false false

canonicalBoundedWhy : RadicalTitlePropositionPayment
canonicalBoundedWhy = radicalTitlePropositionPayment
  "mabo:proposition:radical-title-native-title"
  Exact.canonicalPaidSpan
  paidObservation
  explicitResidual
  explicitResidual
  explicitResidual
  false
  false

sourceOnlyNoSupport : RadicalTitlePropositionPayment
sourceOnlyNoSupport = radicalTitlePropositionPayment
  "mabo:proposition:radical-title-native-title"
  Exact.canonicalPaidSpan
  missingRole
  explicitResidual
  explicitResidual
  explicitResidual
  false
  false

pnfSupportWithoutIndependentSourceWeld : RadicalTitlePropositionPayment
pnfSupportWithoutIndependentSourceWeld = radicalTitlePropositionPayment
  "mabo:proposition:radical-title-native-title"
  Exact.canonicalPaidSpan
  pnfOnlyWithoutGraphSpan
  explicitResidual
  explicitResidual
  explicitResidual
  false
  false

paidQualifierBoundedWhy : RadicalTitlePropositionPayment
paidQualifierBoundedWhy = radicalTitlePropositionPayment
  "mabo:proposition:radical-title-native-title"
  Exact.canonicalPaidSpan
  paidObservation
  paidObservation
  explicitResidual
  explicitResidual
  false
  false

canonicalChainPaysBoundedWhy : propositionChainPaid canonicalBoundedWhy ≡ true
canonicalChainPaysBoundedWhy = refl

canonicalWhyExecutes : whyDisposition canonicalBoundedWhy ≡ executeBoundedWhy
canonicalWhyExecutes = refl

sourceAloneCannotPayWhy :
  whyDisposition sourceOnlyNoSupport ≡ deferDetailedPropositionChain
sourceAloneCannotPayWhy = refl

pnfParityWithoutIndependentSpanCannotPayWhy :
  whyDisposition pnfSupportWithoutIndependentSourceWeld
    ≡ deferDetailedPropositionChain
pnfParityWithoutIndependentSpanCannotPayWhy = refl

paidQualifierMayReplaceQualifierResidual :
  whyDisposition paidQualifierBoundedWhy ≡ executeBoundedWhy
paidQualifierMayReplaceQualifierResidual = refl

boundedWhyDoesNotPayApplicability : applicabilityPaid canonicalBoundedWhy ≡ false
boundedWhyDoesNotPayApplicability = refl

boundedWhyDoesNotPayTruth : claimTruthPaid canonicalBoundedWhy ≡ false
boundedWhyDoesNotPayTruth = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ExactSpanCreatesPropositionChainPermission : Set where
data PNFParityCreatesSourceProvenancePermission : Set where
data ResidualizedSupportMayPayPermission : Set where
data BoundedWhyCreatesApplicabilityPermission : Set where
data BoundedWhyCreatesClaimTruthPermission : Set where
data ExplicitResidualMeansPropositionFalsePermission : Set where

exactSpanCannotCreatePropositionChain :
  ExactSpanCreatesPropositionChainPermission → ⊥
exactSpanCannotCreatePropositionChain ()

pnfParityCannotCreateSourceProvenance :
  PNFParityCreatesSourceProvenancePermission → ⊥
pnfParityCannotCreateSourceProvenance ()

supportCannotBeResidualizedAway :
  ResidualizedSupportMayPayPermission → ⊥
supportCannotBeResidualizedAway ()

boundedWhyCannotCreateApplicability :
  BoundedWhyCreatesApplicabilityPermission → ⊥
boundedWhyCannotCreateApplicability ()

boundedWhyCannotCreateClaimTruth :
  BoundedWhyCreatesClaimTruthPermission → ⊥
boundedWhyCannotCreateClaimTruth ()

explicitResidualDoesNotAssertFalsehood :
  ExplicitResidualMeansPropositionFalsePermission → ⊥
explicitResidualDoesNotAssertFalsehood ()

------------------------------------------------------------------------
-- Execution/certification coordinates.
------------------------------------------------------------------------

slrTargetOwner : String
slrTargetOwner = "crates/sl-evidence-payment"

postgresLegacyReference : String
postgresLegacyReference =
  "SensibLaw legal_ir.semantic_build/projection/observation/graph_revision"

sourceWritten : Bool
sourceWritten = true

slrRuntimeReceiptObserved : Bool
slrRuntimeReceiptObserved = false

agdaKernelReceiptObserved : Bool
agdaKernelReceiptObserved = false
