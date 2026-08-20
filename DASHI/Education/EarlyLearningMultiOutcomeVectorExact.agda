module DASHI.Education.EarlyLearningMultiOutcomeVectorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection

------------------------------------------------------------------------
-- MULTI-OUTCOME POLICY EVIDENCE
--
-- Child development, caregiver labour, caregiver well-being, fiscal effects
-- and entitlement are separate evidence axes.  A positive signal on one axis
-- does not mathematically reconstruct the others.
------------------------------------------------------------------------

data EvidenceDirection : Set where
  adverseSignal unresolvedSignal beneficialSignal : EvidenceDirection

data EntitlementState : Set where
  entitlementAbsent entitlementRetained : EntitlementState

record EarlyLearningOutcomeVector : Set where
  constructor earlyLearningOutcomeVector
  field
    childDevelopment : EvidenceDirection
    caregiverLabour : EvidenceDirection
    caregiverWellbeing : EvidenceDirection
    fiscalBalance : EvidenceDirection
    entitlement : EntitlementState

open EarlyLearningOutcomeVector public

------------------------------------------------------------------------
-- Finite source-shaped witnesses.
--
-- These are not a pooled meta-analysis.  They encode the logical fact exposed
-- by the Quebec literature that maternal labour gains can coexist with adverse
-- measured child/family signals, while later fiscal evidence can change without
-- erasing the distinct child-outcome evidence surface.
------------------------------------------------------------------------

mixedQuebecEvidence : EarlyLearningOutcomeVector
mixedQuebecEvidence =
  earlyLearningOutcomeVector
    adverseSignal
    beneficialSignal
    adverseSignal
    unresolvedSignal
    entitlementRetained

updatedFiscalQuebecEvidence : EarlyLearningOutcomeVector
updatedFiscalQuebecEvidence =
  earlyLearningOutcomeVector
    adverseSignal
    beneficialSignal
    unresolvedSignal
    beneficialSignal
    entitlementRetained

labourProjection : EarlyLearningOutcomeVector → EvidenceDirection
labourProjection = caregiverLabour

childProjection : EarlyLearningOutcomeVector → EvidenceDirection
childProjection = childDevelopment

fiscalProjection : EarlyLearningOutcomeVector → EvidenceDirection
fiscalProjection = fiscalBalance

------------------------------------------------------------------------
-- Labour improvement alone cannot determine the child-development axis.
------------------------------------------------------------------------

data LabourMatchedCase : Set where
  labourGainChildAdverse labourGainChildBeneficial : LabourMatchedCase

labourMatchedProjection : LabourMatchedCase → EvidenceDirection
labourMatchedProjection labourGainChildAdverse = beneficialSignal
labourMatchedProjection labourGainChildBeneficial = beneficialSignal

childSignalAt : LabourMatchedCase → EvidenceDirection
childSignalAt labourGainChildAdverse = adverseSignal
childSignalAt labourGainChildBeneficial = beneficialSignal

childSignalsDiffer :
  childSignalAt labourGainChildAdverse ≡
  childSignalAt labourGainChildBeneficial → ⊥
childSignalsDiffer ()

labourGainCannotDetermineChildEffect :
  Intersection.FactorsThrough labourMatchedProjection childSignalAt → ⊥
labourGainCannotDetermineChildEffect =
  Intersection.witnessRulesOutEveryFlatFactorisation
    (Intersection.nonFactorabilityWitness
      labourGainChildAdverse
      labourGainChildBeneficial
      refl
      childSignalsDiffer)

------------------------------------------------------------------------
-- Likewise one retained child signal cannot determine the fiscal axis.
------------------------------------------------------------------------

data SameChildDifferentFiscal : Set where
  adverseChildFiscalUnknown adverseChildFiscalPositive : SameChildDifferentFiscal

sameChildProjection : SameChildDifferentFiscal → EvidenceDirection
sameChildProjection adverseChildFiscalUnknown = adverseSignal
sameChildProjection adverseChildFiscalPositive = adverseSignal

fiscalSignalAt : SameChildDifferentFiscal → EvidenceDirection
fiscalSignalAt adverseChildFiscalUnknown = unresolvedSignal
fiscalSignalAt adverseChildFiscalPositive = beneficialSignal

fiscalSignalsDiffer :
  fiscalSignalAt adverseChildFiscalUnknown ≡
  fiscalSignalAt adverseChildFiscalPositive → ⊥
fiscalSignalsDiffer ()

childSignalCannotDetermineFiscalEffect :
  Intersection.FactorsThrough sameChildProjection fiscalSignalAt → ⊥
childSignalCannotDetermineFiscalEffect =
  Intersection.witnessRulesOutEveryFlatFactorisation
    (Intersection.nonFactorabilityWitness
      adverseChildFiscalUnknown
      adverseChildFiscalPositive
      refl
      fiscalSignalsDiffer)

------------------------------------------------------------------------
-- A whole-policy verdict therefore requires an explicit normative aggregation
-- rule.  The repository deliberately supplies no privileged constructor from
-- any single evidence axis to such a verdict.
------------------------------------------------------------------------

data WholePolicyVerdict : Set where
  rejectPolicy revisePolicy supportPolicy : WholePolicyVerdict

record ExplicitAggregationRule : Set₁ where
  constructor explicitAggregationRule
  field
    aggregate : EarlyLearningOutcomeVector → WholePolicyVerdict

open ExplicitAggregationRule public

data SingleAxisWholeVerdictAuthority : Set where

singleAxisCannotAutoPromoteToWholeVerdict :
  SingleAxisWholeVerdictAuthority → ⊥
singleAxisCannotAutoPromoteToWholeVerdict ()

record MultiOutcomeBoundary : Set where
  constructor multiOutcomeBoundary
  field
    labourGainDeterminesChildOutcome : Bool
    labourGainDeterminesChildOutcomeIsFalse : labourGainDeterminesChildOutcome ≡ false
    childOutcomeDeterminesFiscalBalance : Bool
    childOutcomeDeterminesFiscalBalanceIsFalse : childOutcomeDeterminesFiscalBalance ≡ false
    wholeVerdictRequiresExplicitAggregation : Bool
    wholeVerdictRequiresExplicitAggregationIsTrue :
      wholeVerdictRequiresExplicitAggregation ≡ true

canonicalMultiOutcomeBoundary : MultiOutcomeBoundary
canonicalMultiOutcomeBoundary =
  multiOutcomeBoundary false refl false refl true refl
