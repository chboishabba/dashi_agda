module DASHI.Cognition.PNF.BoundedProperNameEvidenceExecution where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.IdentityEvidenceProduction

------------------------------------------------------------------------
-- SensibLaw migration 085 execution contract.
--
-- Proper-name expansion is candidate evidence only. Runtime enumerates a
-- bounded representative target carrier per standalone proper-name mention and
-- records overflow when the family carrier is larger than the execution budget.
-- The semantic possibility count remains the full observed family cardinality;
-- bounded representation never means omitted targets were semantically rejected.
-- A token already embedded in a PERSON span is not a standalone surname source.
------------------------------------------------------------------------

data ProperNameMentionContext : Set where
  standaloneProperName embeddedInPersonSpan : ProperNameMentionContext

data ProperNameExpansionSourcePermission : ProperNameMentionContext → Set where
  standaloneProperNameMayExpand :
    ProperNameExpansionSourcePermission standaloneProperName

embeddedPersonTokenCannotExpand :
  ProperNameExpansionSourcePermission embeddedInPersonSpan → ⊥
embeddedPersonTokenCannotExpand ()

record ProperNameTargetEnumeration : Set where
  constructor properNameTargetEnumeration
  field
    possibleTargetCount : Nat
    retainedTargetCount : Nat
    retainedTargetLimit : Nat
    retainedWithinLimit : retainedTargetCount ≤ᶜ retainedTargetLimit

open ProperNameTargetEnumeration public

record BoundedProperNameCandidate : Set where
  constructor boundedProperNameCandidate
  field
    evidenceKind : ParserIdentityEvidence
    isProperNameExpansion : evidenceKind ≡ properNameExpansion
    sourcePermission :
      ProperNameExpansionSourcePermission standaloneProperName
    targetEnumeration : ProperNameTargetEnumeration

open BoundedProperNameCandidate public

------------------------------------------------------------------------
-- Overflow witnesses incomplete execution enumeration, not a smaller semantic
-- possibility space. There is deliberately no constructor granting identity
-- authority from an overflow receipt.
------------------------------------------------------------------------

data ProperNameEnumerationCoverage : Set where
  completeEnumeration boundedRepresentativeEnumeration :
    ProperNameEnumerationCoverage

record ProperNameOverflowReceipt : Set where
  constructor properNameOverflowReceipt
  field
    enumeration : ProperNameTargetEnumeration
    coverage : ProperNameEnumerationCoverage

data ProperNameOverflowAuthority : Set where
  properNameExecutionEvidenceOnly : ProperNameOverflowAuthority

data ProperNameOverflowIdentityPermission : ProperNameOverflowAuthority → Set where

properNameOverflowCannotAdmitIdentity :
  ProperNameOverflowIdentityPermission properNameExecutionEvidenceOnly → ⊥
properNameOverflowCannotAdmitIdentity ()

open ProperNameOverflowReceipt public

------------------------------------------------------------------------
-- Bounded enumeration does not alter the epistemic rule already formalised in
-- IdentityEvidenceProduction: proper-name expansion cannot bootstrap identity.
-- Admission still requires an independent CorroboratedNameExpansion witness.
------------------------------------------------------------------------

record BoundedProperNameEvidenceBoundary : Set where
  constructor boundedProperNameEvidenceBoundary
  field
    embeddedSourceDenied :
      ProperNameExpansionSourcePermission embeddedInPersonSpan → ⊥
    overflowHasNoIdentityPermission :
      ProperNameOverflowIdentityPermission properNameExecutionEvidenceOnly → ⊥
    nameExpansionStillNeedsCorroboration :
      DirectIdentityEvidencePermission properNameExpansion → ⊥

open BoundedProperNameEvidenceBoundary public

canonicalBoundedProperNameEvidenceBoundary : BoundedProperNameEvidenceBoundary
canonicalBoundedProperNameEvidenceBoundary =
  boundedProperNameEvidenceBoundary
    embeddedPersonTokenCannotExpand
    properNameOverflowCannotAdmitIdentity
    properNameExpansionCannotBootstrapIdentity
