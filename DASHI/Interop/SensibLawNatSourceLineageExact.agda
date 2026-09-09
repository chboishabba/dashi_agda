module DASHI.Interop.SensibLawNatSourceLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawNatSourceDiscoveryExact as Discovery

------------------------------------------------------------------------
-- SOURCE LINEAGE IS ORTHOGONAL TO SAME-SOURCE IDENTITY
--
-- A candidate may fail the exact same-source identity question while still
-- being a useful source-of-source or sibling that sharpens subsequent
-- discovery.  Such lineage never admits the candidate into alternate fetch.
------------------------------------------------------------------------

data SourceLineageRelation : Set where
  sameSourceRelation : SourceLineageRelation
  sourceOfSource : SourceLineageRelation
  siblingSource : SourceLineageRelation
  unrelatedSource : SourceLineageRelation
  lineageUnresolved : SourceLineageRelation

record SourceLineageReceipt
    {residual : _}
    {demand : _}
    {candidate : _}
    (identity : Discovery.SameSourceIdentityReceipt candidate) : Set where
  constructor sourceLineageReceipt
  field
    relation : SourceLineageRelation
    lineageEvidenceLocator : String
    derivedQueryHintReference : String
    alternateFetchAdmitted : Bool
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
    authorityEvaluated : Bool
    authorityEvaluatedIsFalse : authorityEvaluated ≡ false
open SourceLineageReceipt public

-- A source-of-source is explicitly not an alternate realization of the exact
-- historical source, even though it may produce better discovery queries.
canonicalSourceOfSourceReceipt :
  {residual : _} →
  {demand : _} →
  {candidate : _} →
  (identity : Discovery.SameSourceIdentityReceipt candidate) →
  Discovery.disposition identity ≡ Discovery.differentSource →
  String →
  String →
  SourceLineageReceipt identity
canonicalSourceOfSourceReceipt identity refl evidence queryHint =
  sourceLineageReceipt
    sourceOfSource
    evidence
    queryHint
    false
    false
    refl
    false
    refl

data SourceOfSourcePaysSameSourceIdentity : Set where
data SourceOfSourceMayReenterAlternateFetch : Set where
data SourceLineagePaysSourceSupport : Set where

sourceOfSourceDoesNotPaySameSourceIdentity :
  SourceOfSourcePaysSameSourceIdentity → ⊥
sourceOfSourceDoesNotPaySameSourceIdentity ()

sourceOfSourceDoesNotReenterAlternateFetch :
  SourceOfSourceMayReenterAlternateFetch → ⊥
sourceOfSourceDoesNotReenterAlternateFetch ()

sourceLineageDoesNotPaySourceSupport : SourceLineagePaysSourceSupport → ⊥
sourceLineageDoesNotPaySourceSupport ()

record NatSourceLineageBoundary : Set where
  constructor nat-source-lineage-boundary
  field
    differentSourceMayStillCarryUsefulLineage : Bool
    sourceOfSourcePaysSameSourceIdentity : Bool
    sourceOfSourceMayReenterAlternateFetch : Bool
    sourceLineageMayRefineDiscoveryQueries : Bool
    sourceLineagePaysSourceSupport : Bool

canonicalNatSourceLineageBoundary : NatSourceLineageBoundary
canonicalNatSourceLineageBoundary =
  nat-source-lineage-boundary true false false true false
