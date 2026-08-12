module DASHI.Core.ProvenanceBearingQuotient where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.FibreRestrictionCore as Fibre

------------------------------------------------------------------------
-- Canonical provenance-bearing quotient.
--
-- FibreRestrictionCore already owns the fine carrier, coarse surface and
-- evidence-restriction boundary.  This record adds exactly the datum required
-- to make a projection reopenable: an application-supplied receipt and a
-- reconstruction map.  The receipt is provenance/residual state, not semantic
-- authority.
------------------------------------------------------------------------

record ProvenanceBearingQuotient
    (core : Fibre.FibreRestrictionCore) : Set₁ where
  constructor provenanceBearingQuotient
  field
    Receipt : Set
    receipt : Fibre.Carrier core → Receipt
    reopen : Fibre.Surface core → Receipt → Fibre.Carrier core
    reopenExact :
      (x : Fibre.Carrier core) →
      reopen (Fibre.project core x) (receipt x) ≡ x

open ProvenanceBearingQuotient public

------------------------------------------------------------------------
-- Some consumers only require reconstruction up to a declared relevant
-- equivalence.  That weaker contract is explicit rather than silently
-- replacing exact reconstruction.
------------------------------------------------------------------------

record RelevantProvenanceBearingQuotient
    (core : Fibre.FibreRestrictionCore)
    (Relevant : Fibre.Carrier core → Fibre.Carrier core → Set) : Set₁ where
  constructor relevantProvenanceBearingQuotient
  field
    Receipt : Set
    receipt : Fibre.Carrier core → Receipt
    reopen : Fibre.Surface core → Receipt → Fibre.Carrier core
    reopenRelevant :
      (x : Fibre.Carrier core) →
      Relevant (reopen (Fibre.project core x) (receipt x)) x

open RelevantProvenanceBearingQuotient public

equalityRelevantQuotient :
  ∀ {core} →
  ProvenanceBearingQuotient core →
  RelevantProvenanceBearingQuotient core _≡_
equalityRelevantQuotient quotient =
  relevantProvenanceBearingQuotient
    (ProvenanceBearingQuotient.Receipt quotient)
    (ProvenanceBearingQuotient.receipt quotient)
    (ProvenanceBearingQuotient.reopen quotient)
    (ProvenanceBearingQuotient.reopenExact quotient)

------------------------------------------------------------------------
-- Authority boundary.
--
-- Projecting a distinction away does not prove that distinction false.  A
-- consumer may discard a coordinate operationally only under an independent
-- safety/congruence theorem.
------------------------------------------------------------------------

data ProjectionErasureAuthority : Set where
  projectionReceiptOnly : ProjectionErasureAuthority

data ProjectionSemanticErasurePermission : ProjectionErasureAuthority → Set where

projectionReceiptCannotEraseSemantics :
  ProjectionSemanticErasurePermission projectionReceiptOnly → ⊥
projectionReceiptCannotEraseSemantics ()

record ProvenanceBearingQuotientBoundary : Set where
  constructor provenanceBearingQuotientBoundary
  field
    projectionEqualsErasure : Bool
    projectionEqualsErasureIsFalse : projectionEqualsErasure ≡ false
    residualReceiptPromotesTruth : Bool
    residualReceiptPromotesTruthIsFalse : residualReceiptPromotesTruth ≡ false
    exactReopeningAvailableWhenSupplied : Bool
    exactReopeningAvailableWhenSuppliedIsTrue :
      exactReopeningAvailableWhenSupplied ≡ true
    projectionAloneCannotEraseSemantics :
      ProjectionSemanticErasurePermission projectionReceiptOnly → ⊥

open ProvenanceBearingQuotientBoundary public

canonicalProvenanceBearingQuotientBoundary : ProvenanceBearingQuotientBoundary
canonicalProvenanceBearingQuotientBoundary =
  provenanceBearingQuotientBoundary
    false refl
    false refl
    true refl
    projectionReceiptCannotEraseSemantics
