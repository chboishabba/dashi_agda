module DASHI.Culture.DialecticalMaterialismObserverRevisionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.DialecticalMaterialRevisionExact as Revision
import DASHI.Core.DialecticalMaterialFutureSafetyExact as Future
import DASHI.Core.ContextualDialecticRoleExact as Role
import DASHI.Culture.MarxLabourUnionSourceBoundaryExact as Marx
import DASHI.Culture.HistoricalTotalityCriticalTheoryCrossPollinationExact as Totality

------------------------------------------------------------------------
-- SOURCE / FORMALISATION BOUNDARY
--
-- Marx and the historical-totality lane supply bounded source context.  The
-- append-only revision, observer collision and future-safety theorems are DASHI
-- constructions.  Shared structural usefulness does not transfer authorship.
------------------------------------------------------------------------

record DialecticalMaterialismObserverRevisionBoundary : Set where
  constructor dialectical-materialism-observer-revision-boundary
  field
    marxSourceBoundary : Marx.MarxLabourUnionSourceBoundary
    materialRevisionBoundary : Revision.DialecticalMaterialRevisionBoundary
    futureSafetyBoundary : Future.DialecticalMaterialFutureSafetyBoundary
    contextualRoleBoundary : Role.ContextualDialecticRoleBoundary
    appendOnlyRevisionIsLiteralMarxTheorem : Bool
    consumerFibreAdequacyIsLiteralMarxTheorem : Bool
    contradictionMeansLogicalNegationOnly : Bool
    changedMaterialConditionsMayRequireReopeningCurrentInterpretation : Bool
    retainedHistoricalEvidenceMayCoexistWithRevisedCurrentConclusion : Bool
    sameFormalPatternImpliesSameHistoricalMechanism : Bool

canonicalDialecticalMaterialismObserverRevisionBoundary :
  DialecticalMaterialismObserverRevisionBoundary
canonicalDialecticalMaterialismObserverRevisionBoundary =
  dialectical-materialism-observer-revision-boundary
    Marx.canonicalMarxLabourUnionSourceBoundary
    Revision.canonicalDialecticalMaterialRevisionBoundary
    Future.canonicalDialecticalMaterialFutureSafetyBoundary
    Role.canonicalContextualDialecticRoleBoundary
    false false false true true false

-- The historical-totality owner remains independently available; importing it
-- here is an explicit x-pollination edge, not an identification of theories.
historicalTotalityCrossPollinationAvailable : Bool
historicalTotalityCrossPollinationAvailable = true
