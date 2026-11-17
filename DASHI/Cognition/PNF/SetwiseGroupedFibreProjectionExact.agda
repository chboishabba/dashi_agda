module DASHI.Cognition.PNF.SetwiseGroupedFibreProjectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)

------------------------------------------------------------------------
-- Exact grouped-fibre projection economy.
--
-- Runtime motivation (SensibLaw adaptive-block attribution, 2026-08-21):
-- recurrence authority over a parent region was semantically grouped by repeated
-- head symbol, but the physical implementation re-traversed the complete
-- descendant fibre once for every resulting group.  The measured adaptive block
-- exposed the resulting group × descendant amplification.
--
-- The admissible transformation is narrower than "defer hierarchy": if a
-- set-wise implementation materialises exactly the same authority as the
-- candidate-wise implementation, then physical descendant-pass count is not a
-- semantic observable and may be reduced independently.
------------------------------------------------------------------------

record GroupedFibreProjection
  (Input Authority : Set)
  : Set₁ where
  field
    candidateWiseProjection : Input → Authority
    setwiseProjection : Input → Authority

    -- Semantic authority is unchanged by replacing the physical realization.
    projectionExact :
      ∀ input →
      candidateWiseProjection input ≡ setwiseProjection input

    -- Physical receipts remain explicit and are not inferred from semantic
    -- equality.  The old realization may scale with group count; the set-wise
    -- realization records its bounded number of full descendant passes.
    candidateWiseDescendantPasses : Input → Nat
    setwiseDescendantPasses : Input → Nat

open GroupedFibreProjection public

setwiseGroupedProjectionExact :
  ∀ {Input Authority : Set}
    (projection : GroupedFibreProjection Input Authority)
    (input : Input) →
  candidateWiseProjection projection input
    ≡ setwiseProjection projection input
setwiseGroupedProjectionExact projection input =
  projectionExact projection input

------------------------------------------------------------------------
-- Consumer exactness.
------------------------------------------------------------------------

consumerObservationExact :
  ∀ {Input Authority Observation : Set}
    (projection : GroupedFibreProjection Input Authority)
    (observe : Authority → Observation)
    (input : Input) →
  observe (candidateWiseProjection projection input)
    ≡ observe (setwiseProjection projection input)
consumerObservationExact projection observe input
  rewrite projectionExact projection input = refl

------------------------------------------------------------------------
-- Generic delta-fed projection.
--
-- This is the reusable execution owner behind sentence anaphors, transported
-- parent boundaries, occurrence provenance, and other projection relations.
-- ProjectionRelation is relation-valued on purpose.  A runtime may realise it
-- with transition tables, temporary tables, or another set carrier.  The
-- semantic contract sees only the final authority and the affected-key carrier.
------------------------------------------------------------------------

record DeltaFedProjection
  (SourceDelta ProjectionRelation AffectedKeys Authority : Set)
  : Set₁ where
  field
    projectDelta : SourceDelta → ProjectionRelation
    affectedKeys : ProjectionRelation → AffectedKeys

    legacyAuthority : SourceDelta → Authority
    deltaFedAuthority : SourceDelta → Authority

    finalAuthorityExact :
      ∀ delta →
      legacyAuthority delta ≡ deltaFedAuthority delta

    sourceInteriorRescanCount : SourceDelta → Nat
    sourceInteriorRescanCountIsZero :
      ∀ delta → sourceInteriorRescanCount delta ≡ zero

    recursiveSelfUpdateCount : SourceDelta → Nat
    recursiveSelfUpdateCountIsZero :
      ∀ delta → recursiveSelfUpdateCount delta ≡ zero

    perSourceProceduralStatementCount : SourceDelta → Nat
    perSourceProceduralStatementCountIsZero :
      ∀ delta → perSourceProceduralStatementCount delta ≡ zero

open DeltaFedProjection public

deltaFedProjectionConsumerExact :
  ∀ {SourceDelta ProjectionRelation AffectedKeys Authority Observation : Set}
    (projection :
      DeltaFedProjection
        SourceDelta ProjectionRelation AffectedKeys Authority)
    (observe : Authority → Observation)
    (delta : SourceDelta) →
  observe (legacyAuthority projection delta)
    ≡ observe (deltaFedAuthority projection delta)
deltaFedProjectionConsumerExact projection observe delta
  rewrite finalAuthorityExact projection delta = refl

------------------------------------------------------------------------
-- Recurrence specialization contract.
--
-- A recurrence authority has a grouped carrier and a member carrier.  The
-- runtime optimization is valid only when both are preserved exactly.  This
-- prevents a fast implementation from keeping group counts while silently
-- changing group membership or vice versa.
------------------------------------------------------------------------

record RecurrenceAuthority
  (Groups Members : Set)
  : Set where
  field
    groups : Groups
    members : Members

open RecurrenceAuthority public

record ExactRecurrenceGroupedProjection
  (Input Groups Members : Set)
  : Set₁ where
  field
    groupedProjection :
      GroupedFibreProjection Input (RecurrenceAuthority Groups Members)

open ExactRecurrenceGroupedProjection public

recurrenceGroupsExact :
  ∀ {Input Groups Members : Set}
    (projection : ExactRecurrenceGroupedProjection Input Groups Members)
    (input : Input) →
  groups
    (candidateWiseProjection (groupedProjection projection) input)
    ≡ groups
        (setwiseProjection (groupedProjection projection) input)
recurrenceGroupsExact projection input
  rewrite projectionExact (groupedProjection projection) input = refl

recurrenceMembersExact :
  ∀ {Input Groups Members : Set}
    (projection : ExactRecurrenceGroupedProjection Input Groups Members)
    (input : Input) →
  members
    (candidateWiseProjection (groupedProjection projection) input)
    ≡ members
        (setwiseProjection (groupedProjection projection) input)
recurrenceMembersExact projection input
  rewrite projectionExact (groupedProjection projection) input = refl
