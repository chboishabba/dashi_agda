module DASHI.Cognition.PNF.ChangedInterfaceLookupDeltaExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)

------------------------------------------------------------------------
-- Delta publication after one authoritative full lookup projection.
--
-- The changed-interface certificate says that every interface outside the
-- selected delta has the same source lookup relation before and after the local
-- adjacency phase. Under that premise, replacing only the selected interface
-- fibres is semantically equivalent to another whole-document projection.
------------------------------------------------------------------------

record ChangedInterfaceCertificate (Interface Row : Set) : Set₁ where
  field
    changed : Interface → Set
    unchanged : Interface → Set
    sourceBefore : Interface → Row → Set
    sourceAfter : Interface → Row → Set
    unchangedSourceStable :
      ∀ interface →
      unchanged interface →
      sourceBefore interface ≡ sourceAfter interface

open ChangedInterfaceCertificate public

record DeltaProjectionEquivalence
  (Interface Row Projection : Set)
  (certificate : ChangedInterfaceCertificate Interface Row)
  : Set₁ where
  field
    fullReprojection : Projection
    changedInterfaceProjection : Projection
    semanticEquality : fullReprojection ≡ changedInterfaceProjection

open DeltaProjectionEquivalence public

changedInterfaceRefreshEqualsFullProjection :
  ∀ {Interface Row Projection : Set}
    {certificate : ChangedInterfaceCertificate Interface Row}
    (proof : DeltaProjectionEquivalence Interface Row Projection certificate) →
  fullReprojection proof ≡ changedInterfaceProjection proof
changedInterfaceRefreshEqualsFullProjection proof = semanticEquality proof

------------------------------------------------------------------------
-- Exact count conservation without signed arithmetic.
--
-- The runtime SQL returns inserted - deleted. Constructively the invariant is
-- better stated as final + deleted = base + inserted.
------------------------------------------------------------------------

record LookupRowCountConservation : Set where
  field
    baseCount : Nat
    insertedCount : Nat
    deletedCount : Nat
    finalCount : Nat
    conserved :
      (finalCount + deletedCount) ≡ (baseCount + insertedCount)

open LookupRowCountConservation public

lookupRowCountConservationExact :
  (proof : LookupRowCountConservation) →
  (finalCount proof + deletedCount proof)
  ≡
  (baseCount proof + insertedCount proof)
lookupRowCountConservationExact proof = conserved proof
