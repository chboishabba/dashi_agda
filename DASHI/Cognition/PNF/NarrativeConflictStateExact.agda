module DASHI.Cognition.PNF.NarrativeConflictStateExact where

------------------------------------------------------------------------
-- NARRATIVE CONFLICT STATE / HIDDEN-FIBRE RECONSTRUCTION
--
-- Direct formalization of the E/P/R/Q/K/I/A decomposition used in the
-- Kendrick/Drake analysis:
--
--   E : underlying event/history
--   P : public claims/projection
--   R : opponent response
--   Q : unresolved/private residual
--   K : audience classification
--   I : institutional classification
--   A : later action licensed by K/I
--
-- The key boundary is that a rhetorically persuasive reconstruction of Q is
-- still only a candidate fine state until supplied with a verification witness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record NarrativeConflictState
    (Event PublicClaim Response Residual AudienceClass InstitutionalClass Action : Set) : Set₁ where
  constructor narrativeConflictState
  field
    event : Event
    publicClaim : PublicClaim
    response : Response
    residual : Residual
    audienceClass : AudienceClass
    institutionalClass : InstitutionalClass
    action : Action

open NarrativeConflictState public

------------------------------------------------------------------------
-- Audience and institutional updates do not rewrite the underlying event or
-- unresolved residual by construction.
------------------------------------------------------------------------

updateAudience :
  ∀ {E P R Q K I A} → K → NarrativeConflictState E P R Q K I A →
  NarrativeConflictState E P R Q K I A
updateAudience new (narrativeConflictState e p r q old i a) =
  narrativeConflictState e p r q new i a

updateInstitution :
  ∀ {E P R Q K I A} → I → NarrativeConflictState E P R Q K I A →
  NarrativeConflictState E P R Q K I A
updateInstitution new (narrativeConflictState e p r q k old a) =
  narrativeConflictState e p r q k new a

audienceUpdatePreservesEvent :
  ∀ {E P R Q K I A}
    (new : K) (state : NarrativeConflictState E P R Q K I A) →
  event (updateAudience new state) ≡ event state
audienceUpdatePreservesEvent new state = refl

audienceUpdatePreservesResidual :
  ∀ {E P R Q K I A}
    (new : K) (state : NarrativeConflictState E P R Q K I A) →
  residual (updateAudience new state) ≡ residual state
audienceUpdatePreservesResidual new state = refl

institutionUpdatePreservesEvent :
  ∀ {E P R Q K I A}
    (new : I) (state : NarrativeConflictState E P R Q K I A) →
  event (updateInstitution new state) ≡ event state
institutionUpdatePreservesEvent new state = refl

institutionUpdatePreservesResidual :
  ∀ {E P R Q K I A}
    (new : I) (state : NarrativeConflictState E P R Q K I A) →
  residual (updateInstitution new state) ≡ residual state
institutionUpdatePreservesResidual new state = refl

------------------------------------------------------------------------
-- Reconstruction claims over a hidden fibre.
------------------------------------------------------------------------

record RhetoricalReconstruction
    (Fine Public : Set)
    (project : Fine → Public)
    (visible : Public) : Set₁ where
  constructor rhetoricalReconstruction
  field
    candidate : Fine
    candidateMatchesVisible : project candidate ≡ visible

open RhetoricalReconstruction public

record VerifiedReconstruction
    (Fine Public : Set)
    (project : Fine → Public)
    (actual : Fine) : Set₁ where
  constructor verifiedReconstruction
  field
    rhetorical : RhetoricalReconstruction Fine Public project (project actual)
    verifiesActual : candidate rhetorical ≡ actual

open VerifiedReconstruction public

------------------------------------------------------------------------
-- Finite witness: the same public persona can have distinct fine states.
------------------------------------------------------------------------

data FinePersona : Set where
  fineA fineB : FinePersona

data PublicPersona : Set where
  samePublic : PublicPersona

personaProjection : FinePersona → PublicPersona
personaProjection fineA = samePublic
personaProjection fineB = samePublic

samePublicProjection :
  personaProjection fineA ≡ personaProjection fineB
samePublicProjection = refl

distinctFinePersonae : fineA ≡ fineB → ⊥
distinctFinePersonae ()

reconstructionA reconstructionB :
  RhetoricalReconstruction FinePersona PublicPersona personaProjection samePublic
reconstructionA = rhetoricalReconstruction fineA refl
reconstructionB = rhetoricalReconstruction fineB refl

sameProjectionDoesNotChooseReconstruction :
  candidate reconstructionA ≡ candidate reconstructionB → ⊥
sameProjectionDoesNotChooseReconstruction = distinctFinePersonae

------------------------------------------------------------------------
-- Therefore "public P differs from hidden Q" is a hypothesis family until a
-- provenance/evidence witness selects a representative.  Rhetorical force is
-- not encoded as reconstruction verification.
------------------------------------------------------------------------
