module DASHI.Cognition.PNF.InductiveDemandPreference where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.DemandResolutionState as Demand
import DASHI.Cognition.PNF.ReferenceModeOutcomes as Reference

------------------------------------------------------------------------
-- Inductive preference is a ranking over an unresolved candidate fibre.
--
-- Human/coreference reasoning can favour one interpretation because it best
-- fits discourse, temporal and relational context without possessing a unique
-- deductive witness.  The existing DemandState already keeps candidate rows
-- open; this module adds an explicit preference receipt while reusing that
-- unresolved state rather than inventing a second resolution status machine.
------------------------------------------------------------------------

record InductivePreference : Set where
  constructor inductivePreference
  field
    preferredCandidate : Demand.CandidateEvidence
    evidenceMargin : Nat
    evidenceCoverage : Nat

open InductivePreference public

inductivePreferenceKeepsDemandOpen :
  InductivePreference → Demand.DemandState Demand.openDemand
inductivePreferenceKeepsDemandOpen preference =
  Demand.candidateDoesNotResolve (preferredCandidate preference)

------------------------------------------------------------------------
-- Preference has no scalar identity authority.  A singular identity still
-- requires the existing singularReference × oneWitness permission path.
------------------------------------------------------------------------

data InductiveScalarIdentityPermission : Set where

inductivePreferenceCannotProjectScalarIdentity :
  InductiveScalarIdentityPermission → ⊥
inductivePreferenceCannotProjectScalarIdentity ()

existingDeductivePermission :
  Reference.ScalarIdentityPermission
    Reference.singularReference
    DASHI.Cognition.PNF.SparseFibredFrontier.oneWitness
existingDeductivePermission =
  Reference.singularUniqueMayProjectScalarIdentity

record InductivePreferenceBoundary : Set where
  constructor inductivePreferenceBoundary
  field
    preferredCandidateKeepsDemandOpen :
      InductivePreference → Demand.DemandState Demand.openDemand
    preferenceIsNotDeductiveIdentity :
      InductiveScalarIdentityPermission → ⊥
    rankingCanExistWithoutResolution : Bool
    rankingCanExistWithoutResolutionIsTrue :
      rankingCanExistWithoutResolution ≡ true

open InductivePreferenceBoundary public

canonicalInductivePreferenceBoundary : InductivePreferenceBoundary
canonicalInductivePreferenceBoundary =
  inductivePreferenceBoundary
    inductivePreferenceKeepsDemandOpen
    inductivePreferenceCannotProjectScalarIdentity
    true refl
