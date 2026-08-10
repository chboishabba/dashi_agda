module DASHI.Cognition.PNF.ReferenceModeOutcomes where

open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.SparseFibredFrontier

------------------------------------------------------------------------
-- Reference mode is semantic evidence carried by the typed demand. Candidate
-- multiplicity alone cannot decide whether several compatible actors are an
-- ambiguity or the intended denotation of a plural reference.
------------------------------------------------------------------------

data ReferenceMode : Set where
  singularReference : ReferenceMode
  pluralReference : ReferenceMode
  genericReference : ReferenceMode
  inapplicableReference : ReferenceMode

------------------------------------------------------------------------
-- Outcome is indexed by both declared reference mode and witnessed candidate
-- multiplicity. Singular references preserve the sparse solver's ordinary
-- unique/ambiguous distinction. Plural and generic references remain distinct
-- non-scalar outcomes.
------------------------------------------------------------------------

data ReferenceOutcome : ReferenceMode → WitnessMultiplicity → Set where
  singularNoWitness :
    ReferenceOutcome singularReference noWitness
  singularResolvedUnique :
    ResolvedTarget →
    ReferenceOutcome singularReference oneWitness
  singularAmbiguous :
    ReferenceOutcome singularReference severalWitnesses

  pluralOneMember :
    ReferenceOutcome pluralReference oneWitness
  pluralSeveralMembers :
    ReferenceOutcome pluralReference severalWitnesses

  genericNoWitness :
    ReferenceOutcome genericReference noWitness
  genericOneWitness :
    ReferenceOutcome genericReference oneWitness
  genericSeveralWitnesses :
    ReferenceOutcome genericReference severalWitnesses

  referenceInapplicable :
    ∀ {multiplicity} →
    ReferenceOutcome inapplicableReference multiplicity

------------------------------------------------------------------------
-- Scalar entity projection is intentionally narrower than successful semantic
-- classification. Only an explicitly singular reference with exactly one
-- witness can carry scalar identity authority.
------------------------------------------------------------------------

data ScalarIdentityPermission :
  ReferenceMode → WitnessMultiplicity → Set where
  singularUniqueMayProjectScalarIdentity :
    ScalarIdentityPermission singularReference oneWitness

pluralOneCannotProjectScalarIdentity :
  ScalarIdentityPermission pluralReference oneWitness → ⊥
pluralOneCannotProjectScalarIdentity ()

pluralSeveralCannotProjectScalarIdentity :
  ScalarIdentityPermission pluralReference severalWitnesses → ⊥
pluralSeveralCannotProjectScalarIdentity ()

genericCannotProjectScalarIdentity :
  ∀ {multiplicity} →
  ScalarIdentityPermission genericReference multiplicity → ⊥
genericCannotProjectScalarIdentity ()

inapplicableCannotProjectScalarIdentity :
  ∀ {multiplicity} →
  ScalarIdentityPermission inapplicableReference multiplicity → ⊥
inapplicableCannotProjectScalarIdentity ()

singularAmbiguityCannotProjectScalarIdentity :
  ScalarIdentityPermission singularReference severalWitnesses → ⊥
singularAmbiguityCannotProjectScalarIdentity ()

singularNoWitnessCannotProjectScalarIdentity :
  ScalarIdentityPermission singularReference noWitness → ⊥
singularNoWitnessCannotProjectScalarIdentity ()

record ReferenceModeBoundary : Set where
  constructor referenceModeBoundary
  field
    singularUniquePermission :
      ScalarIdentityPermission singularReference oneWitness
    singularAmbiguityDenied :
      ScalarIdentityPermission singularReference severalWitnesses → ⊥
    pluralSeveralDenied :
      ScalarIdentityPermission pluralReference severalWitnesses → ⊥
    genericDenied :
      ∀ {multiplicity} →
      ScalarIdentityPermission genericReference multiplicity → ⊥

open ReferenceModeBoundary public

canonicalReferenceModeBoundary : ReferenceModeBoundary
canonicalReferenceModeBoundary =
  referenceModeBoundary
    singularUniqueMayProjectScalarIdentity
    singularAmbiguityCannotProjectScalarIdentity
    pluralSeveralCannotProjectScalarIdentity
    genericCannotProjectScalarIdentity
