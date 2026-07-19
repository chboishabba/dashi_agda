module DASHI.Core.GeneralizedDomainTheory where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.FormalStructureKind
open import DASHI.Core.ProofLens
open import DASHI.Core.IndexedRoleEvidence

-- A domain does not merely have a Hamiltonian or one privileged invariant.  It
-- supplies a role family plus any domain-specific mathematical structures,
-- lenses, evidence discipline, residuals, and governance gates it can justify.
record DomainTheory : Set₁ where
  field
    theoryDomain    : RoleFamily
    theoryLenses    : LensFamily theoryDomain
    theoryEvidence  : EvidenceFamily theoryDomain
    theoryPolicy    : ReceiptPolicy theoryDomain theoryEvidence

    StructureAt : (r : FormalRole) → RoleType theoryDomain r → Set
    structures  : (r : FormalRole) → (x : RoleType theoryDomain r) → StructureAt r x

open DomainTheory public

record ClassifiedTerm (T : DomainTheory) : Set₁ where
  field
    classifiedRole      : FormalRole
    classifiedPayload   : RoleType (theoryDomain T) classifiedRole
    classifiedStructure : StructureAt T classifiedRole classifiedPayload

open ClassifiedTerm public

-- The fully governed object preserves every index used to interpret it.
record GovernedTypedTerm (T : DomainTheory) : Set₁ where
  field
    classified : ClassifiedTerm T
    selectedLens : ProofLens
    lensSupport :
      LensWitness
        (theoryLenses T)
        selectedLens
        (classifiedRole classified)
        (classifiedPayload classified)
    evidenceSupport :
      EvidenceFor
        (theoryEvidence T)
        (classifiedRole classified)
        (classifiedPayload classified)
    residualSupport :
      ResidualFor
        (theoryPolicy T)
        (classifiedRole classified)
        (classifiedPayload classified)
    admissibilitySupport :
      Gate
        (theoryPolicy T)
        (classifiedRole classified)
        (classifiedPayload classified)
        evidenceSupport
        residualSupport

open GovernedTypedTerm public

-- No field provides global truth, a universal Hamiltonian, or a universal
-- invariant.  Those must be supplied inside StructureAt by each domain.
