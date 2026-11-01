module DASHI.Cognition.PNF.SetwiseGroupedFibreProjectionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Cognition.PNF.SetwiseGroupedFibreProjectionExact

------------------------------------------------------------------------
-- Finite witness: four recurrence groups over one descendant fibre.
------------------------------------------------------------------------

data TinyInput : Set where
  adaptive : TinyInput

data TinyGroups : Set where
  fourGroups : TinyGroups

data TinyMembers : Set where
  exactMembers : TinyMembers

canonicalAuthority : RecurrenceAuthority TinyGroups TinyMembers
canonicalAuthority = record
  { groups = fourGroups
  ; members = exactMembers
  }

candidateWise : TinyInput → RecurrenceAuthority TinyGroups TinyMembers
candidateWise adaptive = canonicalAuthority

setwise : TinyInput → RecurrenceAuthority TinyGroups TinyMembers
setwise adaptive = canonicalAuthority

candidatePasses : TinyInput → Nat
candidatePasses adaptive = 4

setwisePasses : TinyInput → Nat
setwisePasses adaptive = 2

projection :
  GroupedFibreProjection
    TinyInput
    (RecurrenceAuthority TinyGroups TinyMembers)
projection = record
  { candidateWiseProjection = candidateWise
  ; setwiseProjection = setwise
  ; projectionExact = λ { adaptive → refl }
  ; candidateWiseDescendantPasses = candidatePasses
  ; setwiseDescendantPasses = setwisePasses
  }

recurrenceProjection :
  ExactRecurrenceGroupedProjection TinyInput TinyGroups TinyMembers
recurrenceProjection = record
  { groupedProjection = projection
  }

semanticAuthorityPreserved :
  candidateWise adaptive ≡ setwise adaptive
semanticAuthorityPreserved =
  setwiseGroupedProjectionExact projection adaptive

groupAuthorityPreserved :
  groups (candidateWise adaptive) ≡ groups (setwise adaptive)
groupAuthorityPreserved =
  recurrenceGroupsExact recurrenceProjection adaptive

memberAuthorityPreserved :
  members (candidateWise adaptive) ≡ members (setwise adaptive)
memberAuthorityPreserved =
  recurrenceMembersExact recurrenceProjection adaptive

candidateWiseRescansPerGroup :
  candidateWiseDescendantPasses projection adaptive ≡ 4
candidateWiseRescansPerGroup = refl

setwiseUsesBoundedPasses :
  setwiseDescendantPasses projection adaptive ≡ 2
setwiseUsesBoundedPasses = refl
