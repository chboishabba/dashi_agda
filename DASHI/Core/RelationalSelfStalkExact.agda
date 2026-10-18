module DASHI.Core.RelationalSelfStalkExact where

------------------------------------------------------------------------
-- RELATIONSHIP-INDEXED SELF STALKS
--
-- SOURCE / ATTRIBUTION BOUNDARY
--
-- Andersen--Chen motivate relationship-indexed self-representations and
-- contextual activation.  Lacan motivates a structural distinction between
-- a subject and any self-description.  Neither source claims a mathematical
-- sheaf/stalk construction.  "Stalk", the finite context carrier, authority
-- coordinate and all exact non-collapse boundaries below are DASHI
-- constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.RelationalTrialecticSourceAtlasExact as Sources
import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan

data RelationalContext : Set where
  contextAB : RelationalContext
  contextAC : RelationalContext
  contextBC : RelationalContext
  contextABC : RelationalContext
  contextAlone : RelationalContext

data ResolutionLevel : Set where
  lowResolution : ResolutionLevel
  mediumResolution : ResolutionLevel
  highResolution : ResolutionLevel

data AuthorityLevel : Set where
  lowAuthority : AuthorityLevel
  mediumAuthority : AuthorityLevel
  highAuthority : AuthorityLevel

record SelfStalk (SelfState : Set) : Set where
  constructor self-stalk
  field
    context : RelationalContext
    localSelfRepresentation : SelfState
    representationResolution : ResolutionLevel
    selfAuthority : AuthorityLevel
    provenanceReference : String

open SelfStalk public

record RelationalSelfFamily (SelfState : Set) : Set where
  constructor relational-self-family
  field
    inAB : SelfStalk SelfState
    inAC : SelfStalk SelfState
    inBC : SelfStalk SelfState
    inABC : SelfStalk SelfState
    alone : SelfStalk SelfState

open RelationalSelfFamily public

------------------------------------------------------------------------
-- Subject identity and local self-representation are explicitly separate.
------------------------------------------------------------------------

record SubjectWithRelationalSelf (SelfState : Set) : Set where
  constructor subject-with-relational-self
  field
    subjectReference : String
    stalkFamily : RelationalSelfFamily SelfState
    totalSelfRecoveredFromAnySingleStalk : Bool
    relationshipIndexingMeansMultiplePersons : Bool

open SubjectWithRelationalSelf public

data SingleStalkIsWholeSubject : Set where

singleStalkDoesNotBecomeWholeSubject :
  SingleStalkIsWholeSubject → ⊥
singleStalkDoesNotBecomeWholeSubject ()

------------------------------------------------------------------------
-- Perspective resolution and self-authority are independent coordinates.
------------------------------------------------------------------------

data DemoSelfState : Set where
  sameRepresentedSelf : DemoSelfState

highResolutionLowAuthority : SelfStalk DemoSelfState
highResolutionLowAuthority =
  self-stalk contextAB sameRepresentedSelf highResolution lowAuthority
    "DASHI witness: high representational resolution with low self-authority"

highResolutionHighAuthority : SelfStalk DemoSelfState
highResolutionHighAuthority =
  self-stalk contextAB sameRepresentedSelf highResolution highAuthority
    "DASHI witness: same resolution with different self-authority"

sameRepresentationResolution :
  representationResolution highResolutionLowAuthority
  ≡ representationResolution highResolutionHighAuthority
sameRepresentationResolution = refl

differentSelfAuthority :
  selfAuthority highResolutionLowAuthority
  ≡ selfAuthority highResolutionHighAuthority →
  ⊥
differentSelfAuthority ()

record RelationalSelfStalkBoundary : Set where
  constructor relational-self-stalk-boundary
  field
    selfRepresentationIsWholeSubject : Bool
    relationshipIndexedSelfMeansFragmentedPerson : Bool
    relationshipIndexedSelfIsMathematicalSheafByCitation : Bool
    perspectiveResolutionEqualsSelfAuthority : Bool
    sourceCitationCreatesFormalIdentity : Bool

canonicalRelationalSelfStalkBoundary : RelationalSelfStalkBoundary
canonicalRelationalSelfStalkBoundary =
  relational-self-stalk-boundary false false false false false
