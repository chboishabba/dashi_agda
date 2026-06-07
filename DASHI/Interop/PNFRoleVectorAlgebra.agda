module DASHI.Interop.PNFRoleVectorAlgebra where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Slotwise role algebra for parser/legal observations.
--
-- The older PredicatePNF mirror deliberately treated opaque role arguments as
-- comparable by shape.  This module separates the reducer algebra needed for
-- legal/spaCy decomposition: observations project into named role slots, role
-- slots meet slotwise, and explicit conflict markers force contradiction.
--
-- String comparison is intentionally not proved here.  A runtime reducer may
-- normalize two observed strings into `conflictingRole`; once it does, the
-- algebra below proves the residual consequence.

data RoleSlot : Set where
  subjectRole : RoleSlot
  actionRole : RoleSlot
  objectRole : RoleSlot
  argumentRole : RoleSlot
  conditionRole : RoleSlot
  referenceRole : RoleSlot

data RoleValue : Set where
  absentRole : RoleValue
  observedRole : String → RoleValue
  conflictingRole : RoleValue

meetRoleValue : RoleValue → RoleValue → Residual.ResidualLevel
meetRoleValue absentRole absentRole =
  Residual.exact
meetRoleValue absentRole (observedRole _) =
  Residual.exact
meetRoleValue absentRole conflictingRole =
  Residual.contradiction
meetRoleValue (observedRole _) absentRole =
  Residual.partial
meetRoleValue (observedRole _) (observedRole _) =
  Residual.exact
meetRoleValue (observedRole _) conflictingRole =
  Residual.contradiction
meetRoleValue conflictingRole _ =
  Residual.contradiction

absentRequestedRoleIsPartial :
  ∀ q →
  meetRoleValue (observedRole q) absentRole ≡ Residual.partial
absentRequestedRoleIsPartial q = refl

sameObservedRoleIsExact :
  ∀ v →
  meetRoleValue (observedRole v) (observedRole v) ≡ Residual.exact
sameObservedRoleIsExact v = refl

conflictingRoleIsContradictionLeft :
  ∀ evidence →
  meetRoleValue conflictingRole evidence ≡ Residual.contradiction
conflictingRoleIsContradictionLeft absentRole = refl
conflictingRoleIsContradictionLeft (observedRole _) = refl
conflictingRoleIsContradictionLeft conflictingRole = refl

conflictingObservedRoleIsContradiction :
  ∀ q →
  meetRoleValue (observedRole q) conflictingRole ≡ Residual.contradiction
conflictingObservedRoleIsContradiction q = refl

record RoleVector : Set where
  constructor roleVector
  field
    subject : RoleValue
    action : RoleValue
    object : RoleValue
    argument : RoleValue
    condition : RoleValue
    reference : RoleValue

open RoleVector public

emptyRoleVector : RoleVector
emptyRoleVector =
  roleVector
    absentRole
    absentRole
    absentRole
    absentRole
    absentRole
    absentRole

meetRoleVector : RoleVector → RoleVector → Residual.ResidualLevel
meetRoleVector query evidence =
  Residual.joinResidual
    (meetRoleValue (subject query) (subject evidence))
    (Residual.joinResidual
      (meetRoleValue (action query) (action evidence))
      (Residual.joinResidual
        (meetRoleValue (object query) (object evidence))
        (Residual.joinResidual
          (meetRoleValue (argument query) (argument evidence))
          (Residual.joinResidual
            (meetRoleValue (condition query) (condition evidence))
            (meetRoleValue (reference query) (reference evidence))))))

data StableRoleValue : RoleValue → Set where
  absentStable : StableRoleValue absentRole
  observedStable : ∀ value → StableRoleValue (observedRole value)

stableRoleValueSelfExact :
  ∀ value →
  StableRoleValue value →
  meetRoleValue value value ≡ Residual.exact
stableRoleValueSelfExact absentRole absentStable = refl
stableRoleValueSelfExact (observedRole value) (observedStable value) = refl

record StableRoleVector (vector : RoleVector) : Set where
  constructor stableRoleVector
  field
    subjectStable : StableRoleValue (subject vector)
    actionStable : StableRoleValue (action vector)
    objectStable : StableRoleValue (object vector)
    argumentStable : StableRoleValue (argument vector)
    conditionStable : StableRoleValue (condition vector)
    referenceStable : StableRoleValue (reference vector)

roleVectorAllRequestedSlotsExactIsExact :
  ∀ vector →
  StableRoleVector vector →
  meetRoleVector vector vector ≡ Residual.exact
roleVectorAllRequestedSlotsExactIsExact
  (roleVector subject action object argument condition reference)
  (stableRoleVector
    subjectStable
    actionStable
    objectStable
    argumentStable
    conditionStable
    referenceStable)
  rewrite stableRoleValueSelfExact subject subjectStable
        | stableRoleValueSelfExact action actionStable
        | stableRoleValueSelfExact object objectStable
        | stableRoleValueSelfExact argument argumentStable
        | stableRoleValueSelfExact condition conditionStable
        | stableRoleValueSelfExact reference referenceStable =
  refl

roleVectorMissingRequestedSubjectIsPartial :
  ∀ action object argument condition reference →
  StableRoleValue action →
  StableRoleValue object →
  StableRoleValue argument →
  StableRoleValue condition →
  StableRoleValue reference →
  meetRoleVector
    (roleVector
      (observedRole "requested-subject")
      action
      object
      argument
      condition
      reference)
    (roleVector absentRole action object argument condition reference)
  ≡
  Residual.partial
roleVectorMissingRequestedSubjectIsPartial
  action object argument condition reference
  actionStable objectStable argumentStable conditionStable referenceStable
  rewrite stableRoleValueSelfExact action actionStable
        | stableRoleValueSelfExact object objectStable
        | stableRoleValueSelfExact argument argumentStable
        | stableRoleValueSelfExact condition conditionStable
        | stableRoleValueSelfExact reference referenceStable =
  refl

roleVectorSubjectConflictIsContradiction :
  ∀ querySubject action object argument condition reference →
  meetRoleVector
    (roleVector querySubject action object argument condition reference)
    (roleVector conflictingRole action object argument condition reference)
  ≡
  Residual.contradiction
roleVectorSubjectConflictIsContradiction absentRole _ _ _ _ _ = refl
roleVectorSubjectConflictIsContradiction (observedRole _) _ _ _ _ _ = refl
roleVectorSubjectConflictIsContradiction conflictingRole _ _ _ _ _ = refl

roleVectorResidualJoinPreserved :
  ∀ query evidence →
  meetRoleVector query evidence
  ≡
  Residual.joinResidual
    (meetRoleValue (subject query) (subject evidence))
    (Residual.joinResidual
      (meetRoleValue (action query) (action evidence))
      (Residual.joinResidual
        (meetRoleValue (object query) (object evidence))
        (Residual.joinResidual
          (meetRoleValue (argument query) (argument evidence))
          (Residual.joinResidual
            (meetRoleValue (condition query) (condition evidence))
            (meetRoleValue (reference query) (reference evidence))))))
roleVectorResidualJoinPreserved query evidence = refl

------------------------------------------------------------------------
-- Reduced parser/legal observation vocabulary.

data ParserObservationKind : Set where
  rootVerb : ParserObservationKind
  subjectDep : ParserObservationKind
  objectDep : ParserObservationKind
  negationDep : ParserObservationKind
  auxDep : ParserObservationKind
  modifierDep : ParserObservationKind
  conditionToken : ParserObservationKind
  referenceToken : ParserObservationKind
  junkToken : ParserObservationKind

data ProjectionTarget : Set where
  predicateTarget : ProjectionTarget
  subjectTarget : ProjectionTarget
  actionTarget : ProjectionTarget
  objectTarget : ProjectionTarget
  qualifierTarget : ProjectionTarget
  modifierDiagnosticTarget : ProjectionTarget
  provenanceTarget : ProjectionTarget
  droppedTarget : ProjectionTarget

projectionTargets : ParserObservationKind → List ProjectionTarget
projectionTargets rootVerb =
  predicateTarget ∷ actionTarget ∷ provenanceTarget ∷ []
projectionTargets subjectDep =
  subjectTarget ∷ provenanceTarget ∷ []
projectionTargets objectDep =
  objectTarget ∷ provenanceTarget ∷ []
projectionTargets negationDep =
  qualifierTarget ∷ provenanceTarget ∷ []
projectionTargets auxDep =
  qualifierTarget ∷ modifierDiagnosticTarget ∷ provenanceTarget ∷ []
projectionTargets modifierDep =
  modifierDiagnosticTarget ∷ provenanceTarget ∷ []
projectionTargets conditionToken =
  qualifierTarget ∷ provenanceTarget ∷ []
projectionTargets referenceToken =
  provenanceTarget ∷ []
projectionTargets junkToken =
  droppedTarget ∷ []

rootVerbProjectsToPredicateAndAction :
  projectionTargets rootVerb
  ≡
  predicateTarget ∷ actionTarget ∷ provenanceTarget ∷ []
rootVerbProjectsToPredicateAndAction = refl

subjectDepProjectsToSubjectRole :
  projectionTargets subjectDep
  ≡
  subjectTarget ∷ provenanceTarget ∷ []
subjectDepProjectsToSubjectRole = refl

objectDepProjectsToObjectRole :
  projectionTargets objectDep
  ≡
  objectTarget ∷ provenanceTarget ∷ []
objectDepProjectsToObjectRole = refl

negationProjectsToNegativeQualifier :
  projectionTargets negationDep
  ≡
  qualifierTarget ∷ provenanceTarget ∷ []
negationProjectsToNegativeQualifier = refl

modifierProjectsOnlyToDiagnostic :
  projectionTargets modifierDep
  ≡
  modifierDiagnosticTarget ∷ provenanceTarget ∷ []
modifierProjectsOnlyToDiagnostic = refl

junkIsDroppedOrDiagnostic :
  projectionTargets junkToken ≡ droppedTarget ∷ []
junkIsDroppedOrDiagnostic = refl

promotesLegalAuthority : ParserObservationKind → Bool
promotesLegalAuthority _ = false

grantsLiveWikidataEditAuthority : ParserObservationKind → Bool
grantsLiveWikidataEditAuthority _ = false

evidenceOnlyObservation : ParserObservationKind → Bool
evidenceOnlyObservation _ = true

parserObservationDoesNotPromoteAuthority :
  ∀ observation →
  promotesLegalAuthority observation ≡ false
parserObservationDoesNotPromoteAuthority observation = refl

parserObservationDoesNotGrantWikidataAuthority :
  ∀ observation →
  grantsLiveWikidataEditAuthority observation ≡ false
parserObservationDoesNotGrantWikidataAuthority observation = refl

parserObservationIsEvidenceOnly :
  ∀ observation →
  evidenceOnlyObservation observation ≡ true
parserObservationIsEvidenceOnly observation = refl
