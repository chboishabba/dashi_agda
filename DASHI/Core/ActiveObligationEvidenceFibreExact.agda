module DASHI.Core.ActiveObligationEvidenceFibreExact where

open import DASHI.Core.Prelude
import DASHI.Core.RequiredAxisSupportSquareExact as Required

record ActiveObligationFamily
    (State Query Axis : Set) : Set₁ where
  constructor activeObligationFamily
  field
    Active : State → Query → Axis → Set
    evidenceAt : State → Query → Axis → Required.SupportSquare

open ActiveObligationFamily public

ResolvedFor :
  ∀ {State Query Axis} →
  ActiveObligationFamily State Query Axis →
  State → Query → Set
ResolvedFor {Axis = Axis} family state query =
  (axis : Axis) →
  Active family state query axis →
  Required.ResolvedPositive (evidenceAt family state query axis)

record MissingActiveObligation
    {State Query Axis}
    (family : ActiveObligationFamily State Query Axis)
    (state : State)
    (query : Query) : Set₁ where
  constructor missingActiveObligation
  field
    axis : Axis
    axisIsActive : Active family state query axis
    evidenceMissing : Required.MissingEvidence (evidenceAt family state query axis)

open MissingActiveObligation public

missingActiveObligationBlocksResolution :
  ∀ {State Query Axis}
    {family : ActiveObligationFamily State Query Axis}
    {state : State} {query : Query} →
  MissingActiveObligation family state query →
  ResolvedFor family state query → ⊥
missingActiveObligationBlocksResolution missing resolved =
  Required.missingCannotBeResolvedPositive
    (evidenceMissing missing)
    (resolved (axis missing) (axisIsActive missing))

data AlignmentObligation : Set where
  identifierObligation : AlignmentObligation
  subclassObligation : AlignmentObligation
  disjointnessObligation : AlignmentObligation

data AlignmentStratum : Set where
  identifierOnly : AlignmentStratum
  subclassTransport : AlignmentStratum
  disjointnessTransport : AlignmentStratum

data AlignmentQuery : Set where
  identifierQuery : AlignmentQuery
  subclassQuery : AlignmentQuery
  disjointnessQuery : AlignmentQuery

data Never : Set where

DemoActive : AlignmentStratum → AlignmentQuery → AlignmentObligation → Set
DemoActive identifierOnly identifierQuery identifierObligation = ⊤
DemoActive subclassTransport subclassQuery identifierObligation = ⊤
DemoActive subclassTransport subclassQuery subclassObligation = ⊤
DemoActive disjointnessTransport disjointnessQuery identifierObligation = ⊤
DemoActive disjointnessTransport disjointnessQuery subclassObligation = ⊤
DemoActive disjointnessTransport disjointnessQuery disjointnessObligation = ⊤
DemoActive _ _ _ = Never

positive : Required.SupportSquare
positive = Required.supportSquare true false

missing : Required.SupportSquare
missing = Required.supportSquare false false

DemoEvidence : AlignmentStratum → AlignmentQuery → AlignmentObligation → Required.SupportSquare
DemoEvidence identifierOnly identifierQuery identifierObligation = positive
DemoEvidence subclassTransport subclassQuery identifierObligation = positive
DemoEvidence subclassTransport subclassQuery subclassObligation = positive
DemoEvidence disjointnessTransport disjointnessQuery identifierObligation = positive
DemoEvidence disjointnessTransport disjointnessQuery subclassObligation = positive
DemoEvidence disjointnessTransport disjointnessQuery disjointnessObligation = missing
DemoEvidence _ _ _ = missing

demoFamily : ActiveObligationFamily AlignmentStratum AlignmentQuery AlignmentObligation
demoFamily = activeObligationFamily DemoActive DemoEvidence

identifierOnlyResolved : ResolvedFor demoFamily identifierOnly identifierQuery
identifierOnlyResolved identifierObligation tt = refl , refl
identifierOnlyResolved subclassObligation ()
identifierOnlyResolved disjointnessObligation ()

subclassTransportResolved : ResolvedFor demoFamily subclassTransport subclassQuery
subclassTransportResolved identifierObligation tt = refl , refl
subclassTransportResolved subclassObligation tt = refl , refl
subclassTransportResolved disjointnessObligation ()

missingDisjointnessWitness :
  MissingActiveObligation demoFamily disjointnessTransport disjointnessQuery
missingDisjointnessWitness =
  missingActiveObligation disjointnessObligation tt (refl , refl)

disjointnessLanguageNotResolved :
  ResolvedFor demoFamily disjointnessTransport disjointnessQuery → ⊥
disjointnessLanguageNotResolved =
  missingActiveObligationBlocksResolution missingDisjointnessWitness

record ActiveObligationBoundary : Set where
  constructor activeObligationBoundary
  field
    obligationFamilyMayVaryByStateAndQuery : Bool
    inactiveObligationCountsAsMissingFailure : Bool
    strongerInferenceLanguageCanActivateAdditionalObligations : Bool
    activeMissingObligationBlocksResolution : Bool

canonicalActiveObligationBoundary : ActiveObligationBoundary
canonicalActiveObligationBoundary =
  activeObligationBoundary true false true true
