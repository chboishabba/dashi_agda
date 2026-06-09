module DASHI.Physics.Closure.YMKillingBoundaryOppositeFaceInvolutionLightweightBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

domainContractReference : String
domainContractReference =
  "DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract"

fluxCancellationReference : String
fluxCancellationReference =
  "DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationBoundary"

data OppositeFaceClause : Set where
  chooseBoundaryFacePairing :
    OppositeFaceClause
  defineOppositeFaceMap :
    OppositeFaceClause
  proveOppositeFaceMapTotal :
    OppositeFaceClause
  proveOppositeFaceMapInvolutive :
    OppositeFaceClause
  preserveBoundaryFaceDegree :
    OppositeFaceClause
  preserveKillingWeightProfile :
    OppositeFaceClause
  reverseBoundaryOrientationSign :
    OppositeFaceClause
  preserveGaugeCompatibleFaceLabels :
    OppositeFaceClause
  routePairedFacesIntoFluxCancellation :
    OppositeFaceClause

canonicalOppositeFaceClauses : List OppositeFaceClause
canonicalOppositeFaceClauses =
  chooseBoundaryFacePairing
  ∷ defineOppositeFaceMap
  ∷ proveOppositeFaceMapTotal
  ∷ proveOppositeFaceMapInvolutive
  ∷ preserveBoundaryFaceDegree
  ∷ preserveKillingWeightProfile
  ∷ reverseBoundaryOrientationSign
  ∷ preserveGaugeCompatibleFaceLabels
  ∷ routePairedFacesIntoFluxCancellation
  ∷ []

oppositeFaceClauseCount : Nat
oppositeFaceClauseCount = listLength canonicalOppositeFaceClauses

oppositeFaceClauseCountIs9 : oppositeFaceClauseCount ≡ 9
oppositeFaceClauseCountIs9 = refl

data OppositeFaceMechanism : Set where
  antipodalFaceCoordinatesMatch :
    OppositeFaceMechanism
  faceNormalSignFlips :
    OppositeFaceMechanism
  faceMeasureIsInvariant :
    OppositeFaceMechanism
  localGaugeStencilIsTransported :
    OppositeFaceMechanism

canonicalOppositeFaceMechanisms : List OppositeFaceMechanism
canonicalOppositeFaceMechanisms =
  antipodalFaceCoordinatesMatch
  ∷ faceNormalSignFlips
  ∷ faceMeasureIsInvariant
  ∷ localGaugeStencilIsTransported
  ∷ []

oppositeFaceMechanismCount : Nat
oppositeFaceMechanismCount = listLength canonicalOppositeFaceMechanisms

oppositeFaceMechanismCountIs4 : oppositeFaceMechanismCount ≡ 4
oppositeFaceMechanismCountIs4 = refl

data OppositeFaceBlocker : Set where
  blocker-opposite-face-theorem-unproved :
    OppositeFaceBlocker
  blocker-flux-cancellation-still-open :
    OppositeFaceBlocker
  blocker-ym1-still-open :
    OppositeFaceBlocker
  blocker-ym-clay-forbidden :
    OppositeFaceBlocker

canonicalOppositeFaceBlockers : List OppositeFaceBlocker
canonicalOppositeFaceBlockers =
  blocker-opposite-face-theorem-unproved
  ∷ blocker-flux-cancellation-still-open
  ∷ blocker-ym1-still-open
  ∷ blocker-ym-clay-forbidden
  ∷ []

oppositeFaceBlockerCount : Nat
oppositeFaceBlockerCount = listLength canonicalOppositeFaceBlockers

oppositeFaceBlockerCountIs4 : oppositeFaceBlockerCount ≡ 4
oppositeFaceBlockerCountIs4 = refl

OppositeFaceTheoremProvedLightweight : Bool
OppositeFaceTheoremProvedLightweight = false

OppositeFaceTheoremProvedLightweightIsFalse :
  OppositeFaceTheoremProvedLightweight ≡ false
OppositeFaceTheoremProvedLightweightIsFalse = refl

YM1PromotedFromOppositeFace : Bool
YM1PromotedFromOppositeFace = false

YM1PromotedFromOppositeFaceIsFalse :
  YM1PromotedFromOppositeFace ≡ false
YM1PromotedFromOppositeFaceIsFalse = refl

record YMKillingBoundaryOppositeFaceInvolutionLightweightBoundary : Set where
  field
    clauses : List OppositeFaceClause
    clausesAreCanonical : clauses ≡ canonicalOppositeFaceClauses
    mechanisms : List OppositeFaceMechanism
    mechanismsAreCanonical : mechanisms ≡ canonicalOppositeFaceMechanisms
    blockers : List OppositeFaceBlocker
    blockersAreCanonical : blockers ≡ canonicalOppositeFaceBlockers
    clauseCountIs9 : oppositeFaceClauseCount ≡ 9
    mechanismCountIs4 : oppositeFaceMechanismCount ≡ 4
    blockerCountIs4 : oppositeFaceBlockerCount ≡ 4
    theoremStillFalse : OppositeFaceTheoremProvedLightweight ≡ false
    ym1StillFalse : YM1PromotedFromOppositeFace ≡ false

canonicalYMKillingBoundaryOppositeFaceInvolutionLightweightBoundary :
  YMKillingBoundaryOppositeFaceInvolutionLightweightBoundary
canonicalYMKillingBoundaryOppositeFaceInvolutionLightweightBoundary =
  record
    { clauses = canonicalOppositeFaceClauses
    ; clausesAreCanonical = refl
    ; mechanisms = canonicalOppositeFaceMechanisms
    ; mechanismsAreCanonical = refl
    ; blockers = canonicalOppositeFaceBlockers
    ; blockersAreCanonical = refl
    ; clauseCountIs9 = refl
    ; mechanismCountIs4 = refl
    ; blockerCountIs4 = refl
    ; theoremStillFalse = refl
    ; ym1StillFalse = refl
    }

YMOppositeFaceLightweightBoundaryRecorded : Bool
YMOppositeFaceLightweightBoundaryRecorded = true

YMOppositeFaceLightweightBoundaryRecordedIsTrue :
  YMOppositeFaceLightweightBoundaryRecorded ≡ true
YMOppositeFaceLightweightBoundaryRecordedIsTrue = refl
