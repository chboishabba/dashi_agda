module DASHI.Physics.Closure.DiscreteStokesBianchiObstruction where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; []; _++_)

import DASHI.Foundations.RealAnalysisAxioms as RA
import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteBianchiIdentitySurface as DBIS
import DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature as Ricci

cong :
  {A B : Set} →
  {x y : A} →
  (f : A → B) →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

trans :
  {A : Set} →
  {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
trans refl y≡z = y≡z

data ⊥ : Set where

_≢_ :
  {A : Set} →
  A →
  A →
  Set
x ≢ y = x ≡ y → ⊥

mapList :
  {A B : Set} →
  (A → B) →
  List A →
  List B
mapList =
  RA.mapList

mapListAppend :
  {A B : Set} →
  (f : A → B) →
  (left right : List A) →
  mapList f (left ++ right)
  ≡
  mapList f left ++ mapList f right
mapListAppend =
  RA.mapListAppend

mapListCompose :
  {A B C : Set} →
  (f : B → C) →
  (g : A → B) →
  (xs : List A) →
  mapList f (mapList g xs)
  ≡
  mapList (λ x → f (g x)) xs
mapListCompose f g [] = refl
mapListCompose f g (x ∷ xs) =
  cong
    (λ rest → f (g x) ∷ rest)
    (mapListCompose f g xs)

mapListPointwise :
  {A B : Set} →
  (f g : A → B) →
  ((x : A) → f x ≡ g x) →
  (xs : List A) →
  mapList f xs ≡ mapList g xs
mapListPointwise f g pointwise [] = refl
mapListPointwise f g pointwise (x ∷ xs)
  rewrite pointwise x
        | mapListPointwise f g pointwise xs =
  refl

------------------------------------------------------------------------
-- Discrete Stokes / Bianchi obstruction.
--
-- The local B0.2 Stokes surface in RealAnalysisAxioms supplies a finite
-- Nat/telescoping receipt and an authority socket for analytic Stokes.  It
-- does not supply the GR-specific primitive needed here: a carrier 3-cell
-- whose boundary word is identified with CRT monodromy holonomy and whose
-- boundary-of-boundary cancellation is transported to the cyclic covariant
-- derivative form of the discrete Bianchi identity.

data DiscreteStokesBianchiStatus : Set where
  blockedMissingGRBoundaryOfBoundaryPrimitive :
    DiscreteStokesBianchiStatus
  exactCRTBoundaryOfBoundaryCarrierHolonomyBridgeMissing :
    DiscreteStokesBianchiStatus
  exactCRTBoundaryWordHolonomyTransportCyclicBridgeMissing :
    DiscreteStokesBianchiStatus

data CRTMonodromy3Cell : Set where
  crtMonodromyCube :
    CRTMonodromy3Cell

data CRTMonodromy2Face : Set where
  faceP2P3Neg :
    CRTMonodromy2Face
  faceP2P3Pos :
    CRTMonodromy2Face
  faceP2JP3Neg :
    CRTMonodromy2Face
  faceP2JP3Pos :
    CRTMonodromy2Face
  faceP3JP2Neg :
    CRTMonodromy2Face
  faceP3JP2Pos :
    CRTMonodromy2Face

data CRTMonodromy1Edge : Set where
  edgeP2 :
    CRTMonodromy1Edge
  edgeP3 :
    CRTMonodromy1Edge
  edgeJ :
    CRTMonodromy1Edge

crtMonodromy3Boundary :
  CRTMonodromy3Cell →
  List CRTMonodromy2Face
crtMonodromy3Boundary crtMonodromyCube =
  faceP2P3Neg
  ∷ faceP2P3Pos
  ∷ faceP2JP3Neg
  ∷ faceP2JP3Pos
  ∷ faceP3JP2Neg
  ∷ faceP3JP2Pos
  ∷ []

crtMonodromy2Boundary :
  CRTMonodromy2Face →
  List CRTMonodromy1Edge
crtMonodromy2Boundary faceP2P3Neg = edgeP2 ∷ edgeP3 ∷ []
crtMonodromy2Boundary faceP2P3Pos = edgeP3 ∷ edgeP2 ∷ []
crtMonodromy2Boundary faceP2JP3Neg = edgeP2 ∷ edgeJ ∷ edgeP3 ∷ []
crtMonodromy2Boundary faceP2JP3Pos = edgeP3 ∷ edgeJ ∷ edgeP2 ∷ []
crtMonodromy2Boundary faceP3JP2Neg = edgeP3 ∷ edgeJ ∷ edgeP2 ∷ []
crtMonodromy2Boundary faceP3JP2Pos = edgeP2 ∷ edgeJ ∷ edgeP3 ∷ []

crtMonodromyBoundaryOfBoundaryWord :
  CRTMonodromy3Cell →
  List CRTMonodromy1Edge
crtMonodromyBoundaryOfBoundaryWord crtMonodromyCube = []

crtMonodromyBoundaryOfBoundaryZero :
  (cell : CRTMonodromy3Cell) →
  crtMonodromyBoundaryOfBoundaryWord cell ≡ []
crtMonodromyBoundaryOfBoundaryZero crtMonodromyCube = refl

crtMonodromy2BoundaryWord :
  List CRTMonodromy2Face →
  List CRTMonodromy1Edge
crtMonodromy2BoundaryWord [] = []
crtMonodromy2BoundaryWord (face ∷ rest) =
  crtMonodromy2Boundary face ++ crtMonodromy2BoundaryWord rest

crtMonodromy3BoundaryShellWord :
  CRTMonodromy3Cell →
  List CRTMonodromy1Edge
crtMonodromy3BoundaryShellWord cell =
  crtMonodromy2BoundaryWord (crtMonodromy3Boundary cell)

data CRTBoundaryWordIsNonErasing : List CRTMonodromy1Edge → Set where
  crtMonodromyShellWordIsNonErasing :
    CRTBoundaryWordIsNonErasing
      (crtMonodromy3BoundaryShellWord crtMonodromyCube)

CRTBoundaryWordAction :
  Set
CRTBoundaryWordAction =
  DCRT.DiscreteConnectionCandidateFromCRT.Carrier
    DCRT.canonicalDiscreteConnectionCandidateFromCRT →
  DCRT.DiscreteConnectionCandidateFromCRT.Carrier
    DCRT.canonicalDiscreteConnectionCandidateFromCRT

identityCRTBoundaryWordAction :
  CRTBoundaryWordAction
identityCRTBoundaryWordAction carrier = carrier

crtMonodromyEdgeHolonomy :
  CRTMonodromy1Edge →
  DCRT.CRTHolonomyElement
crtMonodromyEdgeHolonomy edgeP2 = DCRT.crtMonodromyHolonomy
crtMonodromyEdgeHolonomy edgeP3 = DCRT.crtMonodromyHolonomy
crtMonodromyEdgeHolonomy edgeJ = DCRT.crtMonodromyHolonomy

crtMonodromyEdgeAction :
  CRTMonodromy1Edge →
  CRTBoundaryWordAction
crtMonodromyEdgeAction edgeP2 = DCRT.CRTMonodromyConnection
crtMonodromyEdgeAction edgeP3 = DCRT.CRTMonodromyConnection
crtMonodromyEdgeAction edgeJ = DCRT.CRTMonodromyConnection

crtMonodromyBoundaryWordAction :
  List CRTMonodromy1Edge →
  CRTBoundaryWordAction
crtMonodromyBoundaryWordAction [] =
  identityCRTBoundaryWordAction
crtMonodromyBoundaryWordAction (edge ∷ rest) carrier =
  crtMonodromyBoundaryWordAction rest
    (crtMonodromyEdgeAction edge carrier)

crtMonodromyBoundaryWordActionEmpty :
  (carrier :
    DCRT.DiscreteConnectionCandidateFromCRT.Carrier
      DCRT.canonicalDiscreteConnectionCandidateFromCRT) →
  crtMonodromyBoundaryWordAction [] carrier ≡ carrier
crtMonodromyBoundaryWordActionEmpty carrier = refl

crtMonodromyBoundaryWordActionAppend :
  (left right : List CRTMonodromy1Edge) →
  (carrier :
    DCRT.DiscreteConnectionCandidateFromCRT.Carrier
      DCRT.canonicalDiscreteConnectionCandidateFromCRT) →
  crtMonodromyBoundaryWordAction (left ++ right) carrier
  ≡
  crtMonodromyBoundaryWordAction right
    (crtMonodromyBoundaryWordAction left carrier)
crtMonodromyBoundaryWordActionAppend [] right carrier = refl
crtMonodromyBoundaryWordActionAppend (edge ∷ left) right carrier =
  crtMonodromyBoundaryWordActionAppend
    left
    right
    (crtMonodromyEdgeAction edge carrier)

crtMonodromyWordHolonomyTrace :
  List CRTMonodromy1Edge →
  List DCRT.CRTHolonomyElement
crtMonodromyWordHolonomyTrace [] = []
crtMonodromyWordHolonomyTrace (edge ∷ rest) =
  crtMonodromyEdgeHolonomy edge
  ∷
  crtMonodromyWordHolonomyTrace rest

crtMonodromyWordHolonomyTraceAppend :
  (left right : List CRTMonodromy1Edge) →
  crtMonodromyWordHolonomyTrace (left ++ right)
  ≡
  crtMonodromyWordHolonomyTrace left
  ++
  crtMonodromyWordHolonomyTrace right
crtMonodromyWordHolonomyTraceAppend [] right = refl
crtMonodromyWordHolonomyTraceAppend (edge ∷ left) right =
  cong
    (λ trace → crtMonodromyEdgeHolonomy edge ∷ trace)
    (crtMonodromyWordHolonomyTraceAppend left right)

record CRTBoundaryWordHolonomyTraceHomomorphism : Set₁ where
  field
    wordHolonomyTrace :
      List CRTMonodromy1Edge →
      List DCRT.CRTHolonomyElement

    wordHolonomyTraceIsCanonical :
      wordHolonomyTrace ≡ crtMonodromyWordHolonomyTrace

    emptyWordTraceIsEmpty :
      wordHolonomyTrace [] ≡ []

    appendWordTraceLaw :
      (left right : List CRTMonodromy1Edge) →
      wordHolonomyTrace (left ++ right)
      ≡
      wordHolonomyTrace left ++ wordHolonomyTrace right

    boundaryShellWord :
      List CRTMonodromy1Edge

    boundaryShellWordIsCanonical :
      boundaryShellWord ≡ crtMonodromy3BoundaryShellWord crtMonodromyCube

    boundaryShellWordIsNonErasing :
      CRTBoundaryWordIsNonErasing boundaryShellWord

    boundaryShellHolonomyTrace :
      List DCRT.CRTHolonomyElement

    boundaryShellHolonomyTraceIsWordTrace :
      boundaryShellHolonomyTrace
      ≡
      wordHolonomyTrace boundaryShellWord

    boundaryOfBoundaryTrace :
      List DCRT.CRTHolonomyElement

    boundaryOfBoundaryTraceIsEmpty :
      boundaryOfBoundaryTrace ≡ []

    exactHomomorphismBoundary :
      List String

canonicalCRTBoundaryWordHolonomyTraceHomomorphism :
  CRTBoundaryWordHolonomyTraceHomomorphism
canonicalCRTBoundaryWordHolonomyTraceHomomorphism =
  record
    { wordHolonomyTrace =
        crtMonodromyWordHolonomyTrace
    ; wordHolonomyTraceIsCanonical =
        refl
    ; emptyWordTraceIsEmpty =
        refl
    ; appendWordTraceLaw =
        crtMonodromyWordHolonomyTraceAppend
    ; boundaryShellWord =
        crtMonodromy3BoundaryShellWord crtMonodromyCube
    ; boundaryShellWordIsCanonical =
        refl
    ; boundaryShellWordIsNonErasing =
        crtMonodromyShellWordIsNonErasing
    ; boundaryShellHolonomyTrace =
        crtMonodromyWordHolonomyTrace
          (crtMonodromy3BoundaryShellWord crtMonodromyCube)
    ; boundaryShellHolonomyTraceIsWordTrace =
        refl
    ; boundaryOfBoundaryTrace =
        crtMonodromyWordHolonomyTrace
          (crtMonodromyBoundaryOfBoundaryWord crtMonodromyCube)
    ; boundaryOfBoundaryTraceIsEmpty =
        refl
    ; exactHomomorphismBoundary =
        "CRT edge words have a canonical holonomy trace into CRTHolonomyElement lists"
        ∷ "The CRT holonomy trace preserves list concatenation definitionally up to the append lemma"
        ∷ "The six-face CRT boundary shell is retained as a non-erasing edge word"
        ∷ "The separate formal boundary-of-boundary word remains empty and has empty holonomy trace"
        ∷ "This is a CRT-side word/trace homomorphism only, not a Stokes-to-CRT interpreter"
        ∷ []
    }

crtMonodromyBoundaryOfBoundaryAction :
  CRTMonodromy3Cell →
  CRTBoundaryWordAction
crtMonodromyBoundaryOfBoundaryAction cell =
  crtMonodromyBoundaryWordAction
    (crtMonodromyBoundaryOfBoundaryWord cell)

crtMonodromyBoundaryOfBoundaryActionIsIdentity :
  (cell : CRTMonodromy3Cell) →
  crtMonodromyBoundaryOfBoundaryAction cell
  ≡
  identityCRTBoundaryWordAction
crtMonodromyBoundaryOfBoundaryActionIsIdentity crtMonodromyCube = refl

crtBoundaryWordActionIsIdentityFromEmpty :
  (word : List CRTMonodromy1Edge) →
  word ≡ [] →
  crtMonodromyBoundaryWordAction word
  ≡
  identityCRTBoundaryWordAction
crtBoundaryWordActionIsIdentityFromEmpty [] refl = refl

record CRTBoundaryWordFoldConcatenationInterface : Set₁ where
  field
    wordAction :
      List CRTMonodromy1Edge →
      CRTBoundaryWordAction

    wordActionIsCanonical :
      wordAction ≡ crtMonodromyBoundaryWordAction

    emptyWordActsByIdentity :
      wordAction [] ≡ identityCRTBoundaryWordAction

    appendWordActionLaw :
      (left right : List CRTMonodromy1Edge) →
      (carrier :
        DCRT.DiscreteConnectionCandidateFromCRT.Carrier
          DCRT.canonicalDiscreteConnectionCandidateFromCRT) →
      wordAction (left ++ right) carrier
      ≡
      wordAction right (wordAction left carrier)

    boundaryOfBoundaryWord :
      List CRTMonodromy1Edge

    boundaryOfBoundaryWordIsEmpty :
      boundaryOfBoundaryWord ≡ []

    boundaryOfBoundaryActionIsIdentityFromEmpty :
      wordAction boundaryOfBoundaryWord
      ≡
      identityCRTBoundaryWordAction

    exactFoldBoundary :
      List String

canonicalCRTBoundaryWordFoldConcatenationInterface :
  CRTBoundaryWordFoldConcatenationInterface
canonicalCRTBoundaryWordFoldConcatenationInterface =
  record
    { wordAction =
        crtMonodromyBoundaryWordAction
    ; wordActionIsCanonical =
        refl
    ; emptyWordActsByIdentity =
        refl
    ; appendWordActionLaw =
        crtMonodromyBoundaryWordActionAppend
    ; boundaryOfBoundaryWord =
        crtMonodromyBoundaryOfBoundaryWord crtMonodromyCube
    ; boundaryOfBoundaryWordIsEmpty =
        refl
    ; boundaryOfBoundaryActionIsIdentityFromEmpty =
        refl
    ; exactFoldBoundary =
        "CRT boundary words have a canonical fold into CRTBoundaryWordAction"
        ∷ "The empty CRT boundary word acts definitionally as identity"
        ∷ "The CRT word fold satisfies the pointwise append law for list concatenation"
        ∷ "The formal CRT boundary-of-boundary word uses the empty-word witness to act as identity"
        ∷ "No local Stokes BoundaryWordAtDepth concatenation or interpreter homomorphism law is supplied by RealAnalysisAxioms"
        ∷ []
    }

record CRTMonodromyBoundaryOfBoundaryCarrier : Set₁ where
  field
    cell3 :
      CRTMonodromy3Cell

    boundary3 :
      CRTMonodromy3Cell →
      List CRTMonodromy2Face

    boundary3IsCanonical :
      boundary3 cell3 ≡ crtMonodromy3Boundary cell3

    boundary2 :
      CRTMonodromy2Face →
      List CRTMonodromy1Edge

    boundary2IsCanonical :
      (face : CRTMonodromy2Face) →
      boundary2 face ≡ crtMonodromy2Boundary face

    boundaryOfBoundaryWord :
      CRTMonodromy3Cell →
      List CRTMonodromy1Edge

    boundaryOfBoundaryWordIsEmpty :
      boundaryOfBoundaryWord cell3 ≡ []

    boundaryOfBoundaryZero :
      (cell : CRTMonodromy3Cell) →
      boundaryOfBoundaryWord cell ≡ []

    connection :
      DCRT.DiscreteConnectionCandidateFromCRT.Carrier
        DCRT.canonicalDiscreteConnectionCandidateFromCRT →
      DCRT.DiscreteConnectionCandidateFromCRT.Carrier
        DCRT.canonicalDiscreteConnectionCandidateFromCRT

    connectionIsCRTMonodromy :
      connection ≡ DCRT.CRTMonodromyConnection

    exactBoundary :
      List String

canonicalCRTMonodromyBoundaryOfBoundaryCarrier :
  CRTMonodromyBoundaryOfBoundaryCarrier
canonicalCRTMonodromyBoundaryOfBoundaryCarrier =
  record
    { cell3 =
        crtMonodromyCube
    ; boundary3 =
        crtMonodromy3Boundary
    ; boundary3IsCanonical =
        refl
    ; boundary2 =
        crtMonodromy2Boundary
    ; boundary2IsCanonical =
        λ face → refl
    ; boundaryOfBoundaryWord =
        crtMonodromyBoundaryOfBoundaryWord
    ; boundaryOfBoundaryWordIsEmpty =
        refl
    ; boundaryOfBoundaryZero =
        crtMonodromyBoundaryOfBoundaryZero
    ; connection =
        DCRT.CRTMonodromyConnection
    ; connectionIsCRTMonodromy =
        refl
    ; exactBoundary =
        "Formal CRT monodromy 3-cell carrier is inhabited over the canonical CRTMonodromyConnection"
        ∷ "The six oriented 2-faces name the p2/p3/J commutator shell used as the boundary word carrier"
        ∷ "The boundary-of-boundary word is definitionally empty for this formal carrier"
        ∷ "This does not identify that empty word with a holonomy action or cyclic covariant derivative"
        ∷ []
    }

record CRTBoundaryWordToHolonomyTransport : Set₁ where
  field
    carrier :
      CRTMonodromyBoundaryOfBoundaryCarrier

    carrierIsCanonical :
      carrier
      ≡
      canonicalCRTMonodromyBoundaryOfBoundaryCarrier

    edgeHolonomy :
      CRTMonodromy1Edge →
      DCRT.CRTHolonomyElement

    edgeHolonomyIsCanonical :
      (edge : CRTMonodromy1Edge) →
      edgeHolonomy edge ≡ crtMonodromyEdgeHolonomy edge

    edgeAction :
      CRTMonodromy1Edge →
      CRTBoundaryWordAction

    edgeActionIsCRTMonodromyConnection :
      (edge : CRTMonodromy1Edge) →
      edgeAction edge ≡ DCRT.CRTMonodromyConnection

    wordAction :
      List CRTMonodromy1Edge →
      CRTBoundaryWordAction

    wordActionIsCanonical :
      (word : List CRTMonodromy1Edge) →
      wordAction word ≡ crtMonodromyBoundaryWordAction word

    boundaryOfBoundaryAction :
      CRTMonodromy3Cell →
      CRTBoundaryWordAction

    boundaryOfBoundaryActionIsCanonical :
      (cell : CRTMonodromy3Cell) →
      boundaryOfBoundaryAction cell
      ≡
      crtMonodromyBoundaryOfBoundaryAction cell

    boundaryOfBoundaryActionIsIdentity :
      (cell : CRTMonodromy3Cell) →
      boundaryOfBoundaryAction cell
      ≡
      identityCRTBoundaryWordAction

    exactTransportBoundary :
      List String

canonicalCRTBoundaryWordToHolonomyTransport :
  CRTBoundaryWordToHolonomyTransport
canonicalCRTBoundaryWordToHolonomyTransport =
  record
    { carrier =
        canonicalCRTMonodromyBoundaryOfBoundaryCarrier
    ; carrierIsCanonical =
        refl
    ; edgeHolonomy =
        crtMonodromyEdgeHolonomy
    ; edgeHolonomyIsCanonical =
        λ edge → refl
    ; edgeAction =
        crtMonodromyEdgeAction
    ; edgeActionIsCRTMonodromyConnection =
        λ
          { edgeP2 → refl
          ; edgeP3 → refl
          ; edgeJ → refl
          }
    ; wordAction =
        crtMonodromyBoundaryWordAction
    ; wordActionIsCanonical =
        λ word → refl
    ; boundaryOfBoundaryAction =
        crtMonodromyBoundaryOfBoundaryAction
    ; boundaryOfBoundaryActionIsCanonical =
        λ cell → refl
    ; boundaryOfBoundaryActionIsIdentity =
        crtMonodromyBoundaryOfBoundaryActionIsIdentity
    ; exactTransportBoundary =
        "Each formal CRT boundary edge is mapped to crtMonodromyHolonomy"
        ∷ "Each formal CRT boundary edge acts by CRTMonodromyConnection"
        ∷ "Boundary words act by iterated edge action over the canonical RTC.Carrier 1 target"
        ∷ "The formal CRT boundary-of-boundary word acts definitionally as the identity because the word is empty"
        ∷ "This transport does not identify the action with a cyclic covariant derivative or contracted Bianchi law"
        ∷ []
    }

data CRTDiscreteStokesSpecialisationMissingField : Set where
  missingStokesBoundaryWordInterpreterToCRTBoundaryWord :
    CRTDiscreteStokesSpecialisationMissingField
  missingStokesBoundaryWordInterpreterLawForCRTBoundary :
    CRTDiscreteStokesSpecialisationMissingField
  missingStokesBoundaryProductMatchesCRTConnectionAction :
    CRTDiscreteStokesSpecialisationMissingField
  missingCRTConnectionActionToCyclicCovariantDerivative :
    CRTDiscreteStokesSpecialisationMissingField

canonicalCRTDiscreteStokesSpecialisationMissingFields :
  List CRTDiscreteStokesSpecialisationMissingField
canonicalCRTDiscreteStokesSpecialisationMissingFields =
  missingStokesBoundaryWordInterpreterToCRTBoundaryWord
  ∷ missingStokesBoundaryWordInterpreterLawForCRTBoundary
  ∷ missingStokesBoundaryProductMatchesCRTConnectionAction
  ∷ missingCRTConnectionActionToCyclicCovariantDerivative
  ∷ []

data LocalToCRTBoundaryWordSemanticAlignmentMissingEvidence : Set where
  missingLocalBoundaryWordEdgeLabelingIntoCRTMonodromyEdges :
    LocalToCRTBoundaryWordSemanticAlignmentMissingEvidence
  missingSelectedNativeBoundaryLabelShellPreimage :
    LocalToCRTBoundaryWordSemanticAlignmentMissingEvidence
  missingSelectedNativeBoundaryLabelShellMapsToCRTShell :
    LocalToCRTBoundaryWordSemanticAlignmentMissingEvidence

canonicalLocalToCRTBoundaryWordSemanticAlignmentMissingEvidence :
  List LocalToCRTBoundaryWordSemanticAlignmentMissingEvidence
canonicalLocalToCRTBoundaryWordSemanticAlignmentMissingEvidence =
  missingLocalBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
  ∷ missingSelectedNativeBoundaryLabelShellPreimage
  ∷ missingSelectedNativeBoundaryLabelShellMapsToCRTShell
  ∷ []

record LocalToCRTBoundaryWordSemanticAlignmentRequest : Set where
  field
    requestName :
      String

    requiredSourceInterfaceName :
      String

    requiredTargetWordName :
      String

    targetWordIsNonErasing :
      CRTBoundaryWordIsNonErasing
        (crtMonodromy3BoundaryShellWord crtMonodromyCube)

    requiredSemanticInterpreterTypeName :
      String

    requiredAppendLawTypeName :
      String

    requiredConstructorFieldName :
      String

    requiredEdgeLabelingFieldName :
      String

    requiredSelectedWordFieldName :
      String

    requiredNonErasingAppendLawFieldName :
      String

    requiredFoldComputationLawFieldName :
      String

    typedPrimitiveRequestTypeName :
      String

    appendFoldAlreadyAvailable :
      Bool

    appendFoldAlreadyAvailableIsTrue :
      appendFoldAlreadyAvailable ≡ true

    acceptedAsGRPromotion :
      Bool

    acceptedAsGRPromotionIsFalse :
      acceptedAsGRPromotion ≡ false

    missingEvidence :
      List LocalToCRTBoundaryWordSemanticAlignmentMissingEvidence

    missingEvidenceIsCanonical :
      missingEvidence
      ≡
      canonicalLocalToCRTBoundaryWordSemanticAlignmentMissingEvidence

    firstMissingEvidence :
      LocalToCRTBoundaryWordSemanticAlignmentMissingEvidence

    firstMissingEvidenceIsLocalBoundaryLabelToCRTEdge :
      firstMissingEvidence
      ≡
      missingLocalBoundaryWordEdgeLabelingIntoCRTMonodromyEdges

    exactRequestBoundary :
      List String

canonicalLocalToCRTBoundaryWordSemanticAlignmentRequest :
  LocalToCRTBoundaryWordSemanticAlignmentRequest
canonicalLocalToCRTBoundaryWordSemanticAlignmentRequest =
  record
    { requestName =
        "LocalToCRTBoundaryWordSemanticAlignment"
    ; requiredSourceInterfaceName =
        "LocalBoundaryWordAtDepthStructuralInterface"
    ; requiredTargetWordName =
        "crtMonodromy3BoundaryShellWord crtMonodromyCube"
    ; targetWordIsNonErasing =
        crtMonodromyShellWordIsNonErasing
    ; requiredSemanticInterpreterTypeName =
        "StokesBoundaryWordInterpreterType surface depth loop"
    ; requiredAppendLawTypeName =
        "StokesBoundaryWordInterpreterHomomorphismLawType interpreter localBoundaryWordAppend"
    ; requiredConstructorFieldName =
        "localCRTBoundaryShellWordConstructor"
    ; requiredEdgeLabelingFieldName =
        "localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges"
    ; requiredSelectedWordFieldName =
        "selectedNativeBoundaryLabelShellPreimage"
    ; requiredNonErasingAppendLawFieldName =
        "derived from native boundaryWordEdgeLabelsAppendAtDepth"
    ; requiredFoldComputationLawFieldName =
        "derived from native boundaryWordFoldComputesMappedEdgeLabelListAtDepth"
    ; typedPrimitiveRequestTypeName =
        "LocalToCRTBoundaryWordSemanticAlignmentPrimitive"
    ; appendFoldAlreadyAvailable =
        true
    ; appendFoldAlreadyAvailableIsTrue =
        refl
    ; acceptedAsGRPromotion =
        false
    ; acceptedAsGRPromotionIsFalse =
        refl
    ; missingEvidence =
        canonicalLocalToCRTBoundaryWordSemanticAlignmentMissingEvidence
    ; missingEvidenceIsCanonical =
        refl
    ; firstMissingEvidence =
        missingLocalBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
    ; firstMissingEvidenceIsLocalBoundaryLabelToCRTEdge =
        refl
    ; exactRequestBoundary =
        "BoundaryWordAtDepth now exposes append, fold, local edge labels, edge-list construction, and fold/list laws through LocalBoundaryWordAtDepthStructuralInterface"
        ∷ "The native RealAnalysis edge labels remain CRT-neutral"
        ∷ "The requested native label-to-CRT map and selected local label preimage still must interpret as crtMonodromy3BoundaryShellWord crtMonodromyCube"
        ∷ "The selected BoundaryWordAtDepth, non-erasing shell witness, append law, and fold/list law are derived after that preimage is supplied"
        ∷ "The CRT shell word and CRT-side list append laws are already available"
        ∷ "This request is not a GR promotion and does not inhabit the CRT Stokes specialisation"
        ∷ []
    }

StokesBoundaryWordInterpreterType :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
    localStokesSurface
    depth →
  Set
StokesBoundaryWordInterpreterType localStokesSurface depth stokesLoop =
  RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop →
  List CRTMonodromy1Edge

StokesBoundaryWordInterpreterHomomorphismLawType :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  StokesBoundaryWordInterpreterType
    localStokesSurface
    depth
    stokesLoop →
  (RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop →
   RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop →
   RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop) →
  Set
StokesBoundaryWordInterpreterHomomorphismLawType
  localStokesSurface
  depth
  stokesLoop
  interpreter
  localBoundaryWordAppend =
  (left right :
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop) →
  interpreter (localBoundaryWordAppend left right)
  ≡
  interpreter left ++ interpreter right

StokesBoundaryWordFoldType :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
    localStokesSurface
    depth →
  Set₁
StokesBoundaryWordFoldType localStokesSurface depth stokesLoop =
  (Target : Set) →
  (RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop →
   Target →
   Target) →
  Target →
  RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop →
  Target

localBoundaryWordAppendFromSurface :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop →
  RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop →
  RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop
localBoundaryWordAppendFromSurface localStokesSurface depth stokesLoop =
  RA.LocalDiscreteNonabelianStokesProofSurface.boundaryWordAppendAtDepth
    localStokesSurface
    depth
    stokesLoop

localBoundaryEdgeLabelFromSurface :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
    localStokesSurface
    depth →
  Set
localBoundaryEdgeLabelFromSurface localStokesSurface depth stokesLoop =
  RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryEdgeLabelAtDepth
    localStokesSurface
    depth
    stokesLoop

localBoundaryWordFromEdgeLabelsFromSurface :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  List
    (localBoundaryEdgeLabelFromSurface
      localStokesSurface
      depth
      stokesLoop) →
  RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop
localBoundaryWordFromEdgeLabelsFromSurface localStokesSurface depth stokesLoop =
  RA.LocalDiscreteNonabelianStokesProofSurface.boundaryWordFromEdgeLabelsAtDepth
    localStokesSurface
    depth
    stokesLoop

localBoundaryWordEdgeLabelsFromSurface :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
    localStokesSurface
    depth
    stokesLoop →
  List
    (localBoundaryEdgeLabelFromSurface
      localStokesSurface
      depth
      stokesLoop)
localBoundaryWordEdgeLabelsFromSurface localStokesSurface depth stokesLoop =
  RA.LocalDiscreteNonabelianStokesProofSurface.boundaryWordEdgeLabelsAtDepth
    localStokesSurface
    depth
    stokesLoop

localBoundaryWordFoldFromSurface :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  StokesBoundaryWordFoldType
    localStokesSurface
    depth
    stokesLoop
localBoundaryWordFoldFromSurface localStokesSurface depth stokesLoop =
  RA.LocalDiscreteNonabelianStokesProofSurface.boundaryWordFoldAtDepth
    localStokesSurface
    depth
    stokesLoop

record LocalBoundaryWordAtDepthStructuralInterface
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface)
  (depth : Nat)
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) :
  Set₁ where
  field
    localBoundaryWordAppend :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop →
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop →
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop

    localBoundaryWordFold :
      StokesBoundaryWordFoldType
        localStokesSurface
        depth
        stokesLoop

    localBoundaryEdgeLabel :
      Set

    localBoundaryEdgeLabelIsSurfaceField :
      localBoundaryEdgeLabel
      ≡
      localBoundaryEdgeLabelFromSurface
        localStokesSurface
        depth
        stokesLoop

    localBoundaryWordFromEdgeLabels :
      List localBoundaryEdgeLabel →
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop

    localBoundaryWordEdgeLabels :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop →
      List localBoundaryEdgeLabel

    localBoundaryWordEdgeLabelsFromConstructed :
      (labels : List localBoundaryEdgeLabel) →
      localBoundaryWordEdgeLabels
        (localBoundaryWordFromEdgeLabels labels)
      ≡
      labels

    localBoundaryWordEdgeLabelsAppend :
      (left right :
        RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
          localStokesSurface
          depth
          stokesLoop) →
      localBoundaryWordEdgeLabels (localBoundaryWordAppend left right)
      ≡
      localBoundaryWordEdgeLabels left
      ++
      localBoundaryWordEdgeLabels right

    localBoundaryWordFoldComputesMappedEdgeLabelList :
      (TargetLabel : Set) →
      (labelMap : localBoundaryEdgeLabel → TargetLabel) →
      (left right :
        RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
          localStokesSurface
          depth
          stokesLoop) →
      localBoundaryWordFold
        (List TargetLabel)
        (λ word accumulatedLabels →
          mapList labelMap (localBoundaryWordEdgeLabels word)
          ++
          accumulatedLabels)
        []
        (localBoundaryWordAppend left right)
      ≡
      mapList labelMap (localBoundaryWordEdgeLabels left)
      ++
      mapList labelMap (localBoundaryWordEdgeLabels right)

    localBoundaryWordFoldComputesEdgeLabelList :
      (left right :
        RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
          localStokesSurface
          depth
          stokesLoop) →
      localBoundaryWordFold
        (List localBoundaryEdgeLabel)
        (λ word accumulatedLabels →
          localBoundaryWordEdgeLabels word
          ++
          accumulatedLabels)
        []
        (localBoundaryWordAppend left right)
      ≡
      localBoundaryWordEdgeLabels left
      ++
      localBoundaryWordEdgeLabels right

    exactStructuralBoundary :
      List String

canonicalLocalBoundaryWordAtDepthStructuralInterface :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  LocalBoundaryWordAtDepthStructuralInterface
    localStokesSurface
    depth
    stokesLoop
canonicalLocalBoundaryWordAtDepthStructuralInterface
  localStokesSurface
  depth
  stokesLoop =
  record
    { localBoundaryWordAppend =
        localBoundaryWordAppendFromSurface
          localStokesSurface
          depth
          stokesLoop
    ; localBoundaryWordFold =
        localBoundaryWordFoldFromSurface
          localStokesSurface
          depth
          stokesLoop
    ; localBoundaryEdgeLabel =
        localBoundaryEdgeLabelFromSurface
          localStokesSurface
          depth
          stokesLoop
    ; localBoundaryEdgeLabelIsSurfaceField =
        refl
    ; localBoundaryWordFromEdgeLabels =
        localBoundaryWordFromEdgeLabelsFromSurface
          localStokesSurface
          depth
          stokesLoop
    ; localBoundaryWordEdgeLabels =
        localBoundaryWordEdgeLabelsFromSurface
          localStokesSurface
          depth
          stokesLoop
    ; localBoundaryWordEdgeLabelsFromConstructed =
        RA.LocalDiscreteNonabelianStokesProofSurface.boundaryWordEdgeLabelsFromConstructedAtDepth
          localStokesSurface
          depth
          stokesLoop
    ; localBoundaryWordEdgeLabelsAppend =
        RA.LocalDiscreteNonabelianStokesProofSurface.boundaryWordEdgeLabelsAppendAtDepth
          localStokesSurface
          depth
          stokesLoop
    ; localBoundaryWordFoldComputesMappedEdgeLabelList =
        RA.LocalDiscreteNonabelianStokesProofSurface.boundaryWordFoldComputesMappedEdgeLabelListAtDepth
          localStokesSurface
          depth
          stokesLoop
    ; localBoundaryWordFoldComputesEdgeLabelList =
        RA.LocalDiscreteNonabelianStokesProofSurface.boundaryWordFoldComputesEdgeLabelListAtDepth
          localStokesSurface
          depth
          stokesLoop
    ; exactStructuralBoundary =
        "LocalDiscreteNonabelianStokesProofSurface now exposes BoundaryWordAtDepth append"
        ∷ "LocalDiscreteNonabelianStokesProofSurface now exposes BoundaryWordAtDepth fold/eliminator"
        ∷ "LocalDiscreteNonabelianStokesProofSurface now exposes local boundary-edge labels"
        ∷ "LocalDiscreteNonabelianStokesProofSurface now exposes edge-label-list word construction"
        ∷ "LocalDiscreteNonabelianStokesProofSurface now exposes constructed-word label round-trip, word-to-edge-label-list append, and mapped fold/list laws"
        ∷ "This structural interface still does not choose a CRTMonodromy1Edge interpreter"
        ∷ "The remaining primitive is the semantic map and selected local label preimage for the CRT boundary shell"
        ∷ []
    }

LocalBoundaryWordFoldComputesCRTListAppendLawType :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  LocalBoundaryWordAtDepthStructuralInterface
    localStokesSurface
    depth
    stokesLoop →
  StokesBoundaryWordInterpreterType
    localStokesSurface
    depth
    stokesLoop →
  Set
LocalBoundaryWordFoldComputesCRTListAppendLawType
  localStokesSurface
  depth
  stokesLoop
  localBoundaryWordStructuralInterface
  interpreter =
  (left right :
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop) →
  LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordFold
    localBoundaryWordStructuralInterface
    (List CRTMonodromy1Edge)
    (λ word accumulatedEdges → interpreter word ++ accumulatedEdges)
    []
    (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordAppend
      localBoundaryWordStructuralInterface
      left
      right)
  ≡
  interpreter left ++ interpreter right

nativeLocalBoundaryLabelCRTInterpreter :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  (localBoundaryLabelToCRTEdge :
    LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
      localBoundaryWordStructuralInterface →
    CRTMonodromy1Edge) →
  StokesBoundaryWordInterpreterType
    localStokesSurface
    depth
    stokesLoop
nativeLocalBoundaryLabelCRTInterpreter
  localBoundaryWordStructuralInterface
  localBoundaryLabelToCRTEdge
  stokesBoundaryWord =
  mapList
    localBoundaryLabelToCRTEdge
    (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordEdgeLabels
      localBoundaryWordStructuralInterface
      stokesBoundaryWord)

nativeLocalBoundaryLabelCRTInterpreterAppendLaw :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  (localBoundaryLabelToCRTEdge :
    LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
      localBoundaryWordStructuralInterface →
    CRTMonodromy1Edge) →
  StokesBoundaryWordInterpreterHomomorphismLawType
    localStokesSurface
    depth
    stokesLoop
    (nativeLocalBoundaryLabelCRTInterpreter
      localBoundaryWordStructuralInterface
      localBoundaryLabelToCRTEdge)
    (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordAppend
      localBoundaryWordStructuralInterface)
nativeLocalBoundaryLabelCRTInterpreterAppendLaw
  localBoundaryWordStructuralInterface
  localBoundaryLabelToCRTEdge
  left
  right =
  trans
    (cong
      (mapList localBoundaryLabelToCRTEdge)
      (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordEdgeLabelsAppend
        localBoundaryWordStructuralInterface
        left
        right))
    (mapListAppend
      localBoundaryLabelToCRTEdge
      (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordEdgeLabels
        localBoundaryWordStructuralInterface
        left)
      (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordEdgeLabels
        localBoundaryWordStructuralInterface
        right))

nativeLocalBoundaryLabelCRTInterpreterFoldListAppendLaw :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  (localBoundaryLabelToCRTEdge :
    LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
      localBoundaryWordStructuralInterface →
    CRTMonodromy1Edge) →
  LocalBoundaryWordFoldComputesCRTListAppendLawType
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface
    (nativeLocalBoundaryLabelCRTInterpreter
      localBoundaryWordStructuralInterface
      localBoundaryLabelToCRTEdge)
nativeLocalBoundaryLabelCRTInterpreterFoldListAppendLaw
  localBoundaryWordStructuralInterface
  localBoundaryLabelToCRTEdge =
  LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordFoldComputesMappedEdgeLabelList
    localBoundaryWordStructuralInterface
    CRTMonodromy1Edge
    localBoundaryLabelToCRTEdge

crtBoundaryWordNonErasingFromShellEquality :
  {word : List CRTMonodromy1Edge} →
  word ≡ crtMonodromy3BoundaryShellWord crtMonodromyCube →
  CRTBoundaryWordIsNonErasing word
crtBoundaryWordNonErasingFromShellEquality refl =
  crtMonodromyShellWordIsNonErasing

data NativeBoundaryEdgeLabel : Set where
  nativeBoundaryEdgeP2 :
    NativeBoundaryEdgeLabel
  nativeBoundaryEdgeP3 :
    NativeBoundaryEdgeLabel
  nativeBoundaryEdgeJ :
    NativeBoundaryEdgeLabel

nativeBoundaryEdgeLabelToCRTEdge :
  NativeBoundaryEdgeLabel →
  CRTMonodromy1Edge
nativeBoundaryEdgeLabelToCRTEdge nativeBoundaryEdgeP2 = edgeP2
nativeBoundaryEdgeLabelToCRTEdge nativeBoundaryEdgeP3 = edgeP3
nativeBoundaryEdgeLabelToCRTEdge nativeBoundaryEdgeJ = edgeJ

nativeCRTBoundaryShellLabels :
  List NativeBoundaryEdgeLabel
nativeCRTBoundaryShellLabels =
  nativeBoundaryEdgeP2
  ∷ nativeBoundaryEdgeP3
  ∷ nativeBoundaryEdgeP3
  ∷ nativeBoundaryEdgeP2
  ∷ nativeBoundaryEdgeP2
  ∷ nativeBoundaryEdgeJ
  ∷ nativeBoundaryEdgeP3
  ∷ nativeBoundaryEdgeP3
  ∷ nativeBoundaryEdgeJ
  ∷ nativeBoundaryEdgeP2
  ∷ nativeBoundaryEdgeP3
  ∷ nativeBoundaryEdgeJ
  ∷ nativeBoundaryEdgeP2
  ∷ nativeBoundaryEdgeP2
  ∷ nativeBoundaryEdgeJ
  ∷ nativeBoundaryEdgeP3
  ∷ []

nativeCRTBoundaryShellLabelsInterpretAsCRTShell :
  mapList
    nativeBoundaryEdgeLabelToCRTEdge
    nativeCRTBoundaryShellLabels
  ≡
  crtMonodromy3BoundaryShellWord crtMonodromyCube
nativeCRTBoundaryShellLabelsInterpretAsCRTShell =
  refl

nativeCRTBoundaryShellLabelsAreNonErasing :
  CRTBoundaryWordIsNonErasing
    (mapList
      nativeBoundaryEdgeLabelToCRTEdge
      nativeCRTBoundaryShellLabels)
nativeCRTBoundaryShellLabelsAreNonErasing =
  crtBoundaryWordNonErasingFromShellEquality
    nativeCRTBoundaryShellLabelsInterpretAsCRTShell

record NativeBoundaryEdgeLabelCRTShellWord : Set₁ where
  field
    selectedNativeBoundaryShellLabels :
      List NativeBoundaryEdgeLabel

    selectedNativeBoundaryShellLabelsAreCanonical :
      selectedNativeBoundaryShellLabels
      ≡
      nativeCRTBoundaryShellLabels

    nativeBoundaryLabelToCRTEdge :
      NativeBoundaryEdgeLabel →
      CRTMonodromy1Edge

    nativeBoundaryLabelToCRTEdgeIsCanonical :
      nativeBoundaryLabelToCRTEdge
      ≡
      nativeBoundaryEdgeLabelToCRTEdge

    selectedNativeBoundaryShellLabelsInterpretAsCRTShell :
      mapList
        nativeBoundaryLabelToCRTEdge
        selectedNativeBoundaryShellLabels
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    selectedNativeBoundaryShellWordIsNonErasing :
      CRTBoundaryWordIsNonErasing
        (mapList
          nativeBoundaryLabelToCRTEdge
          selectedNativeBoundaryShellLabels)

    selectedNativeBoundaryShellHolonomyTrace :
      List DCRT.CRTHolonomyElement

    selectedNativeBoundaryShellHolonomyTraceIsCRTTrace :
      selectedNativeBoundaryShellHolonomyTrace
      ≡
      crtMonodromyWordHolonomyTrace
        (mapList
          nativeBoundaryLabelToCRTEdge
          selectedNativeBoundaryShellLabels)

    selectedNativeBoundaryShellAction :
      CRTBoundaryWordAction

    selectedNativeBoundaryShellActionIsCRTWordAction :
      selectedNativeBoundaryShellAction
      ≡
      crtMonodromyBoundaryWordAction
        (mapList
          nativeBoundaryLabelToCRTEdge
          selectedNativeBoundaryShellLabels)

    crtBoundaryWordFoldConcatenationInterface :
      CRTBoundaryWordFoldConcatenationInterface

    crtBoundaryWordFoldConcatenationInterfaceIsCanonical :
      crtBoundaryWordFoldConcatenationInterface
      ≡
      canonicalCRTBoundaryWordFoldConcatenationInterface

    acceptedAsGRPromotion :
      Bool

    acceptedAsGRPromotionIsFalse :
      acceptedAsGRPromotion ≡ false

    exactNativeBoundaryShellWordBoundary :
      List String

canonicalNativeBoundaryEdgeLabelCRTShellWord :
  NativeBoundaryEdgeLabelCRTShellWord
canonicalNativeBoundaryEdgeLabelCRTShellWord =
  record
    { selectedNativeBoundaryShellLabels =
        nativeCRTBoundaryShellLabels
    ; selectedNativeBoundaryShellLabelsAreCanonical =
        refl
    ; nativeBoundaryLabelToCRTEdge =
        nativeBoundaryEdgeLabelToCRTEdge
    ; nativeBoundaryLabelToCRTEdgeIsCanonical =
        refl
    ; selectedNativeBoundaryShellLabelsInterpretAsCRTShell =
        nativeCRTBoundaryShellLabelsInterpretAsCRTShell
    ; selectedNativeBoundaryShellWordIsNonErasing =
        nativeCRTBoundaryShellLabelsAreNonErasing
    ; selectedNativeBoundaryShellHolonomyTrace =
        crtMonodromyWordHolonomyTrace
          (mapList
            nativeBoundaryEdgeLabelToCRTEdge
            nativeCRTBoundaryShellLabels)
    ; selectedNativeBoundaryShellHolonomyTraceIsCRTTrace =
        refl
    ; selectedNativeBoundaryShellAction =
        crtMonodromyBoundaryWordAction
          (mapList
            nativeBoundaryEdgeLabelToCRTEdge
            nativeCRTBoundaryShellLabels)
    ; selectedNativeBoundaryShellActionIsCRTWordAction =
        refl
    ; crtBoundaryWordFoldConcatenationInterface =
        canonicalCRTBoundaryWordFoldConcatenationInterface
    ; crtBoundaryWordFoldConcatenationInterfaceIsCanonical =
        refl
    ; acceptedAsGRPromotion =
        false
    ; acceptedAsGRPromotionIsFalse =
        refl
    ; exactNativeBoundaryShellWordBoundary =
        "NativeBoundaryEdgeLabel has explicit edgeP2 edgeP3 edgeJ constructors"
        ∷ "The canonical native shell label list maps definitionally to crtMonodromy3BoundaryShellWord crtMonodromyCube"
        ∷ "The canonical native shell inherits the CRT non-erasing shell witness"
        ∷ "The CRT-side holonomy trace and word action are computed by the existing CRT word folds"
        ∷ "This native CRT shell word is not by itself a local Stokes BoundaryWordAtDepth or GR promotion"
        ∷ []
    }

data GenericBoundaryEdge : Set where
  genericBoundaryEdgeP2 :
    GenericBoundaryEdge
  genericBoundaryEdgeP3 :
    GenericBoundaryEdge
  genericBoundaryEdgeJ :
    GenericBoundaryEdge

genericBoundaryEdgeToCRTEdge :
  GenericBoundaryEdge →
  CRTMonodromy1Edge
genericBoundaryEdgeToCRTEdge genericBoundaryEdgeP2 = edgeP2
genericBoundaryEdgeToCRTEdge genericBoundaryEdgeP3 = edgeP3
genericBoundaryEdgeToCRTEdge genericBoundaryEdgeJ = edgeJ

genericBoundaryEdgeToNativeBoundaryEdgeLabel :
  GenericBoundaryEdge →
  NativeBoundaryEdgeLabel
genericBoundaryEdgeToNativeBoundaryEdgeLabel genericBoundaryEdgeP2 =
  nativeBoundaryEdgeP2
genericBoundaryEdgeToNativeBoundaryEdgeLabel genericBoundaryEdgeP3 =
  nativeBoundaryEdgeP3
genericBoundaryEdgeToNativeBoundaryEdgeLabel genericBoundaryEdgeJ =
  nativeBoundaryEdgeJ

nativeBoundaryEdgeLabelToGenericBoundaryEdge :
  NativeBoundaryEdgeLabel →
  GenericBoundaryEdge
nativeBoundaryEdgeLabelToGenericBoundaryEdge nativeBoundaryEdgeP2 =
  genericBoundaryEdgeP2
nativeBoundaryEdgeLabelToGenericBoundaryEdge nativeBoundaryEdgeP3 =
  genericBoundaryEdgeP3
nativeBoundaryEdgeLabelToGenericBoundaryEdge nativeBoundaryEdgeJ =
  genericBoundaryEdgeJ

genericBoundaryEdgeToNativeToGenericRoundTrip :
  (edge : GenericBoundaryEdge) →
  nativeBoundaryEdgeLabelToGenericBoundaryEdge
    (genericBoundaryEdgeToNativeBoundaryEdgeLabel edge)
  ≡
  edge
genericBoundaryEdgeToNativeToGenericRoundTrip genericBoundaryEdgeP2 = refl
genericBoundaryEdgeToNativeToGenericRoundTrip genericBoundaryEdgeP3 = refl
genericBoundaryEdgeToNativeToGenericRoundTrip genericBoundaryEdgeJ = refl

nativeBoundaryEdgeLabelToGenericToNativeRoundTrip :
  (label : NativeBoundaryEdgeLabel) →
  genericBoundaryEdgeToNativeBoundaryEdgeLabel
    (nativeBoundaryEdgeLabelToGenericBoundaryEdge label)
  ≡
  label
nativeBoundaryEdgeLabelToGenericToNativeRoundTrip nativeBoundaryEdgeP2 = refl
nativeBoundaryEdgeLabelToGenericToNativeRoundTrip nativeBoundaryEdgeP3 = refl
nativeBoundaryEdgeLabelToGenericToNativeRoundTrip nativeBoundaryEdgeJ = refl

genericBoundaryEdgeToNativeCRTEdgeCommutes :
  (edge : GenericBoundaryEdge) →
  nativeBoundaryEdgeLabelToCRTEdge
    (genericBoundaryEdgeToNativeBoundaryEdgeLabel edge)
  ≡
  genericBoundaryEdgeToCRTEdge edge
genericBoundaryEdgeToNativeCRTEdgeCommutes genericBoundaryEdgeP2 = refl
genericBoundaryEdgeToNativeCRTEdgeCommutes genericBoundaryEdgeP3 = refl
genericBoundaryEdgeToNativeCRTEdgeCommutes genericBoundaryEdgeJ = refl

nativeBoundaryEdgeLabelToGenericCRTEdgeCommutes :
  (label : NativeBoundaryEdgeLabel) →
  genericBoundaryEdgeToCRTEdge
    (nativeBoundaryEdgeLabelToGenericBoundaryEdge label)
  ≡
  nativeBoundaryEdgeLabelToCRTEdge label
nativeBoundaryEdgeLabelToGenericCRTEdgeCommutes nativeBoundaryEdgeP2 = refl
nativeBoundaryEdgeLabelToGenericCRTEdgeCommutes nativeBoundaryEdgeP3 = refl
nativeBoundaryEdgeLabelToGenericCRTEdgeCommutes nativeBoundaryEdgeJ = refl

genericBoundaryEdgeP2≢P3 :
  genericBoundaryEdgeP2 ≢ genericBoundaryEdgeP3
genericBoundaryEdgeP2≢P3 ()

nativeBoundaryEdgeP2≢P3 :
  nativeBoundaryEdgeP2 ≢ nativeBoundaryEdgeP3
nativeBoundaryEdgeP2≢P3 ()

genericCRTBoundaryShellEdges :
  List GenericBoundaryEdge
genericCRTBoundaryShellEdges =
  genericBoundaryEdgeP2
  ∷ genericBoundaryEdgeP3
  ∷ genericBoundaryEdgeP3
  ∷ genericBoundaryEdgeP2
  ∷ genericBoundaryEdgeP2
  ∷ genericBoundaryEdgeJ
  ∷ genericBoundaryEdgeP3
  ∷ genericBoundaryEdgeP3
  ∷ genericBoundaryEdgeJ
  ∷ genericBoundaryEdgeP2
  ∷ genericBoundaryEdgeP3
  ∷ genericBoundaryEdgeJ
  ∷ genericBoundaryEdgeP2
  ∷ genericBoundaryEdgeP2
  ∷ genericBoundaryEdgeJ
  ∷ genericBoundaryEdgeP3
  ∷ []

genericCRTBoundaryShellEdgesInterpretAsCRTShell :
  mapList
    genericBoundaryEdgeToCRTEdge
    genericCRTBoundaryShellEdges
  ≡
  crtMonodromy3BoundaryShellWord crtMonodromyCube
genericCRTBoundaryShellEdgesInterpretAsCRTShell =
  refl

genericCRTBoundaryShellEdgesMapToNativeShell :
  mapList
    genericBoundaryEdgeToNativeBoundaryEdgeLabel
    genericCRTBoundaryShellEdges
  ≡
  nativeCRTBoundaryShellLabels
genericCRTBoundaryShellEdgesMapToNativeShell =
  refl

genericCRTBoundaryShellEdgesAreNonErasing :
  CRTBoundaryWordIsNonErasing
    (mapList
      genericBoundaryEdgeToCRTEdge
      genericCRTBoundaryShellEdges)
genericCRTBoundaryShellEdgesAreNonErasing =
  crtBoundaryWordNonErasingFromShellEquality
    genericCRTBoundaryShellEdgesInterpretAsCRTShell

record NativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism : Set₁ where
  field
    toGenericBoundaryEdge :
      NativeBoundaryEdgeLabel →
      GenericBoundaryEdge

    toGenericBoundaryEdgeIsCanonical :
      toGenericBoundaryEdge
      ≡
      nativeBoundaryEdgeLabelToGenericBoundaryEdge

    fromGenericBoundaryEdge :
      GenericBoundaryEdge →
      NativeBoundaryEdgeLabel

    fromGenericBoundaryEdgeIsCanonical :
      fromGenericBoundaryEdge
      ≡
      genericBoundaryEdgeToNativeBoundaryEdgeLabel

    genericRoundTrip :
      (edge : GenericBoundaryEdge) →
      toGenericBoundaryEdge (fromGenericBoundaryEdge edge)
      ≡
      edge

    nativeRoundTrip :
      (label : NativeBoundaryEdgeLabel) →
      fromGenericBoundaryEdge (toGenericBoundaryEdge label)
      ≡
      label

    genericToCRTCommutesWithNative :
      (edge : GenericBoundaryEdge) →
      nativeBoundaryEdgeLabelToCRTEdge
        (fromGenericBoundaryEdge edge)
      ≡
      genericBoundaryEdgeToCRTEdge edge

    nativeToCRTCommutesWithGeneric :
      (label : NativeBoundaryEdgeLabel) →
      genericBoundaryEdgeToCRTEdge
        (toGenericBoundaryEdge label)
      ≡
      nativeBoundaryEdgeLabelToCRTEdge label

    selectedGenericShellMapsToNativeShell :
      mapList
        fromGenericBoundaryEdge
        genericCRTBoundaryShellEdges
      ≡
      nativeCRTBoundaryShellLabels

    genericP2P3Distinct :
      genericBoundaryEdgeP2 ≢ genericBoundaryEdgeP3

    nativeP2P3Distinct :
      nativeBoundaryEdgeP2 ≢ nativeBoundaryEdgeP3

    acceptedAsLocalBoundaryEdgeRealization :
      Bool

    acceptedAsLocalBoundaryEdgeRealizationIsFalse :
      acceptedAsLocalBoundaryEdgeRealization ≡ false

    exactIsomorphismBoundary :
      List String

canonicalNativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism :
  NativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism
canonicalNativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism =
  record
    { toGenericBoundaryEdge =
        nativeBoundaryEdgeLabelToGenericBoundaryEdge
    ; toGenericBoundaryEdgeIsCanonical =
        refl
    ; fromGenericBoundaryEdge =
        genericBoundaryEdgeToNativeBoundaryEdgeLabel
    ; fromGenericBoundaryEdgeIsCanonical =
        refl
    ; genericRoundTrip =
        genericBoundaryEdgeToNativeToGenericRoundTrip
    ; nativeRoundTrip =
        nativeBoundaryEdgeLabelToGenericToNativeRoundTrip
    ; genericToCRTCommutesWithNative =
        genericBoundaryEdgeToNativeCRTEdgeCommutes
    ; nativeToCRTCommutesWithGeneric =
        nativeBoundaryEdgeLabelToGenericCRTEdgeCommutes
    ; selectedGenericShellMapsToNativeShell =
        genericCRTBoundaryShellEdgesMapToNativeShell
    ; genericP2P3Distinct =
        genericBoundaryEdgeP2≢P3
    ; nativeP2P3Distinct =
        nativeBoundaryEdgeP2≢P3
    ; acceptedAsLocalBoundaryEdgeRealization =
        false
    ; acceptedAsLocalBoundaryEdgeRealizationIsFalse =
        refl
    ; exactIsomorphismBoundary =
        "NativeBoundaryEdgeLabel and GenericBoundaryEdge are isomorphic over the three P2/P3/J constructors"
        ∷ "Both directions commute with the CRTMonodromy1Edge interpretation"
        ∷ "P2 and P3 are distinct constructors, preserving the p=2 versus p=3 non-degeneracy of the boundary directions"
        ∷ "The selected generic shell maps definitionally to nativeCRTBoundaryShellLabels"
        ∷ "This isomorphism is between native/generic shell labels only"
        ∷ "It does not realize either label type inside an arbitrary LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel carrier"
        ∷ []
    }

record GenericBoundaryEdgeCRTShellCompatibility : Set₁ where
  field
    selectedGenericBoundaryShellEdges :
      List GenericBoundaryEdge

    selectedGenericBoundaryShellEdgesAreCanonical :
      selectedGenericBoundaryShellEdges
      ≡
      genericCRTBoundaryShellEdges

    genericBoundaryEdgeToCRT :
      GenericBoundaryEdge →
      CRTMonodromy1Edge

    genericBoundaryEdgeToCRTIsCanonical :
      genericBoundaryEdgeToCRT
      ≡
      genericBoundaryEdgeToCRTEdge

    selectedGenericBoundaryShellEdgesInterpretAsCRTShell :
      mapList
        genericBoundaryEdgeToCRT
        selectedGenericBoundaryShellEdges
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    selectedGenericBoundaryShellEdgesAreNonErasing :
      CRTBoundaryWordIsNonErasing
        (mapList
          genericBoundaryEdgeToCRT
          selectedGenericBoundaryShellEdges)

    selectedGenericBoundaryShellEdgesMapToNativeShell :
      mapList
        genericBoundaryEdgeToNativeBoundaryEdgeLabel
        selectedGenericBoundaryShellEdges
      ≡
      nativeCRTBoundaryShellLabels

    nativeBoundaryEdgeLabelCRTShellWord :
      NativeBoundaryEdgeLabelCRTShellWord

    nativeBoundaryEdgeLabelCRTShellWordIsCanonical :
      nativeBoundaryEdgeLabelCRTShellWord
      ≡
      canonicalNativeBoundaryEdgeLabelCRTShellWord

    acceptedAsGRPromotion :
      Bool

    acceptedAsGRPromotionIsFalse :
      acceptedAsGRPromotion ≡ false

    exactGenericBoundaryEdgeCompatibilityBoundary :
      List String

canonicalGenericBoundaryEdgeCRTShellCompatibility :
  GenericBoundaryEdgeCRTShellCompatibility
canonicalGenericBoundaryEdgeCRTShellCompatibility =
  record
    { selectedGenericBoundaryShellEdges =
        genericCRTBoundaryShellEdges
    ; selectedGenericBoundaryShellEdgesAreCanonical =
        refl
    ; genericBoundaryEdgeToCRT =
        genericBoundaryEdgeToCRTEdge
    ; genericBoundaryEdgeToCRTIsCanonical =
        refl
    ; selectedGenericBoundaryShellEdgesInterpretAsCRTShell =
        genericCRTBoundaryShellEdgesInterpretAsCRTShell
    ; selectedGenericBoundaryShellEdgesAreNonErasing =
        genericCRTBoundaryShellEdgesAreNonErasing
    ; selectedGenericBoundaryShellEdgesMapToNativeShell =
        genericCRTBoundaryShellEdgesMapToNativeShell
    ; nativeBoundaryEdgeLabelCRTShellWord =
        canonicalNativeBoundaryEdgeLabelCRTShellWord
    ; nativeBoundaryEdgeLabelCRTShellWordIsCanonical =
        refl
    ; acceptedAsGRPromotion =
        false
    ; acceptedAsGRPromotionIsFalse =
        refl
    ; exactGenericBoundaryEdgeCompatibilityBoundary =
        "GenericBoundaryEdge supplies P2 P3 J constructors independent of the local BoundaryWordAtDepth label carrier"
        ∷ "The generic P2/P3/J map to CRTMonodromy1Edge labels definitionally"
        ∷ "The selected generic shell word maps definitionally to crtMonodromy3BoundaryShellWord crtMonodromyCube"
        ∷ "The selected generic shell word also maps to the existing NativeBoundaryEdgeLabel shell word"
        ∷ "This bridges the user-supplied generic edge formalism into the native CRT shell receipt"
        ∷ "It still does not construct values of arbitrary LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel"
        ∷ "A supplied NativeBoundaryEdgeLabelLocalRealization or equivalent generic-to-local realization remains required for a local selected shell word"
        ∷ []
    }

data NativeLocalBoundaryLabelCRTCompatibilityRequiredField : Set where
  requiredLocalBoundaryLabelToCRTEdge :
    NativeLocalBoundaryLabelCRTCompatibilityRequiredField
  requiredSelectedLocalBoundaryShellLabelList :
    NativeLocalBoundaryLabelCRTCompatibilityRequiredField
  requiredSelectedLocalBoundaryShellLabelsInterpretAsCRTShell :
    NativeLocalBoundaryLabelCRTCompatibilityRequiredField

canonicalNativeLocalBoundaryLabelCRTCompatibilityRequiredFields :
  List NativeLocalBoundaryLabelCRTCompatibilityRequiredField
canonicalNativeLocalBoundaryLabelCRTCompatibilityRequiredFields =
  requiredLocalBoundaryLabelToCRTEdge
  ∷ requiredSelectedLocalBoundaryShellLabelList
  ∷ requiredSelectedLocalBoundaryShellLabelsInterpretAsCRTShell
  ∷ []

record FinalNativeLocalBoundaryLabelCRTCompatibilityRequest : Set where
  field
    requestName :
      String

    sourceStructuralInterfaceName :
      String

    compatibilityRecordName :
      String

    unlockedPrimitiveConstructorName :
      String

    requiredFields :
      List NativeLocalBoundaryLabelCRTCompatibilityRequiredField

    requiredFieldsAreCanonical :
      requiredFields
      ≡
      canonicalNativeLocalBoundaryLabelCRTCompatibilityRequiredFields

    firstRequiredField :
      NativeLocalBoundaryLabelCRTCompatibilityRequiredField

    firstRequiredFieldIsLabelToCRTEdge :
      firstRequiredField
      ≡
      requiredLocalBoundaryLabelToCRTEdge

    localWordSyntaxAvailable :
      Bool

    localWordSyntaxAvailableIsTrue :
      localWordSyntaxAvailable ≡ true

    acceptedAsGRPromotion :
      Bool

    acceptedAsGRPromotionIsFalse :
      acceptedAsGRPromotion ≡ false

    exactFinalCompatibilityBoundary :
      List String

canonicalFinalNativeLocalBoundaryLabelCRTCompatibilityRequest :
  FinalNativeLocalBoundaryLabelCRTCompatibilityRequest
canonicalFinalNativeLocalBoundaryLabelCRTCompatibilityRequest =
  record
    { requestName =
        "FinalNativeLocalBoundaryLabelCRTCompatibility"
    ; sourceStructuralInterfaceName =
        "LocalBoundaryWordAtDepthStructuralInterface"
    ; compatibilityRecordName =
        "NativeLocalBoundaryLabelShellSelection"
    ; unlockedPrimitiveConstructorName =
        "localToCRTBoundaryWordSemanticAlignmentPrimitiveFromNativeLabelCompatibility"
    ; requiredFields =
        canonicalNativeLocalBoundaryLabelCRTCompatibilityRequiredFields
    ; requiredFieldsAreCanonical =
        refl
    ; firstRequiredField =
        requiredLocalBoundaryLabelToCRTEdge
    ; firstRequiredFieldIsLabelToCRTEdge =
        refl
    ; localWordSyntaxAvailable =
        true
    ; localWordSyntaxAvailableIsTrue =
        refl
    ; acceptedAsGRPromotion =
        false
    ; acceptedAsGRPromotionIsFalse =
        refl
    ; exactFinalCompatibilityBoundary =
        "Native local boundary-edge labels are available through LocalBoundaryWordAtDepthStructuralInterface"
        ∷ "The missing CRT compatibility is a map from each native local boundary label to CRTMonodromy1Edge"
        ∷ "A selected native boundary-label list must be supplied for the CRT monodromy cube"
        ∷ "Mapping that selected native label list must produce crtMonodromy3BoundaryShellWord crtMonodromyCube"
        ∷ "The selected BoundaryWordAtDepth, non-erasing shell witness, append law, and fold/list law are then derived from native constructors"
        ∷ "This request is only the final interface; it is not a GR, Clay, or terminal promotion"
        ∷ []
    }

record NativeLocalBoundaryLabelToCRTCompatibility
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface)
  (depth : Nat)
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth)
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) :
  Set₁ where
  field
    localBoundaryLabelToCRTEdge :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface →
      CRTMonodromy1Edge

    selectedLocalBoundaryWordForCRTMonodromyCube :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop

    selectedLocalBoundaryWordLabelsInterpretAsCRTShell :
      nativeLocalBoundaryLabelCRTInterpreter
        localBoundaryWordStructuralInterface
        localBoundaryLabelToCRTEdge
        selectedLocalBoundaryWordForCRTMonodromyCube
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    selectedLocalBoundaryWordLabelsAreNonErasing :
      CRTBoundaryWordIsNonErasing
        (nativeLocalBoundaryLabelCRTInterpreter
          localBoundaryWordStructuralInterface
          localBoundaryLabelToCRTEdge
          selectedLocalBoundaryWordForCRTMonodromyCube)

    localFoldComputesCRTListAppendAfterLabelInterpretation :
      LocalBoundaryWordFoldComputesCRTListAppendLawType
        localStokesSurface
        depth
        stokesLoop
        localBoundaryWordStructuralInterface
        (nativeLocalBoundaryLabelCRTInterpreter
          localBoundaryWordStructuralInterface
          localBoundaryLabelToCRTEdge)

    finalCompatibilityRequest :
      FinalNativeLocalBoundaryLabelCRTCompatibilityRequest

    finalCompatibilityRequestIsCanonical :
      finalCompatibilityRequest
      ≡
      canonicalFinalNativeLocalBoundaryLabelCRTCompatibilityRequest

    exactCRTLabelCompatibilityBoundary :
      List String

record NativeLocalBoundaryLabelShellSelection
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface)
  (depth : Nat)
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth)
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) :
  Set₁ where
  field
    localBoundaryLabelToCRTEdge :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface →
      CRTMonodromy1Edge

    selectedLocalBoundaryShellLabels :
      List
        (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
          localBoundaryWordStructuralInterface)

    selectedLocalBoundaryShellLabelsInterpretAsCRTShell :
      mapList
        localBoundaryLabelToCRTEdge
        selectedLocalBoundaryShellLabels
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    finalCompatibilityRequest :
      FinalNativeLocalBoundaryLabelCRTCompatibilityRequest

    finalCompatibilityRequestIsCanonical :
      finalCompatibilityRequest
      ≡
      canonicalFinalNativeLocalBoundaryLabelCRTCompatibilityRequest

    exactShellSelectionBoundary :
      List String

record NativeBoundaryEdgeLabelLocalRealization
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface)
  (depth : Nat)
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth)
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) :
  Set₁ where
  field
    nativeBoundaryEdgeLabelToLocalBoundaryLabel :
      NativeBoundaryEdgeLabel →
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface

    localBoundaryLabelToCRTEdge :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface →
      CRTMonodromy1Edge

    nativeBoundaryEdgeLabelLocalRealizationCommutesWithCRT :
      (label : NativeBoundaryEdgeLabel) →
      localBoundaryLabelToCRTEdge
        (nativeBoundaryEdgeLabelToLocalBoundaryLabel label)
      ≡
      nativeBoundaryEdgeLabelToCRTEdge label

    nativeBoundaryEdgeLabelCRTShellWord :
      NativeBoundaryEdgeLabelCRTShellWord

    nativeBoundaryEdgeLabelCRTShellWordIsCanonical :
      nativeBoundaryEdgeLabelCRTShellWord
      ≡
      canonicalNativeBoundaryEdgeLabelCRTShellWord

    acceptedAsGRPromotion :
      Bool

    acceptedAsGRPromotionIsFalse :
      acceptedAsGRPromotion ≡ false

    exactNativeBoundaryEdgeLabelLocalRealizationBoundary :
      List String

record LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface)
  (depth : Nat)
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth)
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) :
  Set₁ where
  field
    genericBoundaryEdgeToLocalBoundaryLabel :
      GenericBoundaryEdge →
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface

    localBoundaryLabelToGenericBoundaryEdge :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface →
      GenericBoundaryEdge

    genericBoundaryEdgeRoundTrip :
      (edge : GenericBoundaryEdge) →
      localBoundaryLabelToGenericBoundaryEdge
        (genericBoundaryEdgeToLocalBoundaryLabel edge)
      ≡
      edge

    localBoundaryLabelToCRTEdge :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface →
      CRTMonodromy1Edge

    localBoundaryLabelToCRTEdgeIsGenericInterpretation :
      (label :
        LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
          localBoundaryWordStructuralInterface) →
      localBoundaryLabelToCRTEdge label
      ≡
      genericBoundaryEdgeToCRTEdge
        (localBoundaryLabelToGenericBoundaryEdge label)

    selectedGenericBoundaryShellLocalPreimage :
      List
        (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
          localBoundaryWordStructuralInterface)

    selectedGenericBoundaryShellLocalPreimageIsCanonical :
      selectedGenericBoundaryShellLocalPreimage
      ≡
      mapList
        genericBoundaryEdgeToLocalBoundaryLabel
        genericCRTBoundaryShellEdges

    selectedGenericBoundaryShellLocalPreimageMapsToCRTShell :
      mapList
        localBoundaryLabelToCRTEdge
        selectedGenericBoundaryShellLocalPreimage
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    selectedGenericBoundaryShellLocalPreimageIsNonErasing :
      CRTBoundaryWordIsNonErasing
        (mapList
          localBoundaryLabelToCRTEdge
          selectedGenericBoundaryShellLocalPreimage)

    nativeGenericIsomorphism :
      NativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism

    nativeGenericIsomorphismIsCanonical :
      nativeGenericIsomorphism
      ≡
      canonicalNativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism

    acceptedAsCRTStokesSpecialisation :
      Bool

    acceptedAsCRTStokesSpecialisationIsFalse :
      acceptedAsCRTStokesSpecialisation ≡ false

    exactEmbeddingBoundary :
      List String

localBoundaryEdgeLabelGenericEmbeddingSelectedLabelsInterpretAsCRTShell :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  (genericBoundaryEdgeToLocalBoundaryLabel :
    GenericBoundaryEdge →
    LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
      localBoundaryWordStructuralInterface) →
  (localBoundaryLabelToGenericBoundaryEdge :
    LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
      localBoundaryWordStructuralInterface →
    GenericBoundaryEdge) →
  ((edge : GenericBoundaryEdge) →
    localBoundaryLabelToGenericBoundaryEdge
      (genericBoundaryEdgeToLocalBoundaryLabel edge)
    ≡
    edge) →
  mapList
    (λ label →
      genericBoundaryEdgeToCRTEdge
        (localBoundaryLabelToGenericBoundaryEdge label))
    (mapList
      genericBoundaryEdgeToLocalBoundaryLabel
      genericCRTBoundaryShellEdges)
  ≡
  crtMonodromy3BoundaryShellWord crtMonodromyCube
localBoundaryEdgeLabelGenericEmbeddingSelectedLabelsInterpretAsCRTShell
  localBoundaryWordStructuralInterface
  genericBoundaryEdgeToLocalBoundaryLabel
  localBoundaryLabelToGenericBoundaryEdge
  genericBoundaryEdgeRoundTrip =
  trans
    (mapListCompose
      (λ label →
        genericBoundaryEdgeToCRTEdge
          (localBoundaryLabelToGenericBoundaryEdge label))
      genericBoundaryEdgeToLocalBoundaryLabel
      genericCRTBoundaryShellEdges)
    (trans
      (mapListPointwise
        (λ edge →
          genericBoundaryEdgeToCRTEdge
            (localBoundaryLabelToGenericBoundaryEdge
              (genericBoundaryEdgeToLocalBoundaryLabel edge)))
        genericBoundaryEdgeToCRTEdge
        (λ edge →
          cong
            genericBoundaryEdgeToCRTEdge
            (genericBoundaryEdgeRoundTrip edge))
        genericCRTBoundaryShellEdges)
      genericCRTBoundaryShellEdgesInterpretAsCRTShell)

localBoundaryEdgeLabelGenericEmbeddingToNativeBoundaryEdgeLabelLocalRealization :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface →
  NativeBoundaryEdgeLabelLocalRealization
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface
localBoundaryEdgeLabelGenericEmbeddingToNativeBoundaryEdgeLabelLocalRealization
  localBoundaryWordStructuralInterface
  embedding =
  record
    { nativeBoundaryEdgeLabelToLocalBoundaryLabel =
        λ label →
          genericBoundaryEdgeToLocalBoundaryLabel
            (nativeBoundaryEdgeLabelToGenericBoundaryEdge label)
    ; localBoundaryLabelToCRTEdge =
        localBoundaryLabelToCRTEdge
    ; nativeBoundaryEdgeLabelLocalRealizationCommutesWithCRT =
        λ label →
          trans
            (trans
              (localBoundaryLabelToCRTEdgeIsGenericInterpretation
                (genericBoundaryEdgeToLocalBoundaryLabel
                  (nativeBoundaryEdgeLabelToGenericBoundaryEdge label)))
              (cong
                genericBoundaryEdgeToCRTEdge
                (genericBoundaryEdgeRoundTrip
                  (nativeBoundaryEdgeLabelToGenericBoundaryEdge label))))
            (nativeBoundaryEdgeLabelToGenericCRTEdgeCommutes label)
    ; nativeBoundaryEdgeLabelCRTShellWord =
        canonicalNativeBoundaryEdgeLabelCRTShellWord
    ; nativeBoundaryEdgeLabelCRTShellWordIsCanonical =
        refl
    ; acceptedAsGRPromotion =
        false
    ; acceptedAsGRPromotionIsFalse =
        refl
    ; exactNativeBoundaryEdgeLabelLocalRealizationBoundary =
        "A supplied LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding realizes generic P2/P3/J labels inside the local label carrier"
        ∷ "The generic round-trip proves the realized generic labels keep their intended P2/P3/J identity"
        ∷ "The local label-to-CRT map is required to be the generic CRT interpretation"
        ∷ "NativeBoundaryEdgeLabel realizes through the native-to-generic isomorphism and the supplied generic local embedding"
        ∷ "This derives only NativeBoundaryEdgeLabelLocalRealization evidence; it is not a CRT Stokes or Bianchi proof"
        ∷ []
    }
  where
    genericBoundaryEdgeToLocalBoundaryLabel :
      GenericBoundaryEdge →
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface
    genericBoundaryEdgeToLocalBoundaryLabel =
      LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding.genericBoundaryEdgeToLocalBoundaryLabel
        embedding

    localBoundaryLabelToCRTEdge :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface →
      CRTMonodromy1Edge
    localBoundaryLabelToCRTEdge =
      LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding.localBoundaryLabelToCRTEdge
        embedding

    localBoundaryLabelToCRTEdgeIsGenericInterpretation :
      (label :
        LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
          localBoundaryWordStructuralInterface) →
      localBoundaryLabelToCRTEdge label
      ≡
      genericBoundaryEdgeToCRTEdge
        (LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding.localBoundaryLabelToGenericBoundaryEdge
          embedding
          label)
    localBoundaryLabelToCRTEdgeIsGenericInterpretation =
      LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding.localBoundaryLabelToCRTEdgeIsGenericInterpretation
        embedding

    genericBoundaryEdgeRoundTrip :
      (edge : GenericBoundaryEdge) →
      LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding.localBoundaryLabelToGenericBoundaryEdge
        embedding
        (genericBoundaryEdgeToLocalBoundaryLabel edge)
      ≡
      edge
    genericBoundaryEdgeRoundTrip =
      LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding.genericBoundaryEdgeRoundTrip
        embedding

nativeBoundaryEdgeLabelLocalRealizationSelectedLocalBoundaryShellLabels :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  NativeBoundaryEdgeLabelLocalRealization
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface →
  List
    (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
      localBoundaryWordStructuralInterface)
nativeBoundaryEdgeLabelLocalRealizationSelectedLocalBoundaryShellLabels
  localBoundaryWordStructuralInterface
  realization =
  mapList
    (NativeBoundaryEdgeLabelLocalRealization.nativeBoundaryEdgeLabelToLocalBoundaryLabel
      realization)
    nativeCRTBoundaryShellLabels

nativeBoundaryEdgeLabelLocalRealizationSelectedLabelsInterpretAsCRTShell :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  (realization :
    NativeBoundaryEdgeLabelLocalRealization
      localStokesSurface
      depth
      stokesLoop
      localBoundaryWordStructuralInterface) →
  mapList
    (NativeBoundaryEdgeLabelLocalRealization.localBoundaryLabelToCRTEdge
      realization)
    (nativeBoundaryEdgeLabelLocalRealizationSelectedLocalBoundaryShellLabels
      localBoundaryWordStructuralInterface
      realization)
  ≡
  crtMonodromy3BoundaryShellWord crtMonodromyCube
nativeBoundaryEdgeLabelLocalRealizationSelectedLabelsInterpretAsCRTShell
  localBoundaryWordStructuralInterface
  realization =
  trans
    (mapListCompose
      localBoundaryLabelToCRTEdge
      nativeBoundaryEdgeLabelToLocalBoundaryLabel
      nativeCRTBoundaryShellLabels)
    (trans
      (mapListPointwise
        (λ label →
          localBoundaryLabelToCRTEdge
            (nativeBoundaryEdgeLabelToLocalBoundaryLabel label))
        nativeBoundaryEdgeLabelToCRTEdge
        nativeBoundaryEdgeLabelLocalRealizationCommutesWithCRT
        nativeCRTBoundaryShellLabels)
      nativeCRTBoundaryShellLabelsInterpretAsCRTShell)
  where
    nativeBoundaryEdgeLabelToLocalBoundaryLabel :
      NativeBoundaryEdgeLabel →
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface
    nativeBoundaryEdgeLabelToLocalBoundaryLabel =
      NativeBoundaryEdgeLabelLocalRealization.nativeBoundaryEdgeLabelToLocalBoundaryLabel
        realization

    localBoundaryLabelToCRTEdge :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface →
      CRTMonodromy1Edge
    localBoundaryLabelToCRTEdge =
      NativeBoundaryEdgeLabelLocalRealization.localBoundaryLabelToCRTEdge
        realization

    nativeBoundaryEdgeLabelLocalRealizationCommutesWithCRT :
      (label : NativeBoundaryEdgeLabel) →
      localBoundaryLabelToCRTEdge
        (nativeBoundaryEdgeLabelToLocalBoundaryLabel label)
      ≡
      nativeBoundaryEdgeLabelToCRTEdge label
    nativeBoundaryEdgeLabelLocalRealizationCommutesWithCRT =
      NativeBoundaryEdgeLabelLocalRealization.nativeBoundaryEdgeLabelLocalRealizationCommutesWithCRT
        realization

nativeLocalBoundaryLabelShellSelectionFromNativeBoundaryEdgeLabelLocalRealization :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  NativeBoundaryEdgeLabelLocalRealization
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface →
  NativeLocalBoundaryLabelShellSelection
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface
nativeLocalBoundaryLabelShellSelectionFromNativeBoundaryEdgeLabelLocalRealization
  localBoundaryWordStructuralInterface
  realization =
  record
    { localBoundaryLabelToCRTEdge =
        NativeBoundaryEdgeLabelLocalRealization.localBoundaryLabelToCRTEdge
          realization
    ; selectedLocalBoundaryShellLabels =
        nativeBoundaryEdgeLabelLocalRealizationSelectedLocalBoundaryShellLabels
          localBoundaryWordStructuralInterface
          realization
    ; selectedLocalBoundaryShellLabelsInterpretAsCRTShell =
        nativeBoundaryEdgeLabelLocalRealizationSelectedLabelsInterpretAsCRTShell
          localBoundaryWordStructuralInterface
          realization
    ; finalCompatibilityRequest =
        canonicalFinalNativeLocalBoundaryLabelCRTCompatibilityRequest
    ; finalCompatibilityRequestIsCanonical =
        refl
    ; exactShellSelectionBoundary =
        "The selected local shell label list is the native CRT shell list realized into local boundary labels"
        ∷ "The supplied local label-to-CRT map is required to commute with nativeBoundaryEdgeLabelToCRTEdge on realized native labels"
        ∷ "Map composition and pointwise commutation identify the selected local labels with the CRT shell word"
        ∷ "This constructs NativeLocalBoundaryLabelShellSelection from supplied realization evidence only"
        ∷ "It does not promote the local Stokes surface to a GR or cyclic Bianchi theorem"
        ∷ []
    }

constantLocalBoundaryLabelToCRTEdgeFallback :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
    localBoundaryWordStructuralInterface →
  CRTMonodromy1Edge
constantLocalBoundaryLabelToCRTEdgeFallback _ _ =
  edgeP2

data NativeLocalBoundaryLabelShellSelectionCurrentDataAbsence : Set where
  missingNativeLocalBoundaryLabelCRTEdgeSemanticConstructor :
    NativeLocalBoundaryLabelShellSelectionCurrentDataAbsence
  missingSelectedNativeLocalBoundaryShellLabelListConstructor :
    NativeLocalBoundaryLabelShellSelectionCurrentDataAbsence
  missingSelectedNativeLocalBoundaryShellLabelsInterpretAsCRTShellEquality :
    NativeLocalBoundaryLabelShellSelectionCurrentDataAbsence

canonicalNativeLocalBoundaryLabelShellSelectionCurrentDataAbsence :
  List NativeLocalBoundaryLabelShellSelectionCurrentDataAbsence
canonicalNativeLocalBoundaryLabelShellSelectionCurrentDataAbsence =
  missingNativeLocalBoundaryLabelCRTEdgeSemanticConstructor
  ∷ missingSelectedNativeLocalBoundaryShellLabelListConstructor
  ∷ missingSelectedNativeLocalBoundaryShellLabelsInterpretAsCRTShellEquality
  ∷ []

record NativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger :
  Set₁ where
  field
    attemptedRecordName :
      String

    attemptedMapFieldName :
      String

    attemptedMapTypeName :
      String

    attemptedSelectedLabelListFieldName :
      String

    absentSemanticEqualityName :
      String

    absentNativeConstructorName :
      String

    targetCRTShellWord :
      List CRTMonodromy1Edge

    targetCRTShellWordIsCanonical :
      targetCRTShellWord
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    targetCRTShellWordIsNonErasing :
      CRTBoundaryWordIsNonErasing targetCRTShellWord

    nativeLabelListSyntaxAvailable :
      Bool

    nativeLabelListSyntaxAvailableIsTrue :
      nativeLabelListSyntaxAvailable ≡ true

    constantLocalBoundaryLabelToCRTEdgeFallbackAvailable :
      Bool

    constantLocalBoundaryLabelToCRTEdgeFallbackAvailableIsTrue :
      constantLocalBoundaryLabelToCRTEdgeFallbackAvailable ≡ true

    constantLocalBoundaryLabelToCRTEdgeFallbackAcceptedAsShellSemanticMap :
      Bool

    constantLocalBoundaryLabelToCRTEdgeFallbackAcceptedAsShellSemanticMapIsFalse :
      constantLocalBoundaryLabelToCRTEdgeFallbackAcceptedAsShellSemanticMap
      ≡
      false

    selectedLabelListConstructedFromCurrentData :
      Bool

    selectedLabelListConstructedFromCurrentDataIsFalse :
      selectedLabelListConstructedFromCurrentData ≡ false

    nativeShellSelectionInhabitedFromCurrentData :
      Bool

    nativeShellSelectionInhabitedFromCurrentDataIsFalse :
      nativeShellSelectionInhabitedFromCurrentData ≡ false

    acceptedAsGRPromotion :
      Bool

    acceptedAsGRPromotionIsFalse :
      acceptedAsGRPromotion ≡ false

    unavailableFromCurrentNativeData :
      List NativeLocalBoundaryLabelShellSelectionCurrentDataAbsence

    unavailableFromCurrentNativeDataIsCanonical :
      unavailableFromCurrentNativeData
      ≡
      canonicalNativeLocalBoundaryLabelShellSelectionCurrentDataAbsence

    firstUnavailableFromCurrentNativeData :
      NativeLocalBoundaryLabelShellSelectionCurrentDataAbsence

    firstUnavailableFromCurrentNativeDataIsCRTEdgeSemanticConstructor :
      firstUnavailableFromCurrentNativeData
      ≡
      missingNativeLocalBoundaryLabelCRTEdgeSemanticConstructor

    exactCurrentDataAbsenceBoundary :
      List String

canonicalNativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger :
  NativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger
canonicalNativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger =
  record
    { attemptedRecordName =
        "NativeLocalBoundaryLabelShellSelection"
    ; attemptedMapFieldName =
        "localBoundaryLabelToCRTEdge"
    ; attemptedMapTypeName =
        "localBoundaryEdgeLabel -> CRTMonodromy1Edge"
    ; attemptedSelectedLabelListFieldName =
        "selectedLocalBoundaryShellLabels"
    ; absentSemanticEqualityName =
        "selectedLocalBoundaryShellLabelsInterpretAsCRTShell"
    ; absentNativeConstructorName =
        "native boundary-label realization into the current localBoundaryEdgeLabel carrier with commuting CRT interpretation"
    ; targetCRTShellWord =
        crtMonodromy3BoundaryShellWord crtMonodromyCube
    ; targetCRTShellWordIsCanonical =
        refl
    ; targetCRTShellWordIsNonErasing =
        crtMonodromyShellWordIsNonErasing
    ; nativeLabelListSyntaxAvailable =
        true
    ; nativeLabelListSyntaxAvailableIsTrue =
        refl
    ; constantLocalBoundaryLabelToCRTEdgeFallbackAvailable =
        true
    ; constantLocalBoundaryLabelToCRTEdgeFallbackAvailableIsTrue =
        refl
    ; constantLocalBoundaryLabelToCRTEdgeFallbackAcceptedAsShellSemanticMap =
        false
    ; constantLocalBoundaryLabelToCRTEdgeFallbackAcceptedAsShellSemanticMapIsFalse =
        refl
    ; selectedLabelListConstructedFromCurrentData =
        false
    ; selectedLabelListConstructedFromCurrentDataIsFalse =
        refl
    ; nativeShellSelectionInhabitedFromCurrentData =
        false
    ; nativeShellSelectionInhabitedFromCurrentDataIsFalse =
        refl
    ; acceptedAsGRPromotion =
        false
    ; acceptedAsGRPromotionIsFalse =
        refl
    ; unavailableFromCurrentNativeData =
        canonicalNativeLocalBoundaryLabelShellSelectionCurrentDataAbsence
    ; unavailableFromCurrentNativeDataIsCanonical =
        refl
    ; firstUnavailableFromCurrentNativeData =
        missingNativeLocalBoundaryLabelCRTEdgeSemanticConstructor
    ; firstUnavailableFromCurrentNativeDataIsCRTEdgeSemanticConstructor =
        refl
    ; exactCurrentDataAbsenceBoundary =
        "The native local word/list API is available, including edge-label-list construction and round-trip"
        ∷ "This module now has concrete NativeBoundaryEdgeLabel constructors for edgeP2 edgeP3 edgeJ"
        ∷ "The canonical native shell label list maps definitionally to crtMonodromy3BoundaryShellWord crtMonodromyCube"
        ∷ "The current RealAnalysis local label carrier remains CRT-neutral without a supplied native-to-local realization"
        ∷ "A constant localBoundaryLabelToCRTEdge fallback is typeable but maps every native label to edgeP2"
        ∷ "That constant fallback is not accepted as semantic shell evidence for the mixed CRT shell word"
        ∷ "No selectedLocalBoundaryShellLabels constructor is present from current local data alone whose mapped image is the CRT monodromy shell"
        ∷ "The absent semantic equality is selectedLocalBoundaryShellLabelsInterpretAsCRTShell"
        ∷ "The absent native/local bridge is a realization of NativeBoundaryEdgeLabel into localBoundaryEdgeLabel with pointwise CRT commutation"
        ∷ "Consequently NativeLocalBoundaryLabelShellSelection is not inhabited from current local label/list data alone"
        ∷ "This ledger records only the blocked shell selection and is not a GR, Clay, or terminal promotion"
        ∷ []
    }

data FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker : Set where
  localBoundaryEdgeLabelIsOnlyASetField :
    FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker
  localBoundaryEdgeLabelHasNoCanonicalConstructor :
    FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker
  localBoundaryEdgeLabelHasNoNativeBoundaryEdgeLabelRealizer :
    FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker
  localBoundaryEdgeLabelHasNoCRTEdgeEliminator :
    FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker
  localBoundaryEdgeLabelHasNoSelectedCRTShellPreimage :
    FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker

canonicalFinalLocalBoundaryEdgeLabelRealizationIrreducibleBlockers :
  List FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker
canonicalFinalLocalBoundaryEdgeLabelRealizationIrreducibleBlockers =
  localBoundaryEdgeLabelIsOnlyASetField
  ∷ localBoundaryEdgeLabelHasNoCanonicalConstructor
  ∷ localBoundaryEdgeLabelHasNoNativeBoundaryEdgeLabelRealizer
  ∷ localBoundaryEdgeLabelHasNoCRTEdgeEliminator
  ∷ localBoundaryEdgeLabelHasNoSelectedCRTShellPreimage
  ∷ []

record FinalLocalBoundaryEdgeLabelRealizationIrreducibilityLedger
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface)
  (depth : Nat)
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth)
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) :
  Set₁ where
  field
    attemptedRealizationName :
      String

    attemptedSourceInterfaceName :
      String

    localBoundaryEdgeLabelCarrier :
      Set

    localBoundaryEdgeLabelCarrierIsInterfaceField :
      localBoundaryEdgeLabelCarrier
      ≡
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface

    localBoundaryEdgeLabelIsOnlySurfaceSetField :
      Bool

    localBoundaryEdgeLabelIsOnlySurfaceSetFieldIsTrue :
      localBoundaryEdgeLabelIsOnlySurfaceSetField ≡ true

    boundaryWordFromEdgeLabelsAvailable :
      Bool

    boundaryWordFromEdgeLabelsAvailableIsTrue :
      boundaryWordFromEdgeLabelsAvailable ≡ true

    boundaryWordFromEdgeLabelsConstructsOnlyWords :
      Bool

    boundaryWordFromEdgeLabelsConstructsOnlyWordsIsTrue :
      boundaryWordFromEdgeLabelsConstructsOnlyWords ≡ true

    boundaryWordEdgeLabelsRequiresBoundaryWord :
      Bool

    boundaryWordEdgeLabelsRequiresBoundaryWordIsTrue :
      boundaryWordEdgeLabelsRequiresBoundaryWord ≡ true

    nativeBoundaryEdgeLabelConstructorsAvailable :
      Bool

    nativeBoundaryEdgeLabelConstructorsAvailableIsTrue :
      nativeBoundaryEdgeLabelConstructorsAvailable ≡ true

    nativeBoundaryEdgeLabelToLocalBoundaryLabelAvailable :
      Bool

    nativeBoundaryEdgeLabelToLocalBoundaryLabelAvailableIsFalse :
      nativeBoundaryEdgeLabelToLocalBoundaryLabelAvailable ≡ false

    localBoundaryLabelToCRTEdgeAvailableFromInterface :
      Bool

    localBoundaryLabelToCRTEdgeAvailableFromInterfaceIsFalse :
      localBoundaryLabelToCRTEdgeAvailableFromInterface ≡ false

    selectedNativeCRTShellPreimageAvailableFromInterface :
      Bool

    selectedNativeCRTShellPreimageAvailableFromInterfaceIsFalse :
      selectedNativeCRTShellPreimageAvailableFromInterface ≡ false

    nativeBoundaryEdgeLabelLocalRealizationInhabitedFromInterfaceOnly :
      Bool

    nativeBoundaryEdgeLabelLocalRealizationInhabitedFromInterfaceOnlyIsFalse :
      nativeBoundaryEdgeLabelLocalRealizationInhabitedFromInterfaceOnly
      ≡
      false

    selectedLocalCRTBoundaryShellWordInhabitedFromInterfaceOnly :
      Bool

    selectedLocalCRTBoundaryShellWordInhabitedFromInterfaceOnlyIsFalse :
      selectedLocalCRTBoundaryShellWordInhabitedFromInterfaceOnly
      ≡
      false

    acceptedAsCRTStokesSpecialisation :
      Bool

    acceptedAsCRTStokesSpecialisationIsFalse :
      acceptedAsCRTStokesSpecialisation ≡ false

    irreducibleBlockers :
      List FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker

    irreducibleBlockersAreCanonical :
      irreducibleBlockers
      ≡
      canonicalFinalLocalBoundaryEdgeLabelRealizationIrreducibleBlockers

    firstIrreducibleBlocker :
      FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker

    firstIrreducibleBlockerIsSetField :
      firstIrreducibleBlocker
      ≡
      localBoundaryEdgeLabelIsOnlyASetField

    exactFinalIrreducibilityBoundary :
      List String

finalLocalBoundaryEdgeLabelRealizationIrreducibilityLedger :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  FinalLocalBoundaryEdgeLabelRealizationIrreducibilityLedger
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface
finalLocalBoundaryEdgeLabelRealizationIrreducibilityLedger
  localBoundaryWordStructuralInterface =
  record
    { attemptedRealizationName =
        "NativeBoundaryEdgeLabelLocalRealization"
    ; attemptedSourceInterfaceName =
        "LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel"
    ; localBoundaryEdgeLabelCarrier =
        LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
          localBoundaryWordStructuralInterface
    ; localBoundaryEdgeLabelCarrierIsInterfaceField =
        refl
    ; localBoundaryEdgeLabelIsOnlySurfaceSetField =
        true
    ; localBoundaryEdgeLabelIsOnlySurfaceSetFieldIsTrue =
        refl
    ; boundaryWordFromEdgeLabelsAvailable =
        true
    ; boundaryWordFromEdgeLabelsAvailableIsTrue =
        refl
    ; boundaryWordFromEdgeLabelsConstructsOnlyWords =
        true
    ; boundaryWordFromEdgeLabelsConstructsOnlyWordsIsTrue =
        refl
    ; boundaryWordEdgeLabelsRequiresBoundaryWord =
        true
    ; boundaryWordEdgeLabelsRequiresBoundaryWordIsTrue =
        refl
    ; nativeBoundaryEdgeLabelConstructorsAvailable =
        true
    ; nativeBoundaryEdgeLabelConstructorsAvailableIsTrue =
        refl
    ; nativeBoundaryEdgeLabelToLocalBoundaryLabelAvailable =
        false
    ; nativeBoundaryEdgeLabelToLocalBoundaryLabelAvailableIsFalse =
        refl
    ; localBoundaryLabelToCRTEdgeAvailableFromInterface =
        false
    ; localBoundaryLabelToCRTEdgeAvailableFromInterfaceIsFalse =
        refl
    ; selectedNativeCRTShellPreimageAvailableFromInterface =
        false
    ; selectedNativeCRTShellPreimageAvailableFromInterfaceIsFalse =
        refl
    ; nativeBoundaryEdgeLabelLocalRealizationInhabitedFromInterfaceOnly =
        false
    ; nativeBoundaryEdgeLabelLocalRealizationInhabitedFromInterfaceOnlyIsFalse =
        refl
    ; selectedLocalCRTBoundaryShellWordInhabitedFromInterfaceOnly =
        false
    ; selectedLocalCRTBoundaryShellWordInhabitedFromInterfaceOnlyIsFalse =
        refl
    ; acceptedAsCRTStokesSpecialisation =
        false
    ; acceptedAsCRTStokesSpecialisationIsFalse =
        refl
    ; irreducibleBlockers =
        canonicalFinalLocalBoundaryEdgeLabelRealizationIrreducibleBlockers
    ; irreducibleBlockersAreCanonical =
        refl
    ; firstIrreducibleBlocker =
        localBoundaryEdgeLabelIsOnlyASetField
    ; firstIrreducibleBlockerIsSetField =
        refl
    ; exactFinalIrreducibilityBoundary =
        "For an arbitrary local structural interface, localBoundaryEdgeLabel is exposed only as a Set field"
        ∷ "The interface has no constructor producing a localBoundaryEdgeLabel value"
        ∷ "boundaryWordFromEdgeLabels constructs BoundaryWordAtDepth from already supplied local labels; it does not construct labels"
        ∷ "boundaryWordEdgeLabels eliminates an already supplied BoundaryWordAtDepth to a list of local labels; it does not select the CRT shell preimage"
        ∷ "The fold/eliminator is for BoundaryWordAtDepth values, not for arbitrary localBoundaryEdgeLabel values"
        ∷ "NativeBoundaryEdgeLabel has canonical edgeP2 edgeP3 edgeJ constructors, but no map from NativeBoundaryEdgeLabel into this arbitrary local label carrier is supplied"
        ∷ "The interface also supplies no localBoundaryEdgeLabel -> CRTMonodromy1Edge semantic eliminator"
        ∷ "Therefore NativeBoundaryEdgeLabelLocalRealization cannot be inhabited from LocalBoundaryWordAtDepthStructuralInterface alone"
        ∷ "Consequently the CRT Stokes specialisation cannot be advanced without additional native-to-local realization evidence"
        ∷ []
    }

nativeLocalBoundaryLabelToCRTCompatibilityFromShellSelection :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  NativeLocalBoundaryLabelShellSelection
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface →
  NativeLocalBoundaryLabelToCRTCompatibility
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface
nativeLocalBoundaryLabelToCRTCompatibilityFromShellSelection
  {localStokesSurface}
  {depth}
  {stokesLoop}
  localBoundaryWordStructuralInterface
  shellSelection =
  record
    { localBoundaryLabelToCRTEdge =
        labelToCRTEdge
    ; selectedLocalBoundaryWordForCRTMonodromyCube =
        selectedWord
    ; selectedLocalBoundaryWordLabelsInterpretAsCRTShell =
        selectedWordInterpretsAsCRTShell
    ; selectedLocalBoundaryWordLabelsAreNonErasing =
        crtBoundaryWordNonErasingFromShellEquality
          selectedWordInterpretsAsCRTShell
    ; localFoldComputesCRTListAppendAfterLabelInterpretation =
        nativeLocalBoundaryLabelCRTInterpreterFoldListAppendLaw
          localBoundaryWordStructuralInterface
          labelToCRTEdge
    ; finalCompatibilityRequest =
        canonicalFinalNativeLocalBoundaryLabelCRTCompatibilityRequest
    ; finalCompatibilityRequestIsCanonical =
        refl
    ; exactCRTLabelCompatibilityBoundary =
        "The selected local BoundaryWordAtDepth is built from the supplied native label list"
        ∷ "The native edge-label constructor round-trip identifies the selected word labels with the supplied label list"
        ∷ "The supplied label-to-CRT map sends that label list to the CRT shell word"
        ∷ "The non-erasing witness is transported from the canonical CRT shell equality"
        ∷ "The append and fold/list laws are derived from the native structural interface"
        ∷ "This compatibility record still does not prove CRT Stokes or cyclic Bianchi"
        ∷ []
    }
  where
    labelToCRTEdge :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface →
      CRTMonodromy1Edge
    labelToCRTEdge =
      NativeLocalBoundaryLabelShellSelection.localBoundaryLabelToCRTEdge
        shellSelection

    selectedLabels :
      List
        (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
          localBoundaryWordStructuralInterface)
    selectedLabels =
      NativeLocalBoundaryLabelShellSelection.selectedLocalBoundaryShellLabels
        shellSelection

    selectedWord :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop
    selectedWord =
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordFromEdgeLabels
        localBoundaryWordStructuralInterface
        selectedLabels

    selectedWordLabelsAreSelectedLabels :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordEdgeLabels
        localBoundaryWordStructuralInterface
        selectedWord
      ≡
      selectedLabels
    selectedWordLabelsAreSelectedLabels =
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordEdgeLabelsFromConstructed
        localBoundaryWordStructuralInterface
        selectedLabels

    selectedWordInterpretsAsCRTShell :
      nativeLocalBoundaryLabelCRTInterpreter
        localBoundaryWordStructuralInterface
        labelToCRTEdge
        selectedWord
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube
    selectedWordInterpretsAsCRTShell =
      trans
        (cong
          (mapList labelToCRTEdge)
          selectedWordLabelsAreSelectedLabels)
        (NativeLocalBoundaryLabelShellSelection.selectedLocalBoundaryShellLabelsInterpretAsCRTShell
          shellSelection)

record LocalToCRTBoundaryWordSemanticAlignmentPrimitive : Set₁ where
  field
    localStokesSurface :
      RA.LocalDiscreteNonabelianStokesProofSurface

    depth :
      Nat

    stokesLoop :
      RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
        localStokesSurface
        depth

    localBoundaryWordStructuralInterface :
      LocalBoundaryWordAtDepthStructuralInterface
        localStokesSurface
        depth
        stokesLoop

    localCRTBoundaryShellWordConstructor :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop

    localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges :
      StokesBoundaryWordInterpreterType
        localStokesSurface
        depth
        stokesLoop

    selectedLocalBoundaryWordForCRTMonodromyCube :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop

    selectedLocalBoundaryWordIsConstructedShell :
      selectedLocalBoundaryWordForCRTMonodromyCube
      ≡
      localCRTBoundaryShellWordConstructor

    selectedLocalBoundaryWordInterpretsAsCRTBoundaryShell :
      localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
        selectedLocalBoundaryWordForCRTMonodromyCube
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    selectedLocalBoundaryWordInterpretationIsNonErasing :
      CRTBoundaryWordIsNonErasing
        (localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
          selectedLocalBoundaryWordForCRTMonodromyCube)

    nonErasingInterpreterAppendLawForSelectedCRTShell :
      StokesBoundaryWordInterpreterHomomorphismLawType
        localStokesSurface
        depth
        stokesLoop
        localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
        (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordAppend
          localBoundaryWordStructuralInterface)

    foldComputationLawRelatingLocalAppendToCRTListAppend :
      LocalBoundaryWordFoldComputesCRTListAppendLawType
        localStokesSurface
        depth
        stokesLoop
        localBoundaryWordStructuralInterface
        localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges

    acceptedAsGRPromotion :
      Bool

    acceptedAsGRPromotionIsFalse :
      acceptedAsGRPromotion ≡ false

    exactTypedPrimitiveBoundary :
      List String

localToCRTBoundaryWordSemanticAlignmentPrimitiveFromSuppliedEvidence :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  (localCRTBoundaryShellWordConstructor :
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop) →
  (localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges :
    StokesBoundaryWordInterpreterType
      localStokesSurface
      depth
      stokesLoop) →
  (selectedLocalBoundaryWordForCRTMonodromyCube :
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop) →
  selectedLocalBoundaryWordForCRTMonodromyCube
  ≡
  localCRTBoundaryShellWordConstructor →
  localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
    selectedLocalBoundaryWordForCRTMonodromyCube
  ≡
  crtMonodromy3BoundaryShellWord crtMonodromyCube →
  CRTBoundaryWordIsNonErasing
    (localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
      selectedLocalBoundaryWordForCRTMonodromyCube) →
  StokesBoundaryWordInterpreterHomomorphismLawType
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
    (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordAppend
      localBoundaryWordStructuralInterface) →
  LocalBoundaryWordFoldComputesCRTListAppendLawType
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface
    localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges →
  LocalToCRTBoundaryWordSemanticAlignmentPrimitive
localToCRTBoundaryWordSemanticAlignmentPrimitiveFromSuppliedEvidence
  {localStokesSurface}
  {depth}
  {stokesLoop}
  localBoundaryWordStructuralInterface
  localCRTBoundaryShellWordConstructor
  localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
  selectedLocalBoundaryWordForCRTMonodromyCube
  selectedLocalBoundaryWordIsConstructedShell
  selectedLocalBoundaryWordInterpretsAsCRTBoundaryShell
  selectedLocalBoundaryWordInterpretationIsNonErasing
  nonErasingInterpreterAppendLawForSelectedCRTShell
  foldComputationLawRelatingLocalAppendToCRTListAppend =
  record
    { localStokesSurface =
        localStokesSurface
    ; depth =
        depth
    ; stokesLoop =
        stokesLoop
    ; localBoundaryWordStructuralInterface =
        localBoundaryWordStructuralInterface
    ; localCRTBoundaryShellWordConstructor =
        localCRTBoundaryShellWordConstructor
    ; localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges =
        localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
    ; selectedLocalBoundaryWordForCRTMonodromyCube =
        selectedLocalBoundaryWordForCRTMonodromyCube
    ; selectedLocalBoundaryWordIsConstructedShell =
        selectedLocalBoundaryWordIsConstructedShell
    ; selectedLocalBoundaryWordInterpretsAsCRTBoundaryShell =
        selectedLocalBoundaryWordInterpretsAsCRTBoundaryShell
    ; selectedLocalBoundaryWordInterpretationIsNonErasing =
        selectedLocalBoundaryWordInterpretationIsNonErasing
    ; nonErasingInterpreterAppendLawForSelectedCRTShell =
        nonErasingInterpreterAppendLawForSelectedCRTShell
    ; foldComputationLawRelatingLocalAppendToCRTListAppend =
        foldComputationLawRelatingLocalAppendToCRTListAppend
    ; acceptedAsGRPromotion =
        false
    ; acceptedAsGRPromotionIsFalse =
        refl
    ; exactTypedPrimitiveBoundary =
        "This constructor only packages supplied local-to-CRT semantic evidence"
        ∷ "The current LocalBoundaryWordAtDepthStructuralInterface supplies append and fold"
        ∷ "It does not derive a local CRT boundary shell word constructor"
        ∷ "It does not derive local BoundaryWordAtDepth edge labels into CRTMonodromy1Edge"
        ∷ "It does not derive the non-erasing selected-shell append homomorphism"
        ∷ "It does not derive the local fold computation law relating append to CRT list append"
        ∷ "The packaged primitive is explicitly not a GR promotion"
        ∷ []
    }

localToCRTBoundaryWordSemanticAlignmentPrimitiveFromNativeLabelCompatibility :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  NativeLocalBoundaryLabelToCRTCompatibility
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface →
  LocalToCRTBoundaryWordSemanticAlignmentPrimitive
localToCRTBoundaryWordSemanticAlignmentPrimitiveFromNativeLabelCompatibility
  {localStokesSurface}
  {depth}
  {stokesLoop}
  localBoundaryWordStructuralInterface
  compatibility =
  localToCRTBoundaryWordSemanticAlignmentPrimitiveFromSuppliedEvidence
    localBoundaryWordStructuralInterface
    selectedWord
    interpreter
    selectedWord
    refl
    selectedWordInterpretsAsCRTShell
    selectedWordInterpretationIsNonErasing
    appendLaw
    foldLaw
  where
    labelToCRTEdge :
      LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel
        localBoundaryWordStructuralInterface →
      CRTMonodromy1Edge
    labelToCRTEdge =
      NativeLocalBoundaryLabelToCRTCompatibility.localBoundaryLabelToCRTEdge
        compatibility

    selectedWord :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop
    selectedWord =
      NativeLocalBoundaryLabelToCRTCompatibility.selectedLocalBoundaryWordForCRTMonodromyCube
        compatibility

    interpreter :
      StokesBoundaryWordInterpreterType
        localStokesSurface
        depth
        stokesLoop
    interpreter =
      nativeLocalBoundaryLabelCRTInterpreter
        localBoundaryWordStructuralInterface
        labelToCRTEdge

    selectedWordInterpretsAsCRTShell :
      interpreter selectedWord
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube
    selectedWordInterpretsAsCRTShell =
      NativeLocalBoundaryLabelToCRTCompatibility.selectedLocalBoundaryWordLabelsInterpretAsCRTShell
        compatibility

    selectedWordInterpretationIsNonErasing :
      CRTBoundaryWordIsNonErasing
        (interpreter selectedWord)
    selectedWordInterpretationIsNonErasing =
      NativeLocalBoundaryLabelToCRTCompatibility.selectedLocalBoundaryWordLabelsAreNonErasing
        compatibility

    appendLaw :
      StokesBoundaryWordInterpreterHomomorphismLawType
        localStokesSurface
        depth
        stokesLoop
        interpreter
        (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordAppend
          localBoundaryWordStructuralInterface)
    appendLaw =
      nativeLocalBoundaryLabelCRTInterpreterAppendLaw
        localBoundaryWordStructuralInterface
        labelToCRTEdge

    foldLaw :
      LocalBoundaryWordFoldComputesCRTListAppendLawType
        localStokesSurface
        depth
        stokesLoop
        localBoundaryWordStructuralInterface
        interpreter
    foldLaw =
      NativeLocalBoundaryLabelToCRTCompatibility.localFoldComputesCRTListAppendAfterLabelInterpretation
        compatibility

localToCRTBoundaryWordSemanticAlignmentPrimitiveFromNativeShellSelection :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  NativeLocalBoundaryLabelShellSelection
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface →
  LocalToCRTBoundaryWordSemanticAlignmentPrimitive
localToCRTBoundaryWordSemanticAlignmentPrimitiveFromNativeShellSelection
  localBoundaryWordStructuralInterface
  shellSelection =
  localToCRTBoundaryWordSemanticAlignmentPrimitiveFromNativeLabelCompatibility
    localBoundaryWordStructuralInterface
    (nativeLocalBoundaryLabelToCRTCompatibilityFromShellSelection
      localBoundaryWordStructuralInterface
      shellSelection)

record SelectedLocalCRTBoundaryShellWord : Set₁ where
  field
    alignmentPrimitive :
      LocalToCRTBoundaryWordSemanticAlignmentPrimitive

    localCRTBoundaryShellWordConstructor :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localStokesSurface
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.depth
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.stokesLoop
          alignmentPrimitive)

    localCRTBoundaryShellWordConstructorIsPrimitiveConstructor :
      localCRTBoundaryShellWordConstructor
      ≡
      LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localCRTBoundaryShellWordConstructor
        alignmentPrimitive

    selectedLocalBoundaryWord :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localStokesSurface
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.depth
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.stokesLoop
          alignmentPrimitive)

    selectedLocalBoundaryWordIsPrimitiveSelected :
      selectedLocalBoundaryWord
      ≡
      LocalToCRTBoundaryWordSemanticAlignmentPrimitive.selectedLocalBoundaryWordForCRTMonodromyCube
        alignmentPrimitive

    selectedLocalBoundaryWordIsConstructedShell :
      selectedLocalBoundaryWord
      ≡
      localCRTBoundaryShellWordConstructor

    selectedLocalBoundaryWordEdgeLabels :
      List CRTMonodromy1Edge

    selectedLocalBoundaryWordEdgeLabelsArePrimitiveInterpretation :
      selectedLocalBoundaryWordEdgeLabels
      ≡
      LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
        alignmentPrimitive
        selectedLocalBoundaryWord

    selectedLocalBoundaryWordEdgeLabelsAreCRTShell :
      selectedLocalBoundaryWordEdgeLabels
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    selectedLocalBoundaryWordEdgeLabelsAreNonErasing :
      CRTBoundaryWordIsNonErasing selectedLocalBoundaryWordEdgeLabels

    selectedLocalBoundaryWordAppendIsCRTListAppend :
      StokesBoundaryWordInterpreterHomomorphismLawType
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localStokesSurface
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.depth
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.stokesLoop
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
          alignmentPrimitive)
        (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordAppend
          (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localBoundaryWordStructuralInterface
            alignmentPrimitive))

    selectedLocalBoundaryWordFoldComputesCRTListAppend :
      LocalBoundaryWordFoldComputesCRTListAppendLawType
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localStokesSurface
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.depth
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.stokesLoop
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localBoundaryWordStructuralInterface
          alignmentPrimitive)
        (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
          alignmentPrimitive)

    selectedLocalBoundaryWordHolonomyTrace :
      List DCRT.CRTHolonomyElement

    selectedLocalBoundaryWordHolonomyTraceIsEdgeTrace :
      selectedLocalBoundaryWordHolonomyTrace
      ≡
      crtMonodromyWordHolonomyTrace selectedLocalBoundaryWordEdgeLabels

    exactSelectedShellBoundary :
      List String

selectedLocalCRTBoundaryShellWordFromAlignmentPrimitive :
  (alignmentPrimitive : LocalToCRTBoundaryWordSemanticAlignmentPrimitive) →
  SelectedLocalCRTBoundaryShellWord
selectedLocalCRTBoundaryShellWordFromAlignmentPrimitive alignmentPrimitive =
  record
    { alignmentPrimitive =
        alignmentPrimitive
    ; localCRTBoundaryShellWordConstructor =
        LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localCRTBoundaryShellWordConstructor
          alignmentPrimitive
    ; localCRTBoundaryShellWordConstructorIsPrimitiveConstructor =
        refl
    ; selectedLocalBoundaryWord =
        LocalToCRTBoundaryWordSemanticAlignmentPrimitive.selectedLocalBoundaryWordForCRTMonodromyCube
          alignmentPrimitive
    ; selectedLocalBoundaryWordIsPrimitiveSelected =
        refl
    ; selectedLocalBoundaryWordIsConstructedShell =
        LocalToCRTBoundaryWordSemanticAlignmentPrimitive.selectedLocalBoundaryWordIsConstructedShell
          alignmentPrimitive
    ; selectedLocalBoundaryWordEdgeLabels =
        LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
          alignmentPrimitive
          (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.selectedLocalBoundaryWordForCRTMonodromyCube
            alignmentPrimitive)
    ; selectedLocalBoundaryWordEdgeLabelsArePrimitiveInterpretation =
        refl
    ; selectedLocalBoundaryWordEdgeLabelsAreCRTShell =
        LocalToCRTBoundaryWordSemanticAlignmentPrimitive.selectedLocalBoundaryWordInterpretsAsCRTBoundaryShell
          alignmentPrimitive
    ; selectedLocalBoundaryWordEdgeLabelsAreNonErasing =
        LocalToCRTBoundaryWordSemanticAlignmentPrimitive.selectedLocalBoundaryWordInterpretationIsNonErasing
          alignmentPrimitive
    ; selectedLocalBoundaryWordAppendIsCRTListAppend =
        LocalToCRTBoundaryWordSemanticAlignmentPrimitive.nonErasingInterpreterAppendLawForSelectedCRTShell
          alignmentPrimitive
    ; selectedLocalBoundaryWordFoldComputesCRTListAppend =
        LocalToCRTBoundaryWordSemanticAlignmentPrimitive.foldComputationLawRelatingLocalAppendToCRTListAppend
          alignmentPrimitive
    ; selectedLocalBoundaryWordHolonomyTrace =
        crtMonodromyWordHolonomyTrace
          (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.localBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
            alignmentPrimitive
            (LocalToCRTBoundaryWordSemanticAlignmentPrimitive.selectedLocalBoundaryWordForCRTMonodromyCube
              alignmentPrimitive))
    ; selectedLocalBoundaryWordHolonomyTraceIsEdgeTrace =
        refl
    ; exactSelectedShellBoundary =
        "SelectedLocalCRTBoundaryShellWord is a non-erasing wrapper over supplied local-to-CRT evidence"
        ∷ "It exposes the selected local BoundaryWordAtDepth value without replacing it by the empty word"
        ∷ "It exposes the CRT edge labels computed by the supplied edge-label interpreter"
        ∷ "The exposed edge labels are identified with crtMonodromy3BoundaryShellWord crtMonodromyCube"
        ∷ "It carries the supplied append law from local boundary-word append to CRT list append"
        ∷ "It carries the supplied fold computation law relating the local fold to CRT list append"
        ∷ "It derives only the CRT holonomy trace over those exposed edge labels"
        ∷ "It is not constructible from the CRT-neutral RealAnalysisAxioms surface without supplied CRT semantic evidence"
        ∷ []
    }

selectedLocalCRTBoundaryShellWordFromNativeBoundaryEdgeLabelLocalRealization :
  {localStokesSurface :
    RA.LocalDiscreteNonabelianStokesProofSurface} →
  {depth :
    Nat} →
  {stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth} →
  (localBoundaryWordStructuralInterface :
    LocalBoundaryWordAtDepthStructuralInterface
      localStokesSurface
      depth
      stokesLoop) →
  NativeBoundaryEdgeLabelLocalRealization
    localStokesSurface
    depth
    stokesLoop
    localBoundaryWordStructuralInterface →
  SelectedLocalCRTBoundaryShellWord
selectedLocalCRTBoundaryShellWordFromNativeBoundaryEdgeLabelLocalRealization
  localBoundaryWordStructuralInterface
  realization =
  selectedLocalCRTBoundaryShellWordFromAlignmentPrimitive
    (localToCRTBoundaryWordSemanticAlignmentPrimitiveFromNativeShellSelection
      localBoundaryWordStructuralInterface
      (nativeLocalBoundaryLabelShellSelectionFromNativeBoundaryEdgeLabelLocalRealization
        localBoundaryWordStructuralInterface
        realization))

data RealAnalysisLocalBoundaryEdgeWordConstructorRequiredField : Set where
  requiredLocalCRTBoundaryShellWordConstructorField :
    RealAnalysisLocalBoundaryEdgeWordConstructorRequiredField
  requiredLocalBoundaryWordEdgeLabelingField :
    RealAnalysisLocalBoundaryEdgeWordConstructorRequiredField
  requiredConstructedWordLabelRoundTripField :
    RealAnalysisLocalBoundaryEdgeWordConstructorRequiredField
  requiredMappedFoldComputesListAppendField :
    RealAnalysisLocalBoundaryEdgeWordConstructorRequiredField

canonicalRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFields :
  List RealAnalysisLocalBoundaryEdgeWordConstructorRequiredField
canonicalRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFields =
  requiredLocalCRTBoundaryShellWordConstructorField
  ∷ requiredLocalBoundaryWordEdgeLabelingField
  ∷ requiredConstructedWordLabelRoundTripField
  ∷ requiredMappedFoldComputesListAppendField
  ∷ []

record RealAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest : Set where
  field
    requestName :
      String

    targetRecordName :
      String

    wrapperUnlockedByExtensionName :
      String

    requiredConstructorFieldName :
      String

    requiredEdgeLabelingFieldName :
      String

    requiredConstructedWordLabelRoundTripFieldName :
      String

    requiredMappedFoldComputesListAppendFieldName :
      String

    requiredFields :
      List RealAnalysisLocalBoundaryEdgeWordConstructorRequiredField

    requiredFieldsAreCanonical :
      requiredFields
      ≡
      canonicalRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFields

    broadAPIChurnAvoidedHere :
      Bool

    broadAPIChurnAvoidedHereIsTrue :
      broadAPIChurnAvoidedHere ≡ true

    acceptedAsGRPromotion :
      Bool

    acceptedAsGRPromotionIsFalse :
      acceptedAsGRPromotion ≡ false

    exactExtensionRequestBoundary :
      List String

canonicalRealAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest :
  RealAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest
canonicalRealAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest =
  record
    { requestName =
        "RealAnalysisLocalBoundaryEdgeWordConstructorExtension"
    ; targetRecordName =
        "DASHI.Foundations.RealAnalysisAxioms.LocalDiscreteNonabelianStokesProofSurface"
    ; wrapperUnlockedByExtensionName =
        "SelectedLocalCRTBoundaryShellWord"
    ; requiredConstructorFieldName =
        "boundaryWordFromEdgeLabelsAtDepth"
    ; requiredEdgeLabelingFieldName =
        "boundaryWordEdgeLabelsAtDepth"
    ; requiredConstructedWordLabelRoundTripFieldName =
        "boundaryWordEdgeLabelsFromConstructedAtDepth"
    ; requiredMappedFoldComputesListAppendFieldName =
        "boundaryWordFoldComputesMappedEdgeLabelListAtDepth"
    ; requiredFields =
        canonicalRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFields
    ; requiredFieldsAreCanonical =
        refl
    ; broadAPIChurnAvoidedHere =
        true
    ; broadAPIChurnAvoidedHereIsTrue =
        refl
    ; acceptedAsGRPromotion =
        false
    ; acceptedAsGRPromotionIsFalse =
        refl
    ; exactExtensionRequestBoundary =
        "RealAnalysisAxioms now exposes the native local boundary-edge label carrier"
        ∷ "RealAnalysisAxioms now exposes local edge-label-list word construction"
        ∷ "RealAnalysisAxioms now exposes constructed-word label round-trip, append, and mapped fold/list laws"
        ∷ "The extension was kept CRT-neutral, so RealAnalysisAxioms does not import CRTMonodromy1Edge"
        ∷ "A CRT specialisation still needs a native label-to-CRT map and a selected local label preimage of the CRT shell"
        ∷ "The non-erasing witness and append/fold computation laws are derived after that narrow compatibility is supplied"
        ∷ "The API change is contained to LocalDiscreteNonabelianStokesProofSurface and its canonical B0.2 consumer"
        ∷ []
    }

data LocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence : Set where
  structuralInterfaceDoesNotInterpretLocalLabelsAsCRTEdgeLabels :
    LocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence
  structuralInterfaceDoesNotSelectLocalLabelShellPreimage :
    LocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence
  structuralInterfaceDoesNotProveSelectedLocalLabelsMapToCRTShell :
    LocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence

canonicalLocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence :
  List LocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence
canonicalLocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence =
  structuralInterfaceDoesNotInterpretLocalLabelsAsCRTEdgeLabels
  ∷ structuralInterfaceDoesNotSelectLocalLabelShellPreimage
  ∷ structuralInterfaceDoesNotProveSelectedLocalLabelsMapToCRTShell
  ∷ []

record LocalToCRTBoundaryWordSemanticAlignmentAbsenceLedger : Set₁ where
  field
    attemptedPrimitiveName :
      String

    attemptedSourceInterfaceName :
      String

    targetCRTShellWord :
      List CRTMonodromy1Edge

    targetCRTShellWordIsCanonical :
      targetCRTShellWord
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    targetCRTShellWordIsNonErasing :
      CRTBoundaryWordIsNonErasing targetCRTShellWord

    localAppendFoldAvailable :
      Bool

    localAppendFoldAvailableIsTrue :
      localAppendFoldAvailable ≡ true

    crtListAppendFoldAvailable :
      Bool

    crtListAppendFoldAvailableIsTrue :
      crtListAppendFoldAvailable ≡ true

    primitiveInhabitedFromStructuralInterfaceOnly :
      Bool

    primitiveInhabitedFromStructuralInterfaceOnlyIsFalse :
      primitiveInhabitedFromStructuralInterfaceOnly ≡ false

    acceptedAsGRPromotion :
      Bool

    acceptedAsGRPromotionIsFalse :
      acceptedAsGRPromotion ≡ false

    unavailableFromStructuralInterface :
      List LocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence

    unavailableFromStructuralInterfaceIsCanonical :
      unavailableFromStructuralInterface
      ≡
      canonicalLocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence

    firstUnavailableFromStructuralInterface :
      LocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence

    firstUnavailableFromStructuralInterfaceIsLabelToCRTEdge :
      firstUnavailableFromStructuralInterface
      ≡
      structuralInterfaceDoesNotInterpretLocalLabelsAsCRTEdgeLabels

    exactAbsenceBoundary :
      List String

canonicalLocalToCRTBoundaryWordSemanticAlignmentAbsenceLedger :
  LocalToCRTBoundaryWordSemanticAlignmentAbsenceLedger
canonicalLocalToCRTBoundaryWordSemanticAlignmentAbsenceLedger =
  record
    { attemptedPrimitiveName =
        "LocalToCRTBoundaryWordSemanticAlignmentPrimitive"
    ; attemptedSourceInterfaceName =
        "LocalBoundaryWordAtDepthStructuralInterface"
    ; targetCRTShellWord =
        crtMonodromy3BoundaryShellWord crtMonodromyCube
    ; targetCRTShellWordIsCanonical =
        refl
    ; targetCRTShellWordIsNonErasing =
        crtMonodromyShellWordIsNonErasing
    ; localAppendFoldAvailable =
        true
    ; localAppendFoldAvailableIsTrue =
        refl
    ; crtListAppendFoldAvailable =
        true
    ; crtListAppendFoldAvailableIsTrue =
        refl
    ; primitiveInhabitedFromStructuralInterfaceOnly =
        false
    ; primitiveInhabitedFromStructuralInterfaceOnlyIsFalse =
        refl
    ; acceptedAsGRPromotion =
        false
    ; acceptedAsGRPromotionIsFalse =
        refl
    ; unavailableFromStructuralInterface =
        canonicalLocalToCRTBoundaryWordSemanticAlignmentStructuralAbsence
    ; unavailableFromStructuralInterfaceIsCanonical =
        refl
    ; firstUnavailableFromStructuralInterface =
        structuralInterfaceDoesNotInterpretLocalLabelsAsCRTEdgeLabels
    ; firstUnavailableFromStructuralInterfaceIsLabelToCRTEdge =
        refl
    ; exactAbsenceBoundary =
        "The CRT shell word and CRT-side list append/fold laws are already present"
        ∷ "The local structural interface now exposes BoundaryWordAtDepth append, fold, edge-label-list construction, constructor round-trip, and mapped fold/list laws"
        ∷ "The local edge labels are RealAnalysis-native and CRT-neutral"
        ∷ "It has no map from native local edge labels to CRTMonodromy1Edge labels"
        ∷ "It has no selected native local label list whose mapped labels are the non-erasing CRT shell"
        ∷ "Once those two pieces are supplied, the selected word, non-erasing witness, append law, and fold/list law are derived"
        ∷ "Therefore the full CRT semantic primitive is not derivable from the native local syntax alone"
        ∷ []
    }

record NonErasingStokesBoundaryWordInterpreterPrimitiveRequest : Set₁ where
  field
    localStokesSurface :
      RA.LocalDiscreteNonabelianStokesProofSurface

    depth :
      Nat

    stokesLoop :
      RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
        localStokesSurface
        depth

    stokesBoundaryWord :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop

    localBoundaryWordStructuralInterface :
      LocalBoundaryWordAtDepthStructuralInterface
        localStokesSurface
        depth
        stokesLoop

    nonErasingInterpreter :
      StokesBoundaryWordInterpreterType
        localStokesSurface
        depth
        stokesLoop

    nonErasingInterpreterAppendLaw :
      StokesBoundaryWordInterpreterHomomorphismLawType
        localStokesSurface
        depth
        stokesLoop
        nonErasingInterpreter
        (LocalBoundaryWordAtDepthStructuralInterface.localBoundaryWordAppend
          localBoundaryWordStructuralInterface)

    selectedWordInterpretsAsCRTBoundaryShell :
      nonErasingInterpreter stokesBoundaryWord
      ≡
      crtMonodromy3BoundaryShellWord crtMonodromyCube

    selectedWordInterpretationIsNonErasing :
      CRTBoundaryWordIsNonErasing
        (nonErasingInterpreter stokesBoundaryWord)

    boundaryShellTraceHomomorphism :
      CRTBoundaryWordHolonomyTraceHomomorphism

    boundaryShellTraceHomomorphismIsCanonical :
      boundaryShellTraceHomomorphism
      ≡
      canonicalCRTBoundaryWordHolonomyTraceHomomorphism

    exactSemanticBoundaryWordPrimitive :
      List String

eraseStokesBoundaryWordToCRTBoundaryWord :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  StokesBoundaryWordInterpreterType
    localStokesSurface
    depth
    stokesLoop
eraseStokesBoundaryWordToCRTBoundaryWord _ _ _ _ = []

eraseStokesBoundaryWordInterpretsCanonicalCRTBoundary :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  (stokesBoundaryWord :
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop) →
  eraseStokesBoundaryWordToCRTBoundaryWord
    localStokesSurface
    depth
    stokesLoop
    stokesBoundaryWord
  ≡
  crtMonodromyBoundaryOfBoundaryWord crtMonodromyCube
eraseStokesBoundaryWordInterpretsCanonicalCRTBoundary _ _ _ _ = refl

eraseStokesBoundaryWordActionIsIdentity :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  (stokesBoundaryWord :
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop) →
  crtMonodromyBoundaryWordAction
    (eraseStokesBoundaryWordToCRTBoundaryWord
      localStokesSurface
      depth
      stokesLoop
      stokesBoundaryWord)
  ≡
  identityCRTBoundaryWordAction
eraseStokesBoundaryWordActionIsIdentity _ _ _ _ = refl

eraseStokesBoundaryWordInterpreterAppendLaw :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  (localBoundaryWordAppend :
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop →
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop →
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop) →
  StokesBoundaryWordInterpreterHomomorphismLawType
    localStokesSurface
    depth
    stokesLoop
    (eraseStokesBoundaryWordToCRTBoundaryWord
      localStokesSurface
      depth
      stokesLoop)
    localBoundaryWordAppend
eraseStokesBoundaryWordInterpreterAppendLaw _ _ _ _ left right = refl

record CRTStokesBoundaryWordInterpreterNarrowing : Set₁ where
  field
    localStokesSurface :
      RA.LocalDiscreteNonabelianStokesProofSurface

    depth :
      Nat

    stokesLoop :
      RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
        localStokesSurface
        depth

    stokesBoundaryWord :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop

    interpreter :
      StokesBoundaryWordInterpreterType
        localStokesSurface
        depth
        stokesLoop

    interpreterMapsSelectedWordToCanonicalCRTBoundary :
      interpreter stokesBoundaryWord
      ≡
      crtMonodromyBoundaryOfBoundaryWord crtMonodromyCube

    interpretedSelectedWordActionIsIdentity :
      crtMonodromyBoundaryWordAction (interpreter stokesBoundaryWord)
      ≡
      identityCRTBoundaryWordAction

    crtBoundaryWordFoldConcatenationInterface :
      CRTBoundaryWordFoldConcatenationInterface

    crtBoundaryWordFoldConcatenationInterfaceIsCanonical :
      crtBoundaryWordFoldConcatenationInterface
      ≡
      canonicalCRTBoundaryWordFoldConcatenationInterface

    acceptedAsCRTStokesSpecialisation :
      Bool

    acceptedAsCRTStokesSpecialisationIsFalse :
      acceptedAsCRTStokesSpecialisation ≡ false

    firstMissingSemanticLaw :
      CRTDiscreteStokesSpecialisationMissingField

    firstMissingSemanticLawIsBoundaryInterpreterLaw :
      firstMissingSemanticLaw
      ≡
      missingStokesBoundaryWordInterpreterLawForCRTBoundary

    exactNarrowingBoundary :
      List String

erasingCRTStokesBoundaryWordInterpreterNarrowing :
  (localStokesSurface : RA.LocalDiscreteNonabelianStokesProofSurface) →
  (depth : Nat) →
  (stokesLoop :
    RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
      localStokesSurface
      depth) →
  (stokesBoundaryWord :
    RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
      localStokesSurface
      depth
      stokesLoop) →
  CRTStokesBoundaryWordInterpreterNarrowing
erasingCRTStokesBoundaryWordInterpreterNarrowing
  localStokesSurface
  depth
  stokesLoop
  stokesBoundaryWord =
  record
    { localStokesSurface =
        localStokesSurface
    ; depth =
        depth
    ; stokesLoop =
        stokesLoop
    ; stokesBoundaryWord =
        stokesBoundaryWord
    ; interpreter =
        eraseStokesBoundaryWordToCRTBoundaryWord
          localStokesSurface
          depth
          stokesLoop
    ; interpreterMapsSelectedWordToCanonicalCRTBoundary =
        eraseStokesBoundaryWordInterpretsCanonicalCRTBoundary
          localStokesSurface
          depth
          stokesLoop
          stokesBoundaryWord
    ; interpretedSelectedWordActionIsIdentity =
        refl
    ; crtBoundaryWordFoldConcatenationInterface =
        canonicalCRTBoundaryWordFoldConcatenationInterface
    ; crtBoundaryWordFoldConcatenationInterfaceIsCanonical =
        refl
    ; acceptedAsCRTStokesSpecialisation =
        false
    ; acceptedAsCRTStokesSpecialisationIsFalse =
        refl
    ; firstMissingSemanticLaw =
        missingStokesBoundaryWordInterpreterLawForCRTBoundary
    ; firstMissingSemanticLawIsBoundaryInterpreterLaw =
        refl
    ; exactNarrowingBoundary =
        "A raw function from the local Stokes boundary-word type to CRT edge words is typeable"
        ∷ "The canonical erasing interpreter maps every local boundary word to the empty CRT boundary word"
        ∷ "The empty CRT word witness transports the selected erased word to identity CRT boundary action"
        ∷ "The CRT-side boundary-word fold has a pointwise append law over list concatenation"
        ∷ "That erasing interpreter is not accepted as a CRT Stokes specialisation"
        ∷ "The first semantic law still needs a non-erasing local boundary-word algebra and interpreter law for the CRT boundary construction"
        ∷ []
    }

record CRTDiscreteStokesSpecialisationAdapterRequest : Set₁ where
  field
    localStokesSurface :
      RA.LocalDiscreteNonabelianStokesProofSurface

    depth :
      Nat

    stokesLoop :
      RA.LocalDiscreteNonabelianStokesProofSurface.LoopAtDepth
        localStokesSurface
        depth

    stokesSurfaceFilling :
      RA.LocalDiscreteNonabelianStokesProofSurface.SurfaceFillingAtDepth
        localStokesSurface
        depth
        stokesLoop

    stokesBoundaryWord :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop

    crtCell :
      CRTMonodromy3Cell

    stokesBoundaryWordInterpreter :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop →
      List CRTMonodromy1Edge

    stokesBoundaryWordAppend :
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop →
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop →
      RA.LocalDiscreteNonabelianStokesProofSurface.BoundaryWordAtDepth
        localStokesSurface
        depth
        stokesLoop

    stokesBoundaryWordInterpreterAppendLaw :
      StokesBoundaryWordInterpreterHomomorphismLawType
        localStokesSurface
        depth
        stokesLoop
        stokesBoundaryWordInterpreter
        stokesBoundaryWordAppend

    stokesBoundaryWordInterpretsAsCRTBoundary :
      stokesBoundaryWordInterpreter stokesBoundaryWord
      ≡
      crtMonodromyBoundaryOfBoundaryWord crtCell

    interpretedBoundaryAction :
      CRTBoundaryWordAction

    interpretedBoundaryActionIsCRTWordAction :
      interpretedBoundaryAction
      ≡
      crtMonodromyBoundaryWordAction
        (stokesBoundaryWordInterpreter stokesBoundaryWord)

    interpretedBoundaryActionIsIdentity :
      interpretedBoundaryAction
      ≡
      identityCRTBoundaryWordAction

    crtBoundaryWordFoldConcatenationInterface :
      CRTBoundaryWordFoldConcatenationInterface

    crtBoundaryWordFoldConcatenationInterfaceIsCanonical :
      crtBoundaryWordFoldConcatenationInterface
      ≡
      canonicalCRTBoundaryWordFoldConcatenationInterface

    exactSpecialisationBoundary :
      List String

data DiscreteStokesBianchiMissingPrimitive : Set where
  missingCRTMonodromy3CellBoundaryCarrier :
    DiscreteStokesBianchiMissingPrimitive
  missingBoundaryOfBoundaryZeroForCRTMonodromy :
    DiscreteStokesBianchiMissingPrimitive
  missingBoundaryWordToCRTHolonomyAction :
    DiscreteStokesBianchiMissingPrimitive
  missingDiscreteStokesSpecialisationToCRTConnection :
    DiscreteStokesBianchiMissingPrimitive
  missingBoundaryHolonomyToCyclicCovariantDerivative :
    DiscreteStokesBianchiMissingPrimitive

canonicalDiscreteStokesBianchiMissingPrimitives :
  List DiscreteStokesBianchiMissingPrimitive
canonicalDiscreteStokesBianchiMissingPrimitives =
  missingDiscreteStokesSpecialisationToCRTConnection
  ∷ missingBoundaryHolonomyToCyclicCovariantDerivative
  ∷ []

data DiscreteStokesBianchiUnsupportedClaim : Set where
  unsupportedBoundaryOfBoundaryZeroClaim :
    DiscreteStokesBianchiUnsupportedClaim
  unsupportedDiscreteStokesToBianchiClaim :
    DiscreteStokesBianchiUnsupportedClaim
  unsupportedCyclicCovariantDerivativeClaim :
    DiscreteStokesBianchiUnsupportedClaim
  unsupportedEinsteinEquationClosureClaim :
    DiscreteStokesBianchiUnsupportedClaim
  unsupportedGRPromotionClaim :
    DiscreteStokesBianchiUnsupportedClaim

canonicalDiscreteStokesBianchiUnsupportedClaims :
  List DiscreteStokesBianchiUnsupportedClaim
canonicalDiscreteStokesBianchiUnsupportedClaims =
  unsupportedDiscreteStokesToBianchiClaim
  ∷ unsupportedCyclicCovariantDerivativeClaim
  ∷ unsupportedEinsteinEquationClosureClaim
  ∷ unsupportedGRPromotionClaim
  ∷ []

record DiscreteStokesBianchiObstruction : Set₁ where
  field
    status :
      DiscreteStokesBianchiStatus

    discreteConnectionCandidate :
      DCRT.DiscreteConnectionCandidateFromCRT

    discreteConnectionCandidateIsCanonical :
      discreteConnectionCandidate
      ≡
      DCRT.canonicalDiscreteConnectionCandidateFromCRT

    discreteRicciCandidate :
      Ricci.GRDiscreteRicciCandidateFromCurvature

    discreteRicciCandidateIsCanonical :
      discreteRicciCandidate
      ≡
      Ricci.canonicalGRDiscreteRicciCandidateFromCurvature

    primeFiniteDifferenceBianchiSurface :
      DBIS.PrimeCarrierFiniteDifferenceBianchiSurface

    primeFiniteDifferenceBianchiSurfaceIsCanonical :
      primeFiniteDifferenceBianchiSurface
      ≡
      DBIS.canonicalPrimeCarrierFiniteDifferenceBianchiSurface

    primeDifferenceAdapterStatus :
      DBIS.PrimeDifferenceToRiemannConnectionAdapterStatus

    crtBoundaryOfBoundaryCarrier :
      CRTMonodromyBoundaryOfBoundaryCarrier

    crtBoundaryOfBoundaryCarrierIsCanonical :
      crtBoundaryOfBoundaryCarrier
      ≡
      canonicalCRTMonodromyBoundaryOfBoundaryCarrier

    crtBoundaryOfBoundaryWord :
      List CRTMonodromy1Edge

    crtBoundaryOfBoundaryWordIsEmpty :
      crtBoundaryOfBoundaryWord ≡ []

    crtBoundaryWordToHolonomyTransport :
      CRTBoundaryWordToHolonomyTransport

    crtBoundaryWordToHolonomyTransportIsCanonical :
      crtBoundaryWordToHolonomyTransport
      ≡
      canonicalCRTBoundaryWordToHolonomyTransport

    crtBoundaryWordFoldConcatenationInterface :
      CRTBoundaryWordFoldConcatenationInterface

    crtBoundaryWordFoldConcatenationInterfaceIsCanonical :
      crtBoundaryWordFoldConcatenationInterface
      ≡
      canonicalCRTBoundaryWordFoldConcatenationInterface

    crtBoundaryWordFoldAppendLawAvailable :
      Bool

    crtBoundaryWordFoldAppendLawAvailableIsTrue :
      crtBoundaryWordFoldAppendLawAvailable ≡ true

    crtBoundaryWordHolonomyTraceHomomorphism :
      CRTBoundaryWordHolonomyTraceHomomorphism

    crtBoundaryWordHolonomyTraceHomomorphismIsCanonical :
      crtBoundaryWordHolonomyTraceHomomorphism
      ≡
      canonicalCRTBoundaryWordHolonomyTraceHomomorphism

    crtBoundaryOfBoundaryAction :
      CRTBoundaryWordAction

    crtBoundaryOfBoundaryActionIsIdentity :
      crtBoundaryOfBoundaryAction ≡ identityCRTBoundaryWordAction

    exactAdapterRemainingPrimitive :
      DBIS.PrimeDifferenceToRiemannConnectionAdapterMissingPrimitive

    exactAdapterRemainingPrimitiveIsNonFlatWitness :
      exactAdapterRemainingPrimitive
      ≡
      DBIS.missingAdapterNonFlatWitnessForAlignedRequest

    localDiscreteStokesInterfaceName :
      String

    crtDiscreteStokesSpecialisationAdapterRequestName :
      String

    exactCRTDiscreteStokesSpecialisationMissingFields :
      List CRTDiscreteStokesSpecialisationMissingField

    exactCRTDiscreteStokesSpecialisationMissingFieldsAreCanonical :
      exactCRTDiscreteStokesSpecialisationMissingFields
      ≡
      canonicalCRTDiscreteStokesSpecialisationMissingFields

    crtDiscreteStokesSpecialisationFirstMissingField :
      CRTDiscreteStokesSpecialisationMissingField

    crtDiscreteStokesSpecialisationFirstMissingFieldIsBoundaryWordInterpreter :
      crtDiscreteStokesSpecialisationFirstMissingField
      ≡
      missingStokesBoundaryWordInterpreterToCRTBoundaryWord

    stokesBoundaryWordInterpreterTypeName :
      String

    stokesBoundaryWordInterpreterHomomorphismLawTypeName :
      String

    localBoundaryWordAtDepthStructuralInterfaceName :
      String

    localBoundaryWordAtDepthAppendFoldAvailable :
      Bool

    localBoundaryWordAtDepthAppendFoldAvailableIsTrue :
      localBoundaryWordAtDepthAppendFoldAvailable ≡ true

    nonErasingStokesBoundaryWordInterpreterPrimitiveRequestName :
      String

    exactRemainingStokesBoundaryWordPrimitiveName :
      String

    erasingStokesBoundaryWordInterpreterTyped :
      Bool

    erasingStokesBoundaryWordInterpreterTypedIsTrue :
      erasingStokesBoundaryWordInterpreterTyped ≡ true

    erasingStokesBoundaryWordInterpreterAppendLawAvailable :
      Bool

    erasingStokesBoundaryWordInterpreterAppendLawAvailableIsTrue :
      erasingStokesBoundaryWordInterpreterAppendLawAvailable ≡ true

    erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation :
      Bool

    erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisationIsFalse :
      erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation
      ≡
      false

    firstMissingSemanticLawAfterTypedInterpreter :
      CRTDiscreteStokesSpecialisationMissingField

    firstMissingSemanticLawAfterTypedInterpreterIsBoundaryInterpreterLaw :
      firstMissingSemanticLawAfterTypedInterpreter
      ≡
      missingStokesBoundaryWordInterpreterLawForCRTBoundary

    localBoundaryWordAtDepthSemanticPrimitiveRequestTypeName :
      String

    localToCRTBoundaryWordSemanticAlignmentRequest :
      LocalToCRTBoundaryWordSemanticAlignmentRequest

    localToCRTBoundaryWordSemanticAlignmentRequestIsCanonical :
      localToCRTBoundaryWordSemanticAlignmentRequest
      ≡
      canonicalLocalToCRTBoundaryWordSemanticAlignmentRequest

    localToCRTBoundaryWordSemanticAlignmentRequestName :
      String

    exactLocalToCRTBoundaryWordSemanticAlignmentMissingEvidence :
      List LocalToCRTBoundaryWordSemanticAlignmentMissingEvidence

    exactLocalToCRTBoundaryWordSemanticAlignmentMissingEvidenceIsCanonical :
      exactLocalToCRTBoundaryWordSemanticAlignmentMissingEvidence
      ≡
      canonicalLocalToCRTBoundaryWordSemanticAlignmentMissingEvidence

    localToCRTBoundaryWordSemanticAlignmentFirstMissingEvidence :
      LocalToCRTBoundaryWordSemanticAlignmentMissingEvidence

    localToCRTBoundaryWordSemanticAlignmentFirstMissingEvidenceIsLabelToCRTEdge :
      localToCRTBoundaryWordSemanticAlignmentFirstMissingEvidence
      ≡
      missingLocalBoundaryWordEdgeLabelingIntoCRTMonodromyEdges

    selectedLocalCRTBoundaryShellWordWrapperName :
      String

    selectedLocalCRTBoundaryShellWordConstructibleFromSuppliedEvidence :
      Bool

    selectedLocalCRTBoundaryShellWordConstructibleFromSuppliedEvidenceIsTrue :
      selectedLocalCRTBoundaryShellWordConstructibleFromSuppliedEvidence
      ≡
      true

    genericBoundaryEdgeCRTShellCompatibility :
      GenericBoundaryEdgeCRTShellCompatibility

    genericBoundaryEdgeCRTShellCompatibilityIsCanonical :
      genericBoundaryEdgeCRTShellCompatibility
      ≡
      canonicalGenericBoundaryEdgeCRTShellCompatibility

    nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism :
      NativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism

    nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphismIsCanonical :
      nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism
      ≡
      canonicalNativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism

    genericBoundaryEdgeShellMapsToNativeShell :
      Bool

    genericBoundaryEdgeShellMapsToNativeShellIsTrue :
      genericBoundaryEdgeShellMapsToNativeShell ≡ true

    localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingRequestName :
      String

    localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealization :
      Bool

    localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealizationIsTrue :
      localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealization
      ≡
      true

    genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterface :
      Bool

    genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterfaceIsFalse :
      genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterface
      ≡
      false

    realAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest :
      RealAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest

    realAnalysisLocalBoundaryEdgeWordConstructorExtensionRequestIsCanonical :
      realAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest
      ≡
      canonicalRealAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest

    finalNativeLocalBoundaryLabelCRTCompatibilityRequest :
      FinalNativeLocalBoundaryLabelCRTCompatibilityRequest

    finalNativeLocalBoundaryLabelCRTCompatibilityRequestIsCanonical :
      finalNativeLocalBoundaryLabelCRTCompatibilityRequest
      ≡
      canonicalFinalNativeLocalBoundaryLabelCRTCompatibilityRequest

    nativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger :
      NativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger

    nativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedgerIsCanonical :
      nativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger
      ≡
      canonicalNativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger

    nativeLocalBoundaryLabelShellSelectionInhabitedFromCurrentData :
      Bool

    nativeLocalBoundaryLabelShellSelectionInhabitedFromCurrentDataIsFalse :
      nativeLocalBoundaryLabelShellSelectionInhabitedFromCurrentData
      ≡
      false

    finalLocalBoundaryEdgeLabelRealizationIrreducibilityLedgerName :
      String

    finalLocalBoundaryEdgeLabelRealizationIrreducibilityLedgerAvailable :
      Bool

    finalLocalBoundaryEdgeLabelRealizationIrreducibilityLedgerAvailableIsTrue :
      finalLocalBoundaryEdgeLabelRealizationIrreducibilityLedgerAvailable
      ≡
      true

    nativeBoundaryEdgeLabelLocalRealizationInhabitedFromArbitraryInterface :
      Bool

    nativeBoundaryEdgeLabelLocalRealizationInhabitedFromArbitraryInterfaceIsFalse :
      nativeBoundaryEdgeLabelLocalRealizationInhabitedFromArbitraryInterface
      ≡
      false

    finalLocalBoundaryEdgeLabelRealizationFirstIrreducibleBlocker :
      FinalLocalBoundaryEdgeLabelRealizationIrreducibleBlocker

    finalLocalBoundaryEdgeLabelRealizationFirstIrreducibleBlockerIsSetField :
      finalLocalBoundaryEdgeLabelRealizationFirstIrreducibleBlocker
      ≡
      localBoundaryEdgeLabelIsOnlyASetField

    exactRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFields :
      List RealAnalysisLocalBoundaryEdgeWordConstructorRequiredField

    exactRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFieldsAreCanonical :
      exactRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFields
      ≡
      canonicalRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFields

    localBoundaryWordAtDepthOpaquePrimitiveRequestTypeName :
      String

    localDiscreteStokesReceiptAvailable :
      Bool

    localDiscreteStokesReceiptAvailableIsTrue :
      localDiscreteStokesReceiptAvailable ≡ true

    analyticStokesStillAuthoritySocket :
      Bool

    analyticStokesStillAuthoritySocketIsTrue :
      analyticStokesStillAuthoritySocket ≡ true

    exactMissingPrimitives :
      List DiscreteStokesBianchiMissingPrimitive

    exactMissingPrimitivesAreCanonical :
      exactMissingPrimitives
      ≡
      canonicalDiscreteStokesBianchiMissingPrimitives

    firstMissingPrimitive :
      DiscreteStokesBianchiMissingPrimitive

    firstMissingPrimitiveIsBoundaryWordToHolonomyAction :
      firstMissingPrimitive
      ≡
      missingDiscreteStokesSpecialisationToCRTConnection

    firstMissingTheoremName :
      String

    unsupportedClaims :
      List DiscreteStokesBianchiUnsupportedClaim

    unsupportedClaimsAreCanonical :
      unsupportedClaims
      ≡
      canonicalDiscreteStokesBianchiUnsupportedClaims

    obstructionBoundary :
      List String

    noPromotionBoundary :
      List String

canonicalDiscreteStokesBianchiObstruction :
  DiscreteStokesBianchiObstruction
canonicalDiscreteStokesBianchiObstruction =
  record
    { status =
        exactCRTBoundaryWordHolonomyTransportCyclicBridgeMissing
    ; discreteConnectionCandidate =
        DCRT.canonicalDiscreteConnectionCandidateFromCRT
    ; discreteConnectionCandidateIsCanonical =
        refl
    ; discreteRicciCandidate =
        Ricci.canonicalGRDiscreteRicciCandidateFromCurvature
    ; discreteRicciCandidateIsCanonical =
        refl
    ; primeFiniteDifferenceBianchiSurface =
        DBIS.canonicalPrimeCarrierFiniteDifferenceBianchiSurface
    ; primeFiniteDifferenceBianchiSurfaceIsCanonical =
        refl
    ; primeDifferenceAdapterStatus =
        DBIS.alignedRequestAndAdapterLawsAvailableNonFlatWitnessMissing
    ; crtBoundaryOfBoundaryCarrier =
        canonicalCRTMonodromyBoundaryOfBoundaryCarrier
    ; crtBoundaryOfBoundaryCarrierIsCanonical =
        refl
    ; crtBoundaryOfBoundaryWord =
        CRTMonodromyBoundaryOfBoundaryCarrier.boundaryOfBoundaryWord
          canonicalCRTMonodromyBoundaryOfBoundaryCarrier
          (CRTMonodromyBoundaryOfBoundaryCarrier.cell3
            canonicalCRTMonodromyBoundaryOfBoundaryCarrier)
    ; crtBoundaryOfBoundaryWordIsEmpty =
        refl
    ; crtBoundaryWordToHolonomyTransport =
        canonicalCRTBoundaryWordToHolonomyTransport
    ; crtBoundaryWordToHolonomyTransportIsCanonical =
        refl
    ; crtBoundaryWordFoldConcatenationInterface =
        canonicalCRTBoundaryWordFoldConcatenationInterface
    ; crtBoundaryWordFoldConcatenationInterfaceIsCanonical =
        refl
    ; crtBoundaryWordFoldAppendLawAvailable =
        true
    ; crtBoundaryWordFoldAppendLawAvailableIsTrue =
        refl
    ; crtBoundaryWordHolonomyTraceHomomorphism =
        canonicalCRTBoundaryWordHolonomyTraceHomomorphism
    ; crtBoundaryWordHolonomyTraceHomomorphismIsCanonical =
        refl
    ; crtBoundaryOfBoundaryAction =
        CRTBoundaryWordToHolonomyTransport.boundaryOfBoundaryAction
          canonicalCRTBoundaryWordToHolonomyTransport
          crtMonodromyCube
    ; crtBoundaryOfBoundaryActionIsIdentity =
        refl
    ; exactAdapterRemainingPrimitive =
        DBIS.PrimeDifferenceToRiemannConnectionAdapterReceipt.firstMissingAdapterPrimitive
          DBIS.canonicalPrimeDifferenceToRiemannConnectionAdapterReceipt
    ; exactAdapterRemainingPrimitiveIsNonFlatWitness =
        refl
    ; localDiscreteStokesInterfaceName =
        "DASHI.Foundations.RealAnalysisAxioms.LocalDiscreteNonabelianStokesProofSurface"
    ; crtDiscreteStokesSpecialisationAdapterRequestName =
        "CRTDiscreteStokesSpecialisationAdapterRequest"
    ; exactCRTDiscreteStokesSpecialisationMissingFields =
        canonicalCRTDiscreteStokesSpecialisationMissingFields
    ; exactCRTDiscreteStokesSpecialisationMissingFieldsAreCanonical =
        refl
    ; crtDiscreteStokesSpecialisationFirstMissingField =
        missingStokesBoundaryWordInterpreterToCRTBoundaryWord
    ; crtDiscreteStokesSpecialisationFirstMissingFieldIsBoundaryWordInterpreter =
        refl
    ; stokesBoundaryWordInterpreterTypeName =
        "StokesBoundaryWordInterpreterType : BoundaryWordAtDepth surface depth loop -> List CRTMonodromy1Edge"
    ; stokesBoundaryWordInterpreterHomomorphismLawTypeName =
        "StokesBoundaryWordInterpreterHomomorphismLawType : interpreter (append left right) == interpreter left ++ interpreter right"
    ; localBoundaryWordAtDepthStructuralInterfaceName =
        "LocalBoundaryWordAtDepthStructuralInterface : BoundaryWordAtDepth append plus fold/eliminator exposed by RealAnalysisAxioms"
    ; localBoundaryWordAtDepthAppendFoldAvailable =
        true
    ; localBoundaryWordAtDepthAppendFoldAvailableIsTrue =
        refl
    ; nonErasingStokesBoundaryWordInterpreterPrimitiveRequestName =
        "NonErasingStokesBoundaryWordInterpreterPrimitiveRequest"
    ; exactRemainingStokesBoundaryWordPrimitiveName =
        "missing non-erasing BoundaryWordAtDepth interpreter law identifying a selected local Stokes boundary word with the CRT boundary shell word"
    ; erasingStokesBoundaryWordInterpreterTyped =
        true
    ; erasingStokesBoundaryWordInterpreterTypedIsTrue =
        refl
    ; erasingStokesBoundaryWordInterpreterAppendLawAvailable =
        true
    ; erasingStokesBoundaryWordInterpreterAppendLawAvailableIsTrue =
        refl
    ; erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation =
        false
    ; erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisationIsFalse =
        refl
    ; firstMissingSemanticLawAfterTypedInterpreter =
        missingStokesBoundaryWordInterpreterLawForCRTBoundary
    ; firstMissingSemanticLawAfterTypedInterpreterIsBoundaryInterpreterLaw =
        refl
    ; localBoundaryWordAtDepthSemanticPrimitiveRequestTypeName =
        "LocalToCRTBoundaryWordSemanticAlignment"
    ; localToCRTBoundaryWordSemanticAlignmentRequest =
        canonicalLocalToCRTBoundaryWordSemanticAlignmentRequest
    ; localToCRTBoundaryWordSemanticAlignmentRequestIsCanonical =
        refl
    ; localToCRTBoundaryWordSemanticAlignmentRequestName =
        "LocalToCRTBoundaryWordSemanticAlignment"
    ; exactLocalToCRTBoundaryWordSemanticAlignmentMissingEvidence =
        canonicalLocalToCRTBoundaryWordSemanticAlignmentMissingEvidence
    ; exactLocalToCRTBoundaryWordSemanticAlignmentMissingEvidenceIsCanonical =
        refl
    ; localToCRTBoundaryWordSemanticAlignmentFirstMissingEvidence =
        missingLocalBoundaryWordEdgeLabelingIntoCRTMonodromyEdges
    ; localToCRTBoundaryWordSemanticAlignmentFirstMissingEvidenceIsLabelToCRTEdge =
        refl
    ; selectedLocalCRTBoundaryShellWordWrapperName =
        "SelectedLocalCRTBoundaryShellWord"
    ; selectedLocalCRTBoundaryShellWordConstructibleFromSuppliedEvidence =
        true
    ; selectedLocalCRTBoundaryShellWordConstructibleFromSuppliedEvidenceIsTrue =
        refl
    ; genericBoundaryEdgeCRTShellCompatibility =
        canonicalGenericBoundaryEdgeCRTShellCompatibility
    ; genericBoundaryEdgeCRTShellCompatibilityIsCanonical =
        refl
    ; nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism =
        canonicalNativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism
    ; nativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphismIsCanonical =
        refl
    ; genericBoundaryEdgeShellMapsToNativeShell =
        true
    ; genericBoundaryEdgeShellMapsToNativeShellIsTrue =
        refl
    ; localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingRequestName =
        "LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding"
    ; localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealization =
        true
    ; localBoundaryEdgeLabelGenericBoundaryEdgeEmbeddingDerivesNativeRealizationIsTrue =
        refl
    ; genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterface =
        false
    ; genericBoundaryEdgeLocalRealizationInhabitedFromArbitraryInterfaceIsFalse =
        refl
    ; realAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest =
        canonicalRealAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest
    ; realAnalysisLocalBoundaryEdgeWordConstructorExtensionRequestIsCanonical =
        refl
    ; finalNativeLocalBoundaryLabelCRTCompatibilityRequest =
        canonicalFinalNativeLocalBoundaryLabelCRTCompatibilityRequest
    ; finalNativeLocalBoundaryLabelCRTCompatibilityRequestIsCanonical =
        refl
    ; nativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger =
        canonicalNativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedger
    ; nativeLocalBoundaryLabelShellSelectionCurrentDataAbsenceLedgerIsCanonical =
        refl
    ; nativeLocalBoundaryLabelShellSelectionInhabitedFromCurrentData =
        false
    ; nativeLocalBoundaryLabelShellSelectionInhabitedFromCurrentDataIsFalse =
        refl
    ; finalLocalBoundaryEdgeLabelRealizationIrreducibilityLedgerName =
        "FinalLocalBoundaryEdgeLabelRealizationIrreducibilityLedger"
    ; finalLocalBoundaryEdgeLabelRealizationIrreducibilityLedgerAvailable =
        true
    ; finalLocalBoundaryEdgeLabelRealizationIrreducibilityLedgerAvailableIsTrue =
        refl
    ; nativeBoundaryEdgeLabelLocalRealizationInhabitedFromArbitraryInterface =
        false
    ; nativeBoundaryEdgeLabelLocalRealizationInhabitedFromArbitraryInterfaceIsFalse =
        refl
    ; finalLocalBoundaryEdgeLabelRealizationFirstIrreducibleBlocker =
        localBoundaryEdgeLabelIsOnlyASetField
    ; finalLocalBoundaryEdgeLabelRealizationFirstIrreducibleBlockerIsSetField =
        refl
    ; exactRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFields =
        canonicalRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFields
    ; exactRealAnalysisLocalBoundaryEdgeWordConstructorRequiredFieldsAreCanonical =
        refl
    ; localBoundaryWordAtDepthOpaquePrimitiveRequestTypeName =
        "LocalToCRTBoundaryWordSemanticAlignment refines the old NonErasingStokesBoundaryWordInterpreterPrimitiveRequest"
    ; localDiscreteStokesReceiptAvailable =
        true
    ; localDiscreteStokesReceiptAvailableIsTrue =
        refl
    ; analyticStokesStillAuthoritySocket =
        true
    ; analyticStokesStillAuthoritySocketIsTrue =
        refl
    ; exactMissingPrimitives =
        canonicalDiscreteStokesBianchiMissingPrimitives
    ; exactMissingPrimitivesAreCanonical =
        refl
    ; firstMissingPrimitive =
        missingDiscreteStokesSpecialisationToCRTConnection
    ; firstMissingPrimitiveIsBoundaryWordToHolonomyAction =
        refl
    ; firstMissingTheoremName =
        "DiscreteStokesSpecialisationToCRTConnection"
    ; unsupportedClaims =
        canonicalDiscreteStokesBianchiUnsupportedClaims
    ; unsupportedClaimsAreCanonical =
        refl
    ; obstructionBoundary =
        "RealAnalysisAxioms exposes LocalDiscreteNonabelianStokesProofSurface as a local Nat/telescoping receipt"
        ∷ "RealAnalysisAxioms also exposes discreteStokesTheoremAxiom as an authority socket"
        ∷ "DiscreteBianchiIdentitySurface supplies prime finite-difference commutation and an aligned FactorVec/SSP adapter-law receipt"
        ∷ "The exact remaining adapter blocker is missingAdapterNonFlatWitnessForAlignedRequest"
        ∷ "This module now supplies a formal CRT 3-cell boundary carrier and definitional boundary-of-boundary-zero word"
        ∷ "This module now transports the formal boundary word to crtMonodromyHolonomy and CRTMonodromyConnection actions"
        ∷ "The formal boundary-of-boundary action is definitionally identity because the transported word is empty"
        ∷ "The CRT-side boundary shell now has a holonomy trace homomorphism preserving list concatenation"
        ∷ "The CRT-side boundary shell word is retained as a non-erasing edge word, separate from the empty boundary-of-boundary word"
        ∷ "A raw StokesBoundaryWordInterpreterType is now exposed, and an erasing fallback maps any local boundary word to the empty CRT word"
        ∷ "The CRT boundary-word fold now carries a typed pointwise append law over list concatenation"
        ∷ "For any supplied local BoundaryWordAtDepth append, the erasing interpreter satisfies the homomorphism shape trivially"
        ∷ "The erasing fallback is not accepted as the CRT Stokes specialisation because it does not prove the semantic boundary-word law"
        ∷ "RealAnalysisAxioms now exposes a local BoundaryWordAtDepth append plus fold/eliminator interface"
        ∷ "The exact typed primitive request is narrowed to LocalToCRTBoundaryWordSemanticAlignment because native local edge labels still need a CRT label map and selected label preimage of the CRT boundary shell"
        ∷ "A supplied-evidence constructor now packages LocalToCRTBoundaryWordSemanticAlignmentPrimitive only after the missing local semantic evidence is provided"
        ∷ "SelectedLocalCRTBoundaryShellWord exposes the selected local word, CRT edge labels, non-erasing shell witness, append law, fold/list law, and holonomy trace from supplied CRT semantic evidence"
        ∷ "RealAnalysisAxioms now provides the native local edge-label constructor, constructor round-trip, and mapped fold/list fields requested by RealAnalysisLocalBoundaryEdgeWordConstructorExtensionRequest"
        ∷ "FinalNativeLocalBoundaryLabelCRTCompatibility names the exact remaining CRT-label compatibility needed after the native local word syntax"
        ∷ "NativeBoundaryEdgeLabel now supplies edgeP2 edgeP3 edgeJ constructors, a canonical label-to-CRT-edge map, and a native CRT shell label word"
        ∷ "GenericBoundaryEdge now supplies P2 P3 J constructors and a selected shell word that maps definitionally to the native CRT shell"
        ∷ "NativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism proves native/generic P2/P3/J round trips and CRT-label compatibility"
        ∷ "A supplied LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding derives NativeBoundaryEdgeLabelLocalRealization through the native/generic isomorphism"
        ∷ "A supplied NativeBoundaryEdgeLabelLocalRealization now derives NativeLocalBoundaryLabelShellSelection and SelectedLocalCRTBoundaryShellWord"
        ∷ "Given a native label shell selection, the local-to-CRT interpreter, selected word compatibility, non-erasing witness, append law, and fold/list law are derived from native local edge labels"
        ∷ "The native shell-selection attempt from current label/list data is recorded as blocked on realizing the native edge labels inside the current local label carrier"
        ∷ "The final irreducibility ledger records that arbitrary localBoundaryEdgeLabel is only a Set field with no label constructor, no NativeBoundaryEdgeLabel realizer, no CRT-edge eliminator, and no selected CRT-shell preimage"
        ∷ "The absence ledger now pins the remaining blocker on the CRT label map and selected-shell label preimage, not on the local word syntax API"
        ∷ "Neither surface transports boundary-of-boundary cancellation to the cyclic covariant-derivative Bianchi expression"
        ∷ []
    ; noPromotionBoundary =
        "This obstruction does not prove discrete Stokes for the CRT connection"
        ∷ "The erasing boundary-word interpreter is a typed fallback only and is not a CRT Stokes specialisation"
        ∷ "LocalToCRTBoundaryWordSemanticAlignment records the exact semantic BoundaryWordAtDepth request and remains uninhabited here"
        ∷ "FinalNativeLocalBoundaryLabelCRTCompatibility is a required interface, not supplied CRT label-map/preimage evidence"
        ∷ "NativeLocalBoundaryLabelShellSelection is derivable from supplied NativeBoundaryEdgeLabelLocalRealization evidence, but remains uninhabited from current local label/list data alone"
        ∷ "GenericBoundaryEdgeCRTShellCompatibility bridges generic P2/P3/J labels to the native CRT shell, but not to arbitrary localBoundaryEdgeLabel values"
        ∷ "NativeBoundaryEdgeLabelGenericBoundaryEdgeIsomorphism is inhabited, but LocalBoundaryEdgeLabelGenericBoundaryEdgeEmbedding is still required to realize generic labels inside arbitrary local labels"
        ∷ "NativeBoundaryEdgeLabelLocalRealization is not derivable for arbitrary LocalBoundaryWordAtDepthStructuralInterface.localBoundaryEdgeLabel"
        ∷ "CRTDiscreteStokesSpecialisationAdapterRequest still requires a non-erasing local boundary-word interpreter append law and remains uninhabited"
        ∷ "This obstruction proves only the formal carrier boundary-of-boundary word and its formal CRT holonomy action, not a cyclic covariant derivative"
        ∷ "This obstruction does not prove the discrete Bianchi identity"
        ∷ "This obstruction does not prove contracted Bianchi, Einstein equations, continuum GR, terminal, or Clay closure"
        ∷ []
    }

discreteStokesBianchiObstructionExactStatus :
  DiscreteStokesBianchiObstruction.status
    canonicalDiscreteStokesBianchiObstruction
  ≡
  exactCRTBoundaryWordHolonomyTransportCyclicBridgeMissing
discreteStokesBianchiObstructionExactStatus = refl

discreteStokesBianchiObstructionExactFirstMissing :
  DiscreteStokesBianchiObstruction.firstMissingPrimitive
    canonicalDiscreteStokesBianchiObstruction
  ≡
  missingDiscreteStokesSpecialisationToCRTConnection
discreteStokesBianchiObstructionExactFirstMissing = refl

discreteStokesBianchiObstructionBoundaryOfBoundaryWordIsEmpty :
  DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryWord
    canonicalDiscreteStokesBianchiObstruction
  ≡
  []
discreteStokesBianchiObstructionBoundaryOfBoundaryWordIsEmpty = refl

discreteStokesBianchiObstructionBoundaryOfBoundaryActionIsIdentity :
  DiscreteStokesBianchiObstruction.crtBoundaryOfBoundaryAction
    canonicalDiscreteStokesBianchiObstruction
  ≡
  identityCRTBoundaryWordAction
discreteStokesBianchiObstructionBoundaryOfBoundaryActionIsIdentity = refl

discreteStokesBianchiObstructionNoBoundaryOfBoundaryClaim :
  DiscreteStokesBianchiObstruction.unsupportedClaims
    canonicalDiscreteStokesBianchiObstruction
  ≡
  canonicalDiscreteStokesBianchiUnsupportedClaims
discreteStokesBianchiObstructionNoBoundaryOfBoundaryClaim = refl

discreteStokesBianchiObstructionExactAdapterRemainingPrimitive :
  DiscreteStokesBianchiObstruction.exactAdapterRemainingPrimitive
    canonicalDiscreteStokesBianchiObstruction
  ≡
  DBIS.missingAdapterNonFlatWitnessForAlignedRequest
discreteStokesBianchiObstructionExactAdapterRemainingPrimitive = refl

discreteStokesBianchiObstructionExactCRTStokesFirstMissingField :
  DiscreteStokesBianchiObstruction.crtDiscreteStokesSpecialisationFirstMissingField
    canonicalDiscreteStokesBianchiObstruction
  ≡
  missingStokesBoundaryWordInterpreterToCRTBoundaryWord
discreteStokesBianchiObstructionExactCRTStokesFirstMissingField = refl

discreteStokesBianchiObstructionErasingInterpreterNotAccepted :
  DiscreteStokesBianchiObstruction.erasingStokesBoundaryWordInterpreterAcceptedAsCRTStokesSpecialisation
    canonicalDiscreteStokesBianchiObstruction
  ≡
  false
discreteStokesBianchiObstructionErasingInterpreterNotAccepted = refl

discreteStokesBianchiObstructionFirstSemanticLawAfterTypedInterpreter :
  DiscreteStokesBianchiObstruction.firstMissingSemanticLawAfterTypedInterpreter
    canonicalDiscreteStokesBianchiObstruction
  ≡
  missingStokesBoundaryWordInterpreterLawForCRTBoundary
discreteStokesBianchiObstructionFirstSemanticLawAfterTypedInterpreter = refl

discreteStokesBianchiObstructionFinalLocalLabelRealizationStillBlocked :
  DiscreteStokesBianchiObstruction.nativeBoundaryEdgeLabelLocalRealizationInhabitedFromArbitraryInterface
    canonicalDiscreteStokesBianchiObstruction
  ≡
  false
discreteStokesBianchiObstructionFinalLocalLabelRealizationStillBlocked = refl

discreteStokesBianchiObstructionFinalLocalLabelRealizationFirstBlocker :
  DiscreteStokesBianchiObstruction.finalLocalBoundaryEdgeLabelRealizationFirstIrreducibleBlocker
    canonicalDiscreteStokesBianchiObstruction
  ≡
  localBoundaryEdgeLabelIsOnlyASetField
discreteStokesBianchiObstructionFinalLocalLabelRealizationFirstBlocker = refl
