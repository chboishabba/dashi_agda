module DASHI.Cognition.PNF.SensibLawTranscriptBoundaryPNFWorldManifoldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreClassifierExact as Legacy
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Residual

------------------------------------------------------------------------
-- Transcript-boundary interpretation as a fibre/manifold, not one scalar.
--
-- The previous runtime emitted a useful local cut score and then five fibre
-- scores.  Those are retained as observations, but they are not the semantic
-- carrier.  Repo-native PNF reasoning keeps candidate alternatives live and
-- lets source/world constraints intersect/refine the residual fibre.
------------------------------------------------------------------------

data ManifoldCoordinate : Set where
  syntaxContinuity : ManifoldCoordinate
  pnfResidualCompatibility : ManifoldCoordinate
  attributionCompatibility : ManifoldCoordinate
  speakerContinuity : ManifoldCoordinate
  worldModelCompatibility : ManifoldCoordinate
  asrIntegrity : ManifoldCoordinate
  rhetoricalContinuity : ManifoldCoordinate

record CoordinateObservation : Set where
  constructor coordinateObservation
  field
    coordinate : ManifoldCoordinate
    valueReference : String
    evidenceReference : String
    producerReference : String

open CoordinateObservation public

record BoundaryWorldPoint : Set where
  constructor boundaryWorldPoint
  field
    fibreKind : Legacy.BoundaryFibreKind
    coordinates : List CoordinateObservation
    pnfCandidateReference : String
    sentenceReference : String
    worldConstraintReference : String
    sourceConstraintReference : String
    residualReference : String

open BoundaryWorldPoint public

record BoundaryManifold : Set where
  constructor boundaryManifold
  field
    sourceSha256 : String
    sentenceReference : String
    splitReference : String
    points : List BoundaryWorldPoint
    paretoFrontReference : String
    retainedResidualReference : String
    legacyCutReceiptReference : String
    manifoldSchema : String

open BoundaryManifold public

------------------------------------------------------------------------
-- Ternary admission is consumer-relative and separate from coordinates.
------------------------------------------------------------------------

data ManifoldDisposition : Set where
  rejectPoint : ManifoldDisposition
  suspendPoint : ManifoldDisposition
  admitPoint : ManifoldDisposition

record ManifoldReview : Set where
  constructor manifoldReview
  field
    pointReference : String
    consumerReference : String
    disposition : ManifoldDisposition
    evidenceReference : String
    sourceOrWorldAuthorityReference : String
    alternativesStillOpenReference : String

open ManifoldReview public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ScalarCutScoreDeterminesFibre : Set where
scalarCutScoreDoesNotDetermineFibre : ScalarCutScoreDeterminesFibre → ⊥
scalarCutScoreDoesNotDetermineFibre ()

data TopLegacyFibreDeletesResidual : Set where
topLegacyFibreDoesNotDeleteResidual : TopLegacyFibreDeletesResidual → ⊥
topLegacyFibreDoesNotDeleteResidual ()

data ParetoFrontDeterminesWorldTruth : Set where
paretoFrontDoesNotDetermineWorldTruth : ParetoFrontDeterminesWorldTruth → ⊥
paretoFrontDoesNotDetermineWorldTruth ()

data SpeakerCompatibilityDeterminesIdentity : Set where
speakerCompatibilityDoesNotDetermineIdentity : SpeakerCompatibilityDeterminesIdentity → ⊥
speakerCompatibilityDoesNotDetermineIdentity ()

data LowPNFResidualProvesCorrectSegmentation : Set where
lowPNFResidualDoesNotProveCorrectSegmentation : LowPNFResidualProvesCorrectSegmentation → ⊥
lowPNFResidualDoesNotProveCorrectSegmentation ()

------------------------------------------------------------------------
-- Existing residual-fibre architecture is the semantic owner.
------------------------------------------------------------------------

semanticResidualBoundaryAnchor : Residual.SemanticResidualBoundary
semanticResidualBoundaryAnchor = Residual.canonicalSemanticResidualBoundary

record PNFWorldManifoldBoundary : Set where
  constructor pnfWorldManifoldBoundary
  field
    legacyScalarRetainedAsObservation : Bool
    fibrePointsRemainSimultaneouslyLive : Bool
    sourceWorldConstraintsMayRefineFibre : Bool
    sourceWorldConstraintsCreateTruth : Bool
    residualSurvivesSelection : Bool
    admissionIsConsumerRelative : Bool
    speakerIdentityRemainsIndependent : Bool

canonicalPNFWorldManifoldBoundary : PNFWorldManifoldBoundary
canonicalPNFWorldManifoldBoundary =
  pnfWorldManifoldBoundary true true true false true true true

------------------------------------------------------------------------
-- ABC regression references.
------------------------------------------------------------------------

sentence45ManifoldExpectation : String
sentence45ManifoldExpectation =
  "45:7: speaker point should lie on/near the live frontier, but ASR/rhetorical points remain residual until source-aligned speaker evidence pays identity"

sentence117ManifoldExpectation : String
sentence117ManifoldExpectation =
  "117:32: quote/nesting/rhetorical points should dominate speaker compatibility without collapsing to a single scalar winner"

sentence118ManifoldExpectation : String
sentence118ManifoldExpectation =
  "118: according-to region: attribution/nesting world point should survive source/world constraint intersection"
