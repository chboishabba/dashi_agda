module DASHI.Culture.CriticalArtSameSceneTransportExact where

------------------------------------------------------------------------
-- APPLICATION ONLY: original owners retain all formal mathematics.
-- A location/hash/attribution string is not a verified original film.
-- This owner makes missing source review an explicit dependent gate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.CriticalArtTemporalReceptionReuseExact as Art
import DASHI.Culture.IntellectualReceptionComposableFibreTransportPathExact as Path
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Time
import DASHI.Culture.IntellectualReceptionSupportPartitionRetainReopenExact as Selective
import DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact as Prefix
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Interop.WikidataDerivationSupportSquareExact as Square
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Algebra.TetralemmaBridge as Tet
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants

data ReviewStage : Set where
  candidate : ReviewStage
  independentOriginalReview : ReviewStage

record EditionSceneSource : Set where
  constructor editionSceneSource
  field
    work : String
    edition : String
    scene : String
    timecodeStart : String
    timecodeEnd : String
    originalSourceLocation : String
    originalBytesSHA256 : String
    originalCreatorAttribution : String
    reviewerReceipt : String
    reviewStage : ReviewStage

record ReviewedOriginalScene (source : EditionSceneSource) : Set where
  constructor reviewedOriginalScene
  field
    independentReview : EditionSceneSource.reviewStage source ≡ independentOriginalReview

candidateCannotClaimIndependentReview :
  candidate ≡ independentOriginalReview → ⊥
candidateCannotClaimIndependentReview ()

-- The concrete path is a dependent original Path.FibreTransportPath,
-- not an invented route or a pair of unverified time labels.
record SceneTemporalPath (source : EditionSceneSource)
    (start finish : Time.ReceptionTime) : Set where
  constructor sceneTemporalPath
  field
    reviewed : ReviewedOriginalScene source
    reception : Art.SourceIndexedArtReception
    selectedWork : Art.SourceIndexedArtReception.workIdentifier reception
      ≡ EditionSceneSource.work source
    selectedEdition : Art.SourceIndexedArtReception.editionIdentifier reception
      ≡ EditionSceneSource.edition source
    selectedScene : Art.SourceIndexedArtReception.sceneIdentifier reception
      ≡ EditionSceneSource.scene source
    path : Path.FibreTransportPath
      (Art.SourceIndexedArtReception.history reception)
      start finish
    finalIndex : Art.SourceIndexedArtReception.observationTime reception ≡ finish

-- Transport composition is inherited from the repository's original
-- history-indexed path owner, not reimplemented as an art-specific monoid.
scenePathComposition :
  ∀ {source start middle finish}
    (r : ReviewedOriginalScene source)
    (history : Time.TemporalReceptionHistory) →
  Path.FibreTransportPath history start middle →
  Path.FibreTransportPath history middle finish →
  Path.FibreTransportPath history start finish
scenePathComposition r history left right = Path.appendPath left right

-- These are the original selectivity proofs: a concrete film case must
-- first instantiate the right supported coordinates; it cannot assert
-- that every new observation reopens every interpretation.
unaffectedPresentFutureSupportCanBeRetained :
  Prefix.SupportContainedInSharedPrefix Prefix.presentFutureSupport
unaffectedPresentFutureSupportCanBeRetained =
  Prefix.presentFutureSupportContained

affectedAuthoritySupportReopensDownstream :
  Closure.ReopeningObligation
    Selective.AuthoritySensitiveReopening.Depends
    Selective.AuthoritySensitiveReopening.divergentCoordinateArtifact
    Selective.AuthoritySensitiveReopening.downstreamCertificate
affectedAuthoritySupportReopensDownstream =
  Selective.authoritySensitiveDownstreamReopens

-- Same original evidence square: the positive and negative updates
-- commute when starting at no support. This DOES NOT say path history
-- or human interpretation commutes.
sceneEvidenceSquareCommutes :
  Square.mergeSquare
    (Square.mergeSquare Square.ignoranceSquare Square.supportSquare)
    Square.contradictionSquare
  ≡
  Square.mergeSquare
    (Square.mergeSquare Square.ignoranceSquare Square.contradictionSquare)
    Square.supportSquare
sceneEvidenceSquareCommutes = refl

sceneConflictIsBoth :
  Four.polarPosition Square.conflictSquare ≡ Tet.both
sceneConflictIsBoth = Square.conflictPositionIsBoth

-- Two channels may be glued only with the five-coordinate interface
-- match AND the same selected work/edition/scene; the latter is extra
-- to the canonical physical/combinatorial pants interface.
record ArtPantsSeam (left right : EditionSceneSource)
    (leftChannel rightChannel : Pants.BranchChannel) : Set where
  constructor artPantsSeam
  field
    sameWork : EditionSceneSource.work left ≡ EditionSceneSource.work right
    sameEdition : EditionSceneSource.edition left ≡ EditionSceneSource.edition right
    sameScene : EditionSceneSource.scene left ≡ EditionSceneSource.scene right
    interface : Pants.InterfaceMatch leftChannel rightChannel
    leftReviewed : ReviewedOriginalScene left
    rightReviewed : ReviewedOriginalScene right

artPantsInterfaceAvailable :
  ∀ {left right leftChannel rightChannel} →
  ArtPantsSeam left right leftChannel rightChannel →
  Pants.InterfaceMatch leftChannel rightChannel
artPantsInterfaceAvailable seam = ArtPantsSeam.interface seam

-- An actual film witness requires an original, independently reviewed
-- source receipt. We intentionally provide no fabricated witness.
