module DASHI.Culture.CriticalArtTriadicFilmBoundaryExact where

------------------------------------------------------------------------
-- DASHI application to film studies: NO assertion that the film triangle
-- is the Peircean sign/object/interpretant itself. Actual scene claims
-- remain uninhabited until independent edition and scene verification.
--
-- Peirce's triadic semeiotic, Barthes' Third Meaning, Metz's cinematic
-- identification, Mulvey's gaze, Bordwell's narration, Murray Smith's
-- character engagement, and Sobchack's phenomenology are distinct
-- attributed theoretical sources; none authored these DASHI definitions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.CriticalArtSameSceneTransportExact as Scene
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

data FilmVertex : Set where
  diegeticAction : FilmVertex
  cinematicForm : FilmVertex
  situatedSpectator : FilmVertex

data PeirceanRole : Set where
  representamen : PeirceanRole
  object : PeirceanRole
  interpretant : PeirceanRole

-- A role translation is a documented *proposal*, not an identity.
-- The Peircean interpretant need not be a person, and a diegetic
-- character need not be the object of every sign.
record ProposedPeirceFilmTranslation : Set where
  constructor proposedPeirceFilmTranslation
  field
    sourceAttribution : String
    originalPassageLocator : String
    proposedMap : FilmVertex → PeirceanRole
    comparisonLimit : String

characterNotCameraRole :
  diegeticAction ≡ cinematicForm → ⊥
characterNotCameraRole ()

peirceanSignNotInterpretant :
  representamen ≡ interpretant → ⊥
peirceanSignNotInterpretant ()

record FilmTriadicReading (source : Scene.EditionSceneSource) : Set where
  constructor filmTriadicReading
  field
    originalSceneReviewed : Scene.ReviewedOriginalScene source
    dyadic : Face.TrialecticBoundary
    attachedFace : Face.TriadicFaceRelation
    criticOriginalAttribution : String
    interpretationEvidenceLocator : String

-- A single reviewed scene can admit distinct hypothetical interpretive
-- faces without changing its three dyadic observations. This is a
-- MATHEMATICAL non-descent in a model of possibilities, not empirical
-- proof that any actual viewers held both readings.
data ReadingChoice : Set where
  reciprocalReading : ReadingChoice
  coerciveReading : ReadingChoice

pairedDyads : ReadingChoice → Face.TrialecticBoundary
pairedDyads _ = Face.sharedPositiveBoundary

pairedFace : ReadingChoice → Face.TriadicFaceRelation
pairedFace reciprocalReading = Face.reciprocalFace
pairedFace coerciveReading = Face.coerciveFace

sameDyadsDifferentFace :
  pairedDyads reciprocalReading ≡ pairedDyads coerciveReading
sameDyadsDifferentFace = refl

differentSelectedFaces :
  pairedFace reciprocalReading ≡ pairedFace coerciveReading → ⊥
differentSelectedFaces ()

artTriadicFaceNonDescent :
  Descent.ConsumerNonDescentWitness pairedDyads pairedFace
artTriadicFaceNonDescent =
  Descent.consumerNonDescentWitness
    reciprocalReading coerciveReading
    sameDyadsDifferentFace differentSelectedFaces

artTriadicFaceDoesNotFactorThroughDyads :
  Descent.FactorsThrough pairedDyads pairedFace → ⊥
artTriadicFaceDoesNotFactorThroughDyads =
  Descent.nonDescentWitnessBlocksFactorization artTriadicFaceNonDescent

-- The possibility result is connected to a concrete source ONLY if
-- independent review is explicitly supplied. Nothing constructs such
-- a reviewed source here.
readingAtReviewedScene :
  (source : Scene.EditionSceneSource) →
  Scene.ReviewedOriginalScene source →
  ReadingChoice →
  String →
  String →
  FilmTriadicReading source
readingAtReviewedScene source reviewed reciprocalReading critic evidence =
  filmTriadicReading reviewed Face.sharedPositiveBoundary
    Face.reciprocalFace critic evidence
readingAtReviewedScene source reviewed coerciveReading critic evidence =
  filmTriadicReading reviewed Face.sharedPositiveBoundary
    Face.coerciveFace critic evidence

data FilmInterpretationProvesRealAudienceEffect : Set where
data FilmTriadIsPeirceanTriadByDefinition : Set where

noMeasuredEffectFromFilmTriad :
  FilmInterpretationProvesRealAudienceEffect → ⊥
noMeasuredEffectFromFilmTriad ()

noAutomaticPeirceanIdentification :
  FilmTriadIsPeirceanTriadByDefinition → ⊥
noAutomaticPeirceanIdentification ()
