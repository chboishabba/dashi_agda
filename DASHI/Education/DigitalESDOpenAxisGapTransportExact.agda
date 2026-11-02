module DASHI.Education.DigitalESDOpenAxisGapTransportExact where

------------------------------------------------------------------------
-- QUESTION-RELATIVE CROSS-STUDY GAP ROUTING ON THE EXISTING N-AXIS WORLD
--
-- One source may identify a gap, challenge an inference or suggest a
-- measurement in another source. That is NOT retroactive evidence about
-- the recipient's participants, period, outcomes or epistemic authority.
-- Cross-source source attribution remains with the original authors.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDStudyParseInteropExact as Parse
import DASHI.Education.DigitalESDERICStudyExecutionExact as ERIC
import DASHI.Education.DigitalESDStudyProcessingCensusExact as Census

data CrossStudyResearchUse : Set where
  pointsToGap : CrossStudyResearchUse
  suggestsMethod : CrossStudyResearchUse
  suppliesChallenge : CrossStudyResearchUse
  proposesConditionalComparison : CrossStudyResearchUse
  motivatesNewObservation : CrossStudyResearchUse

-- Non-vacuous higher-arity relation: there is at least one anchored part,
-- with any finite number of further parts. All of the world's axes remain
-- addressable; this relationship's axis list is just a selected projection.
record ScopedHigherRelation (scope : World.StudyWorldScope) : Set where
  constructor scoped-higher-relation
  field
    firstPart : World.StudyPart scope
    additionalParts : List (World.StudyPart scope)
    firstAxis : World.Axis scope
    additionalAxes : List (World.Axis scope)
    question : String
    attributionAndComparisonReference : String

open ScopedHigherRelation public

-- Adding axes does not rewrite or eliminate the old axis names. An
-- extension is an explicit embedding, not a bounded three-valued carrier.
record OpenAxisExtension (OldAxis NewAxis : Set) : Set₁ where
  constructor open-axis-extension
  field
    embed : OldAxis → NewAxis
    leftInverse : NewAxis → OldAxis
    originalAxisIsRecovered :
      (axis : OldAxis) → leftInverse (embed axis) ≡ axis
    extensionReference : String

open OpenAxisExtension public

-- A gap must be visible AS an unmeasured component/axis in this same world.
-- A comparison through common principle names cannot manufacture it.
record ResearchGapRoute
    (scope : World.StudyWorldScope)
    (world : World.AccountedStudyWorld scope)
    (donor recipient : World.StudyPart scope)
    (axis : World.Axis scope) : Set₁ where
  constructor research-gap-route
  field
    researchQuestion : String
    missingRecipientEvidence : String
    recipientReallyUnmeasured :
      World.accounting world
        (World.study recipient) (World.part recipient) axis ≡
      World.unmeasuredForQuestion
        researchQuestion missingRecipientEvidence

    donorAssessment :
      World.PartAxisAccounting scope
        (World.study donor) (World.part donor) axis
    donorAssessmentIsWorld :
      donorAssessment ≡ World.accounting world
        (World.study donor) (World.part donor) axis

    proposedUse : CrossStudyResearchUse
    provenanceReference : String
    populationAndContextTransferDebt : String
    participantAuthorityDebt : String

open ResearchGapRoute public

-- The routing output remains a research question, not a reviewed finding.
-- Materialising a donor's observation in the recipient study would need an
-- actual new source-specific observation, not a projection or relabelling.
data CrossStudyGapCreatesRecipientObservation : Set where
data SharedAxisCreatesSameStudyPopulation : Set where
data SourceSimilarityPaysParticipantAuthority : Set where

crossStudyGapDoesNotCreateObservation :
  CrossStudyGapCreatesRecipientObservation → ⊥
crossStudyGapDoesNotCreateObservation ()

sharedAxisDoesNotCreateSamePopulation :
  SharedAxisCreatesSameStudyPopulation → ⊥
sharedAxisDoesNotCreateSamePopulation ()

similarityDoesNotPayParticipantAuthority :
  SourceSimilarityPaysParticipantAuthority → ⊥
similarityDoesNotPayParticipantAuthority ()

-- CORPUS/PNF bridge: a real ERIC execution and a parsed retained-study
-- packet are NOT a reviewed observation. The existing 19 coordinates are
-- parser projection coordinates, not the global set of research axes.
record ParsedStudyPartCandidate
    (scope : World.StudyWorldScope)
    (s : World.Study scope)
    (p : World.Part scope s)
    (a : World.Axis scope) : Set where
  constructor parsed-study-part-candidate
  field
    packet : Parse.ParsedRetainedStudyPacket
    sourceIdentityIsExact :
      Parse.GenericSLRParseReceipt.sourceIdentityReference
        (Parse.ParsedRetainedStudyPacket.parseReceipt packet)
      ≡ Attr.canonicalURL (World.studySource scope s)
    partMappingQuestion : String
    axisMappingQuestion : String
    parserProjectionIsNotFullAxisAccount : String

open ParsedStudyPartCandidate public

ericMetadataUniverseExact :
  ERIC.expectedUniqueERICRecordCount ≡ Census.expectedERICMetadataCount
ericMetadataUniverseExact = refl

-- The above equality is only the matching declared metadata denominator.
-- It is NOT a proof of executed full-text screening, 19 extraction
-- coordinates paid, unique study admission or a populated research world.
data MetadataCountImpliesCompleteStudyPartWorld : Set where
data PNFParsingImpliesReviewedAxisEvidence : Set where
data NineteenCoordinatesExhaustEveryFutureAxis : Set where

metadataDoesNotCreateWorld :
  MetadataCountImpliesCompleteStudyPartWorld → ⊥
metadataDoesNotCreateWorld ()

pnfCandidateDoesNotCreateReview :
  PNFParsingImpliesReviewedAxisEvidence → ⊥
pnfCandidateDoesNotCreateReview ()

parserProjectionDoesNotCloseAxisSpace :
  NineteenCoordinatesExhaustEveryFutureAxis → ⊥
parserProjectionDoesNotCloseAxisSpace ()
