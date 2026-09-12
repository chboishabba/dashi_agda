module DASHI.Wikimedia.IbrahimMonster3BActualVOASelected3BCompositionExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOABridgeExact as Legacy
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as LiteralWeld
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as Phase
import DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact as Acquisition
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta

------------------------------------------------------------------------
-- ACTUAL LITERAL VOA -> SELECTED 3B SAME-OBJECT COMPOSITION
--
-- `ActualLinearMultiplicityAcquisition` already requires the exact literal
-- character/action weld, its source-backed linearity receipt, grade-two linear
-- realisation, the 196883 linear constituent, and the selected-3B linear zeta
-- producer.  Separately, `Base369Monster3BVOAActionPhaseAdapterBidiExact`
-- compiles an `ActualMonster3BVOARecognizedActionSource` into the existing
-- `ActualMonster3BSingleActionProducer` on the literal VOA carrier.
--
-- The highest-alpha identity payment is therefore not a new action model.  It
-- is to require those two existing routes to be the SAME route:
--
--   * the recognized 3B source uses the exact MoonshineVOABridge already
--     carried by the literal character/action weld; and
--   * the producer compiled from that recognized source is exactly the
--     producer carried by the acquisition's linear-zeta owner.
--
-- This owner pays only same-object composition.  It does not manufacture the
-- recognized source, action linearity, a normalizer embedding, matrices, or a
-- 12+78 intertwiner.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Attribution / source roles.
------------------------------------------------------------------------

barracloughWilson : Attribution.AttributedSource
barracloughWilson = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary representation-theoretic source for the 3B normalizer and inertia-character route; not authority for a repository same-object equality"
  Attribution.publicAttribution

borcherds : Attribution.AttributedSource
borcherds = Attribution.mkDOISource
  "Richard E. Borcherds"
  "Monstrous moonshine and monstrous Lie superalgebras"
  "Inventiones Mathematicae 109, 405-444"
  "1992"
  "10.1007/BF01232032"
  "https://doi.org/10.1007/BF01232032"
  Attribution.academicArticleSource
  "primary moonshine/VOA representation context; not authority for the repository's selected-3B same-object compiler equality"
  Attribution.publicAttribution

barracloughWilsonAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
borcherdsAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt borcherds

------------------------------------------------------------------------
-- 2. Typed same-object composition.
------------------------------------------------------------------------

record ActualVOASelected3BComposition
    {Monster K : Set}
    (acquisition :
      Acquisition.ActualLinearMultiplicityAcquisition {Monster} {K}) : Setω where
  field
    recognizedActionSource :
      Phase.ActualMonster3BVOARecognizedActionSource
        Monster K
        (GVOA.group
          (Legacy.voaAction
            (LiteralWeld.gradedAuthority
              (Acquisition.literalSameObjectWeld acquisition))))

    recognizedBridgeIsLiteralSameObjectBridge :
      Phase.bridge (Phase.phaseSource recognizedActionSource)
      ≡ LiteralWeld.literalVOA
          (Acquisition.literalSameObjectWeld acquisition)

    compiledSingleActionProducerIsAcquisitionProducer :
      Phase.singleActionProducerFromVOA recognizedActionSource
      ≡ LinearZeta.singleActionProducer
          (Acquisition.linearZetaProducer acquisition)

open ActualVOASelected3BComposition public

------------------------------------------------------------------------
-- 3. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data RecognizedSourceCreatesLinearity : Set where
data BridgeEqualityCreatesActionIntertwiner : Set where
data ProducerEqualityCreatesNormalizerEmbedding : Set where
data CharacterAuthorityCreatesRecognizedSource : Set where
data QidCreatesComposition : Set where
data DeweyCreatesComposition : Set where
data OeisCreatesComposition : Set where

recognizedSourceDoesNotCreateLinearity :
  RecognizedSourceCreatesLinearity → ⊥
recognizedSourceDoesNotCreateLinearity ()

bridgeEqualityDoesNotCreateActionIntertwiner :
  BridgeEqualityCreatesActionIntertwiner → ⊥
bridgeEqualityDoesNotCreateActionIntertwiner ()

producerEqualityDoesNotCreateNormalizerEmbedding :
  ProducerEqualityCreatesNormalizerEmbedding → ⊥
producerEqualityDoesNotCreateNormalizerEmbedding ()

characterAuthorityDoesNotCreateRecognizedSource :
  CharacterAuthorityCreatesRecognizedSource → ⊥
characterAuthorityDoesNotCreateRecognizedSource ()

qidDoesNotCreateComposition : QidCreatesComposition → ⊥
qidDoesNotCreateComposition ()

deweyDoesNotCreateComposition : DeweyCreatesComposition → ⊥
deweyDoesNotCreateComposition ()

oeisDoesNotCreateComposition : OeisCreatesComposition → ⊥
oeisDoesNotCreateComposition ()

------------------------------------------------------------------------
-- 4. DOI / QID / Dewey / OEIS remain descriptive coordinates only.
------------------------------------------------------------------------

record ActualVOASelected3BExternalCoordinates : Set where
  constructor actual-voa-selected3b-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasCompositionAuthority : Bool
open ActualVOASelected3BExternalCoordinates public

canonicalActualVOASelected3BExternalCoordinates :
  ActualVOASelected3BExternalCoordinates
canonicalActualVOASelected3BExternalCoordinates =
  actual-voa-selected3b-external-coordinates
    "Q1055807"
    "Q600043"
    "Q1057968"
    "512.22"
    "512.23"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no same-object, selected-3B, action, matrix, or intertwiner authority"
    false

------------------------------------------------------------------------
-- 5. Pareto frontier.
------------------------------------------------------------------------

record ActualVOASelected3BCompositionFrontier : Set where
  constructor actual-voa-selected3b-composition-frontier
  field
    literalCharacterActionWeldAlreadyOwned : Bool
    recognizedVOA3BCompilerAlreadyOwned : Bool
    selected3BLinearProducerAlreadyNamed : Bool
    sameLiteralVOABridgeEqualityRequired : Bool
    sameCompiledSingleActionProducerEqualityRequired : Bool
    recognizedSourceInhabitedHere : Bool
    normalizerMonsterActionWeldPaidHere : Bool
    twelveSeventyEightIntertwinerPaidHere : Bool
    nextResidual : String
open ActualVOASelected3BCompositionFrontier public

currentActualVOASelected3BCompositionFrontier :
  ActualVOASelected3BCompositionFrontier
currentActualVOASelected3BCompositionFrontier =
  actual-voa-selected3b-composition-frontier
    true true true true true
    false false false
    "find or construct an ActualMonster3BVOARecognizedActionSource on the exact literal MoonshineVOABridge already carried by literalSameObjectWeld. Its recognition must be the existing ActualZetaSectorRecognition on the literal VOA zeta eigenspace, and singleActionProducerFromVOA must equal the producer carried by linearZetaProducer. After that identity payment, attack the existing Selected3BNormalizerMonsterActionWeld: supply the normalizer-to-Monster embedding and prove its action intertwines with the transported 196883 constituent action. DOI/QID/Dewey/OEIS and character values cannot create either receipt."
