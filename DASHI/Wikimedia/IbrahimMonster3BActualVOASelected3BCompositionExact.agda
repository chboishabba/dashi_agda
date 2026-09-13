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
import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as Selected
import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as KernelSame
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as Phase
import DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact as Acquisition
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta

------------------------------------------------------------------------
-- ACTUAL LITERAL VOA -> CERTIFIED 3B -> SELECTED PRODUCER COMPOSITION
--
-- The repo already owns two stronger same-object donors than a fresh adapter:
--
--   * MonsterGradedVOASelected3BSameElementBidiExact forces the phase source
--     onto the literal MoonshineVOABridge welded to exact graded-trace
--     authority and carries ActualZetaSectorRecognition on that literal sector;
--
--   * MonsterGradedVOAActual3BKernelSameElementBidiExact additionally attaches
--     that selected literal element to the independently certified central-zeta
--     kernel class fusing to Monster 3B, while preserving the 65610 / ninety
--     Heisenberg character consequences as character-level facts only.
--
-- This owner therefore consumes the stronger
-- `Actual3BKernelRecognizedSameElementAttachment` and pays only the remaining
-- cross-owner identities needed by the linear multiplicity lane:
--
--   * its literal weld is exactly the acquisition literalSameObjectWeld;
--   * compiling its recognized literal phase source gives exactly the
--     single-action producer carried by linearZetaProducer.
--
-- No matrix/action/intertwiner is manufactured by the class attachment,
-- recognition, character values, or identifiers.
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
-- 2. Reuse existing recognized same-element packages.
------------------------------------------------------------------------

selectedRecognizedFromKernel :
  ∀ {Monster K}
    (source : KernelSame.Actual3BKernelRecognizedSameElementAttachment Monster K) →
  Selected.Selected3BRecognizedSameElementSource Monster K
selectedRecognizedFromKernel source = record
  { selectedSource =
      KernelSame.selectedSource (KernelSame.attachment source)
  ; recognition = KernelSame.recognition source
  }

recognizedActionSourceFromSameElement :
  ∀ {Monster K}
    (source : Selected.Selected3BRecognizedSameElementSource Monster K) →
  Phase.ActualMonster3BVOARecognizedActionSource
    Monster K
    (GVOA.group
      (Legacy.voaAction
        (LiteralWeld.gradedAuthority
          (Selected.weld (Selected.selectedSource source)))))
recognizedActionSourceFromSameElement source = record
  { phaseSource = Selected.phaseSource (Selected.selectedSource source)
  ; recognition = Selected.recognition source
  }

------------------------------------------------------------------------
-- 3. Typed composition into the actual linear-multiplicity acquisition.
------------------------------------------------------------------------

record ActualVOASelected3BComposition
    {Monster K : Set}
    (acquisition :
      Acquisition.ActualLinearMultiplicityAcquisition {Monster} {K}) : Setω where
  field
    kernelRecognizedSameElementAttachment :
      KernelSame.Actual3BKernelRecognizedSameElementAttachment Monster K

    kernelSelectedWeldIsAcquisitionWeld :
      Selected.weld
        (KernelSame.selectedSource
          (KernelSame.attachment kernelRecognizedSameElementAttachment))
      ≡ Acquisition.literalSameObjectWeld acquisition

    compiledSingleActionProducerIsAcquisitionProducer :
      Phase.singleActionProducerFromVOA
        (recognizedActionSourceFromSameElement
          (selectedRecognizedFromKernel kernelRecognizedSameElementAttachment))
      ≡ LinearZeta.singleActionProducer
          (Acquisition.linearZetaProducer acquisition)

open ActualVOASelected3BComposition public

------------------------------------------------------------------------
-- 4. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data RecognizedSourceCreatesLinearity : Set where
data BridgeEqualityCreatesActionIntertwiner : Set where
data ProducerEqualityCreatesNormalizerEmbedding : Set where
data KernelClassAttachmentCreatesRecognition : Set where
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

kernelClassAttachmentDoesNotCreateRecognition :
  KernelClassAttachmentCreatesRecognition → ⊥
kernelClassAttachmentDoesNotCreateRecognition ()

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
-- 5. DOI / QID / Dewey / OEIS remain descriptive coordinates only.
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
-- 6. Pareto frontier.
------------------------------------------------------------------------

record ActualVOASelected3BCompositionFrontier : Set where
  constructor actual-voa-selected3b-composition-frontier
  field
    literalCharacterActionWeldAlreadyOwned : Bool
    selectedSameElementBridgeWeldAlreadyOwned : Bool
    certified3BKernelSameElementAttachmentTyped : Bool
    recognizedZetaSectorPackageAlreadyTyped : Bool
    centralZetaAmplitude65610Available : Bool
    ninetyHeisenbergCharacterIsotypyAvailable : Bool
    selected3BLinearProducerAlreadyNamed : Bool
    kernelSelectedWeldAcquisitionEqualityRequired : Bool
    sameCompiledSingleActionProducerEqualityRequired : Bool
    kernelRecognizedAttachmentInhabitedHere : Bool
    normalizerMonsterActionWeldPaidHere : Bool
    twelveSeventyEightIntertwinerPaidHere : Bool
    nextResidual : String
open ActualVOASelected3BCompositionFrontier public

currentActualVOASelected3BCompositionFrontier :
  ActualVOASelected3BCompositionFrontier
currentActualVOASelected3BCompositionFrontier =
  actual-voa-selected3b-composition-frontier
    true true true true true true true true true
    false false false
    "locate or construct an Actual3BKernelRecognizedSameElementAttachment on the exact literal selected source already used by the acquisition. This single object must combine the certified central-zeta/Monster-3B kernel attachment with ActualZetaSectorRecognition; neither kernel class nor the 65610/ninety character consequences construct recognition. Then prove its weld equals literalSameObjectWeld and its compiled singleActionProducerFromVOA equals the producer inside linearZetaProducer. After those identities, the next theorem-bearing leaf is Selected3BNormalizerMonsterActionWeld: supply normalizerToMonster and prove the transported 196883 Monster action equals the selected normalizer action. DOI/QID/Dewey/OEIS cannot create any of these receipts."
