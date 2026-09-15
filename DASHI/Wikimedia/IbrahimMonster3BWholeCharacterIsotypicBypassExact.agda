module DASHI.Wikimedia.IbrahimMonster3BWholeCharacterIsotypicBypassExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact as Kernel
import DASHI.Wikimedia.IbrahimMonster3BReplayStatusMultiplicitySplitSnowballExact as Replay
import DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentSnowballExact as Constituent
import DASHI.Wikimedia.IbrahimMonsterCharacterDeterminationMathlibProducerSnowballExact as Character

------------------------------------------------------------------------
-- WHOLE-CHARACTER SEMISIMPLE BYPASS
--
-- The previous frontier treated a literal irreducible constituent list for
-- W_zeta|E as mandatory before Stone--von Neumann classification.  That is a
-- sufficient route, but not obviously the shortest generic route.
--
-- At pinned mathlib v4.28.0 the needed ingredients exist, but source inspection
-- exposes a real interface seam: character equalities live on bundled FDRep,
-- while the strongest isotypic APIs are phrased for modules over the group
-- algebra.  Mathlib exposes semantic bridges between these views, but no
-- repo-local theorem has yet been located that directly converts the whole
-- FDRep character identity into the required isotypic-module witness.
--
-- Therefore the whole-character route remains a high-value probe, not a paid
-- shortcut.  The literal constituent route stays available as fallback.
------------------------------------------------------------------------

mathlibCharacterSource : Attribution.AttributedSource
mathlibCharacterSource = Attribution.mkNoDOISource
  "Antoine Labelle; mathlib contributors"
  "Mathlib.RepresentationTheory.Character"
  "mathlib4 source repository"
  "RequestProject pin v4.28.0"
  "https://github.com/leanprover-community/mathlib4/blob/v4.28.0/Mathlib/RepresentationTheory/Character.lean"
  (Attribution.namedSourceKind "machine-checked theorem-library source")
  "external producer for character inner products and irreducible orthogonality; citation does not construct the Monster representation"
  Attribution.publicAttribution

mathlibMaschkeSource : Attribution.AttributedSource
mathlibMaschkeSource = Attribution.mkNoDOISource
  "Kim Morrison; mathlib contributors"
  "Mathlib.RepresentationTheory.Maschke"
  "mathlib4 source repository"
  "RequestProject pin v4.28.0"
  "https://github.com/leanprover-community/mathlib4/blob/v4.28.0/Mathlib/RepresentationTheory/Maschke.lean"
  (Attribution.namedSourceKind "machine-checked theorem-library source")
  "external producer for finite-group semisimplicity under the nonmodular field hypothesis; no Monster-specific conclusion imported"
  Attribution.publicAttribution

mathlibIsotypicSource : Attribution.AttributedSource
mathlibIsotypicSource = Attribution.mkNoDOISource
  "Junyan Xu; mathlib contributors"
  "Mathlib.RingTheory.SimpleModule.Isotypic"
  "mathlib4 source repository"
  "RequestProject pin v4.28.0"
  "https://github.com/leanprover-community/mathlib4/blob/v4.28.0/Mathlib/RingTheory/SimpleModule/Isotypic.lean"
  (Attribution.namedSourceKind "machine-checked theorem-library source")
  "external producer for isotypic components, semisimple exhaustion and finite isotypic linear equivalences; no Monster-specific conclusion imported"
  Attribution.publicAttribution

mathlibFDRepSource : Attribution.AttributedSource
mathlibFDRepSource = Attribution.mkNoDOISource
  "Kim Morrison; mathlib contributors"
  "Mathlib.RepresentationTheory.FDRep / Semisimple"
  "mathlib4 source repository"
  "RequestProject pin v4.28.0"
  "https://github.com/leanprover-community/mathlib4/blob/v4.28.0/Mathlib/RepresentationTheory/FDRep.lean"
  (Attribution.namedSourceKind "machine-checked theorem-library source")
  "owns the bundled finite-dimensional representation carrier and semantic representation/module bridges; does not itself prove the desired whole-character isotypic theorem"
  Attribution.publicAttribution

characterAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibCharacterSource
maschkeAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibMaschkeSource
isotypicAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibIsotypicSource
fdrepAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibFDRepSource

------------------------------------------------------------------------
-- Stronger generic producer contract.
------------------------------------------------------------------------

record WholeCharacterIsotypicProducer : Set₁ where
  field
    GroupCarrier : Set
    FieldCarrier : Set
    ActualRestrictedSector : Set
    CanonicalHeisenberg : Set

    finiteGroup : Set
    algebraicallyClosedField : Set
    groupOrderInvertible : Set
    actualSectorFiniteDimensional : Set
    canonicalHeisenbergSimple : Set
    maschkeSemisimpleActualSector : Set

    wholeCharacterIsNinetyHeisenbergCharacters : Set
    everyOtherSimpleTypeHasZeroHomMultiplicity : Set
    heisenbergHomMultiplicityIsNinety : Set
    actualSectorIsIsotypicOfHeisenbergType : Set
    finiteIsotypicMultiplicityIsNinety : Set

    wholeEquivariantIsoToNinetyHeisenbergCopies : Set

open WholeCharacterIsotypicProducer public

record RecognitionRoutePareto : Set where
  constructor recognition-route-pareto
  field
    literalConstituentRouteAvailable : Bool
    wholeCharacterIsotypicRouteSpecified : Bool
    bothDependOnActualKernelReplay : Bool
    wholeCharacterRouteCanBypassLiteralConstituentEnumeration : Bool
    wholeCharacterRouteCreatesConcreteBase369Chart : Bool
    wholeCharacterRouteCreatesWeylIntertwiners : Bool
open RecognitionRoutePareto public

canonicalRecognitionRoutePareto : RecognitionRoutePareto
canonicalRecognitionRoutePareto = recognition-route-pareto
  true true true true false false

kernelStatus : Kernel.ActualKernelPromotionStatus
kernelStatus = Kernel.canonicalActualKernelPromotionStatus

replayFrontier : Replay.ReplayMultiplicityFrontier
replayFrontier = Replay.currentReplayMultiplicityFrontier

constituentFrontier : Constituent.ConstituentAttachmentFrontier
constituentFrontier = Constituent.currentConstituentAttachmentFrontier

characterProducerFrontier : Character.MathlibCharacterDeterminationSnowballFrontier
characterProducerFrontier = Character.currentMathlibCharacterDeterminationSnowballFrontier

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data CharacterEqualityAloneCreatesWholeRepresentationIso : Set where
data DimensionEqualityCreatesWholeRepresentationIso : Set where
data OEISCreatesWholeRepresentationIso : Set where
data WholeRepresentationIsoCreatesConcreteActionRecognition : Set where
data IsotypicAPICitationCreatesProducerWitness : Set where
data SemanticBridgeCreatesWholeCharacterTheorem : Set where

characterEqualityAloneDoesNotCreateWholeIso :
  CharacterEqualityAloneCreatesWholeRepresentationIso → ⊥
characterEqualityAloneDoesNotCreateWholeIso ()

dimensionEqualityDoesNotCreateWholeIso :
  DimensionEqualityCreatesWholeRepresentationIso → ⊥
dimensionEqualityDoesNotCreateWholeIso ()

oeisDoesNotCreateWholeIso : OEISCreatesWholeRepresentationIso → ⊥
oeisDoesNotCreateWholeIso ()

wholeIsoDoesNotCreateConcreteActionRecognition :
  WholeRepresentationIsoCreatesConcreteActionRecognition → ⊥
wholeIsoDoesNotCreateConcreteActionRecognition ()

isotypicCitationDoesNotCreateProducerWitness :
  IsotypicAPICitationCreatesProducerWitness → ⊥
isotypicCitationDoesNotCreateProducerWitness ()

semanticBridgeDoesNotCreateWholeCharacterTheorem :
  SemanticBridgeCreatesWholeCharacterTheorem → ⊥
semanticBridgeDoesNotCreateWholeCharacterTheorem ()

------------------------------------------------------------------------
-- Current boundary.
------------------------------------------------------------------------

record WholeCharacterIsotypicBypassBoundary : Set where
  constructor whole-character-isotypic-bypass-boundary
  field
    characterInnerProductAPILocated : Bool
    irreducibleOrthogonalityAPILocated : Bool
    maschkeSemisimplicityAPILocated : Bool
    isotypicComponentAPILocated : Bool
    isotypicExhaustionAPILocated : Bool
    isotypicFiniteMultiplicityAPILocated : Bool

    fdrepCharacterAPIIsBundledRepresentationLevel : Bool
    isotypicAPIIsGroupAlgebraModuleLevel : Bool
    fdrepToGroupAlgebraSemanticBridgeLocated : Bool
    directWholeCharacterToIsotypicBridgeLocated : Bool

    wholeCharacterBypassCompilerSpecified : Bool
    literalConstituentListMandatoryAfterBypassProducer : Bool
    literalConstituentRouteRetainedAsFallback : Bool

    wholeCharacterBypassLeanSourceWritten : Bool
    wholeCharacterBypassKernelReceiptObserved : Bool
    crossProverTransportObserved : Bool
    actualKernelReplayReceiptObserved : Bool
    actualMonsterSameObjectActionRecognitionPaid : Bool

    oeisCreatesWholeRepresentationIso : Bool
    dimensionEqualityCreatesWholeRepresentationIso : Bool
    characterEqualityAloneCreatesActionRecognition : Bool

    nextResidual : String
open WholeCharacterIsotypicBypassBoundary public

canonicalWholeCharacterIsotypicBypassBoundary : WholeCharacterIsotypicBypassBoundary
canonicalWholeCharacterIsotypicBypassBoundary = whole-character-isotypic-bypass-boundary
  true true true true true true
  true true true false
  true false true
  false false false false false
  false false false
  "the whole-character probe has localized a concrete Lean interface seam: FDRep owns the character statement, while the strongest finite isotypic decomposition APIs are group-algebra module theorems. First try one small adapter theorem transporting the FDRep object to the semisimple group-algebra module view and back. If that adapter remains awkward, immediately use the retained literal-constituent route rather than inventing another representation ontology. In either route, same-object Monster action recognition and the X6 x Fin90/Base369 operator weld remain downstream. A005052(2)=90 and 65610=729*90 remain numerical coordinates only."
