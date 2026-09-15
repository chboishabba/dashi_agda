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
-- At the pinned mathlib v4.28.0 execution dependency we already have:
--
--   * finite-group Maschke semisimplicity for k[G]-modules;
--   * isotypicComponent / isotypicComponents;
--   * exhaustion of a semisimple module by its isotypic components;
--   * IsIsotypicOfType.linearEquiv_fun for finite isotypic modules;
--   * character inner product = equivariant-Hom finrank;
--   * irreducible character orthogonality.
--
-- Therefore a stronger generic producer may work directly from the whole
-- character identity
--
--     chi(W_zeta|E) = 90 chi(H_zeta)
--
-- by proving all non-H_zeta simple types have zero Hom multiplicity and the
-- H_zeta type has multiplicity 90, then using semisimplicity/isotypic
-- exhaustion to construct the whole equivariant isomorphism.  If that producer
-- is obtained, the explicit constituent-list attachment becomes an optional
-- witness route rather than a mandatory theorem dependency.
--
-- This owner DOES NOT assert that the Lean producer is already written or
-- kernel-checked, and it DOES NOT turn a whole equivariant isomorphism into the
-- concrete X6 x Fin 90 basis/action recognition automatically.  The latter
-- still needs a same-object action/basis weld.
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

characterAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibCharacterSource
maschkeAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibMaschkeSource
isotypicAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibIsotypicSource

------------------------------------------------------------------------
-- Stronger generic producer contract.
--
-- This is deliberately representation-level.  It is stronger than the
-- already-written irreducible equal-character theorem because V itself need
-- not be simple.  Its intended proof route is semisimple/isotypic assembly.
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

------------------------------------------------------------------------
-- The two routes are alternatives after the same actual-kernel replay:
--
--   A. literal constituent attachment -> classify each constituent;
--   B. whole-character semisimple/isotypic producer -> whole representation.
--
-- Route B can bypass the literal list, but neither route creates the concrete
-- Base369/X6 basis chart or Weyl-operator intertwiners by itself.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Existing state anchors.
------------------------------------------------------------------------

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

    wholeCharacterBypassCompilerSpecified : Bool
    literalConstituentListMandatoryAfterBypassProducer : Bool

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
  true false
  false false false false false
  false false false
  "attempt the smallest Lean theorem on the pinned v4.28.0 APIs: for a finite-group FDRep V and simple H, if char(V)=90*char(H), derive that V is the H-isotypic semisimple representation with multiplicity 90 and obtain an equivariant isomorphism to 90 copies of H. Keep the current literal-constituent attachment route as fallback. Even after that theorem is kernel-paid, separately weld the resulting whole equivariant isomorphism to the SAME selected Monster W_zeta carrier and then to the concrete X6 x Fin 90 / Base369 basis with translation and modulation intertwiners. A005052(2)=90 and 65610=729*90 remain numerical coordinates only."
