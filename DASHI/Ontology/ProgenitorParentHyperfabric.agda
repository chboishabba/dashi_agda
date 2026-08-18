module DASHI.Ontology.ProgenitorParentHyperfabric where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Progenitor/parent hyperfabric.
--
-- The carrier is generative provenance. Progeniture, parenthood, genetic
-- contribution, gestation, intended/legal/social parenthood, and disclosure are
-- independent projections. No projection is promoted to the whole carrier.
--
-- Source anchors for non-binary genetic provenance:
-- Masahito Tachibana, Paula Amato, Michelle Sparman, et al.,
-- "Towards germline gene therapy of inherited mitochondrial diseases",
-- Nature 493, 627-631 (2013), DOI 10.1038/nature11647.
--
-- Yanbo Mao, Alexander Gabel, Thomas Nakel, Prisca Viehover, Thomas Baum,
-- Dawit Girma Tekleyohans, Dieu Vo, Ivo Grosse, Rita Gross-Hardt,
-- "Selective egg cell polyspermy bypasses the triploid block",
-- eLife 9:e52976 (2020), DOI 10.7554/eLife.52976.
------------------------------------------------------------------------

infixr 4 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B
open _×_ public

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

record PaperReference : Set where
  constructor paperReference
  field
    paperTitle : String
    paperAuthors : String
    paperVenue : String
    paperYear : Nat
    paperDOI : String
open PaperReference public

mitochondrialReplacementReference : PaperReference
mitochondrialReplacementReference =
  paperReference
    "Towards germline gene therapy of inherited mitochondrial diseases"
    "Masahito Tachibana; Paula Amato; Michelle Sparman; et al."
    "Nature 493, 627-631"
    2013
    "10.1038/nature11647"

polyspermyReference : PaperReference
polyspermyReference =
  paperReference
    "Selective egg cell polyspermy bypasses the triploid block"
    "Yanbo Mao; Alexander Gabel; Thomas Nakel; Prisca Viehover; Thomas Baum; Dawit Girma Tekleyohans; Dieu Vo; Ivo Grosse; Rita Gross-Hardt"
    "eLife 9:e52976"
    2020
    "10.7554/eLife.52976"

mitochondrialReplacementDOIExact :
  paperDOI mitochondrialReplacementReference ≡ "10.1038/nature11647"
mitochondrialReplacementDOIExact = refl

polyspermyDOIExact :
  paperDOI polyspermyReference ≡ "10.7554/eLife.52976"
polyspermyDOIExact = refl

------------------------------------------------------------------------
-- Generative carrier.
------------------------------------------------------------------------

data NodeLevel : Set where
  individualLevel lineageLevel : NodeLevel

data ProgenitorMode : Set where
  genericLineage gametic nuclear mitochondrial : ProgenitorMode

data ReproductiveProfile : Set where
  unrestrictedProfile ordinaryBiparentalNuclearProfile : ReproductiveProfile

record ProgenitorContribution : Set where
  constructor progenitorContribution
  field
    progenitorEntity : String
    progenitorMode : ProgenitorMode
open ProgenitorContribution public

record CausalInput : Set where
  constructor causalInput
  field
    inputEntity : String
    participatesCausally : Bool
    lineageBearing : Bool
open CausalInput public

incubatorInput : CausalInput
incubatorInput = causalInput "incubator" true false

causalInputDoesNotImplyProgenitor :
  participatesCausally incubatorInput ≡ true
  × lineageBearing incubatorInput ≡ false
causalInputDoesNotImplyProgenitor = refl , refl

record GenerationEvent : Set where
  constructor generationEvent
  field
    generatedEntity : String
    generatedLevel : NodeLevel
    progenitors : List ProgenitorContribution
    reproductiveProfile : ReproductiveProfile
open GenerationEvent public

progenitorCount : GenerationEvent → Nat
progenitorCount event = listCount (progenitors event)

triparentalPlantGeneration : GenerationEvent
triparentalPlantGeneration =
  generationEvent
    "triparental Arabidopsis plant"
    individualLevel
    ( progenitorContribution "maternal plant" gametic
    ∷ progenitorContribution "paternal plant A" gametic
    ∷ progenitorContribution "paternal plant B" gametic
    ∷ [] )
    unrestrictedProfile

triparentalPlantHasThreeContributors :
  progenitorCount triparentalPlantGeneration ≡ suc (suc (suc zero))
triparentalPlantHasThreeContributors = refl

record BiparentalNuclearWitness (event : GenerationEvent) : Set where
  constructor biparentalNuclearWitness
  field
    profileExact : reproductiveProfile event ≡ ordinaryBiparentalNuclearProfile
    contributorCountExact : progenitorCount event ≡ suc (suc zero)
open BiparentalNuclearWitness public

binaryBoundRequiresBiparentalProfile :
  (event : GenerationEvent) →
  BiparentalNuclearWitness event →
  progenitorCount event ≡ suc (suc zero)
binaryBoundRequiresBiparentalProfile event witness = contributorCountExact witness

------------------------------------------------------------------------
-- Orthogonal relationship fibres.
------------------------------------------------------------------------

record RelationVector : Set where
  constructor relationVector
  field
    progenitorRelation : Bool
    geneticContributor : Bool
    gameteContributor : Bool
    mitochondrialContributor : Bool
    gestationalContributor : Bool
    genealogicalParent : Bool
    intendedParent : Bool
    legalParent : Bool
    socialParent : Bool
    caregiver : Bool
    identityKnown : Bool
    identityDisclosable : Bool
open RelationVector public

anonymousIVFDonor : RelationVector
anonymousIVFDonor =
  relationVector true true true false false false false false false false false false

singleMother : RelationVector
singleMother =
  relationVector true true true false true true true true true true true true

adoptiveParent : RelationVector
adoptiveParent =
  relationVector false false false false false true true true true true true true

mitochondrialDonor : RelationVector
mitochondrialDonor =
  relationVector true true false true false false false false false false true true

gestationalSurrogateOnly : RelationVector
gestationalSurrogateOnly =
  relationVector false false false false true false false false false false true true

geneticContributionCannotDetermineParenthood :
  geneticContributor anonymousIVFDonor ≡ true
  × genealogicalParent anonymousIVFDonor ≡ false
geneticContributionCannotDetermineParenthood = refl , refl

parenthoodCannotDetermineGeneticContribution :
  genealogicalParent adoptiveParent ≡ true
  × geneticContributor adoptiveParent ≡ false
parenthoodCannotDetermineGeneticContribution = refl , refl

gestationCannotDetermineParenthood :
  gestationalContributor gestationalSurrogateOnly ≡ true
  × genealogicalParent gestationalSurrogateOnly ≡ false
gestationCannotDetermineParenthood = refl , refl

mitochondrialContributionCannotDetermineParenthood :
  mitochondrialContributor mitochondrialDonor ≡ true
  × genealogicalParent mitochondrialDonor ≡ false
mitochondrialContributionCannotDetermineParenthood = refl , refl

anonymousContributionDoesNotRevealIdentity :
  geneticContributor anonymousIVFDonor ≡ true
  × identityKnown anonymousIVFDonor ≡ false
anonymousContributionDoesNotRevealIdentity = refl , refl

identityKnowledgeAndDisclosureAreIndependentCoordinates :
  identityKnown anonymousIVFDonor ≡ false
  × identityDisclosable anonymousIVFDonor ≡ false
identityKnowledgeAndDisclosureAreIndependentCoordinates = refl , refl

------------------------------------------------------------------------
-- Wikidata slots are representation projections, not carrier semantics.
------------------------------------------------------------------------

data WikidataParentSlot : Set where
  fatherP22 motherP25 parentP8810 hybridOfP1531 : WikidataParentSlot

data EntitySurfaceType : Set where
  humanSurface animalSurface cultivarSurface cellSurface deitySurface otherSurface : EntitySurfaceType

record WikidataParentProjection : Set where
  constructor wikidataParentProjection
  field
    surfaceType : EntitySurfaceType
    nodeLevel : NodeLevel
    slot : WikidataParentSlot
    relation : RelationVector
open WikidataParentProjection public

recommendedGenericSlot : NodeLevel → WikidataParentSlot
recommendedGenericSlot individualLevel = parentP8810
recommendedGenericSlot lineageLevel = hybridOfP1531

cultivarLineageProjection : WikidataParentProjection
cultivarLineageProjection =
  wikidataParentProjection cultivarSurface lineageLevel hybridOfP1531
    (relationVector true false false false false false false false false false true true)

fictionalSentientCellParent : WikidataParentProjection
fictionalSentientCellParent =
  wikidataParentProjection cellSurface individualLevel parentP8810
    (relationVector true false false false false true true false true true true true)

ordinaryNonParentCell : WikidataParentProjection
ordinaryNonParentCell =
  wikidataParentProjection cellSurface individualLevel parentP8810
    (relationVector false false false false false false false false false false true true)

anonymousDonorP8810Surface : WikidataParentProjection
anonymousDonorP8810Surface =
  wikidataParentProjection humanSurface individualLevel parentP8810 anonymousIVFDonor

adoptiveP8810Surface : WikidataParentProjection
adoptiveP8810Surface =
  wikidataParentProjection humanSurface individualLevel parentP8810 adoptiveParent

cultivarConflictIsRepresentationRestriction :
  recommendedGenericSlot lineageLevel ≡ hybridOfP1531
cultivarConflictIsRepresentationRestriction = refl

individualGenericParentProjectsToP8810 :
  recommendedGenericSlot individualLevel ≡ parentP8810
individualGenericParentProjectsToP8810 = refl

entityTypeDoesNotDetermineParentEligibility :
  surfaceType fictionalSentientCellParent ≡ surfaceType ordinaryNonParentCell
  × genealogicalParent (relation fictionalSentientCellParent) ≡ true
  × genealogicalParent (relation ordinaryNonParentCell) ≡ false
entityTypeDoesNotDetermineParentEligibility = refl , (refl , refl)

wikidataParentSlotDoesNotDetermineParentSemantics :
  slot anonymousDonorP8810Surface ≡ slot adoptiveP8810Surface
  × geneticContributor (relation anonymousDonorP8810Surface) ≡ true
  × geneticContributor (relation adoptiveP8810Surface) ≡ false
wikidataParentSlotDoesNotDetermineParentSemantics = refl , (refl , refl)

p1531AndP8810ShareProgenitorCarrier :
  progenitorRelation (relation cultivarLineageProjection) ≡ true
  × progenitorRelation (relation fictionalSentientCellParent) ≡ true
p1531AndP8810ShareProgenitorCarrier = refl , refl

------------------------------------------------------------------------
-- Ethical/epistemic boundary.
------------------------------------------------------------------------

record ParentOntologyBoundary : Set where
  constructor parentOntologyBoundary
  field
    causalOriginIsSocialIdentity : Bool
    geneticContributionConfersParenthood : Bool
    parenthoodRequiresGeneticContribution : Bool
    wikidataSlotRecoversCarrier : Bool
    typeRecoversParentEligibility : Bool
    disclosureFollowsIdentityKnowledge : Bool
open ParentOntologyBoundary public

canonicalParentOntologyBoundary : ParentOntologyBoundary
canonicalParentOntologyBoundary =
  parentOntologyBoundary false false false false false false

causalOriginIsNotSocialIdentity :
  causalOriginIsSocialIdentity canonicalParentOntologyBoundary ≡ false
causalOriginIsNotSocialIdentity = refl

geneticContributionDoesNotConferParenthood :
  geneticContributionConfersParenthood canonicalParentOntologyBoundary ≡ false
geneticContributionDoesNotConferParenthood = refl

parenthoodDoesNotRequireGenetics :
  parenthoodRequiresGeneticContribution canonicalParentOntologyBoundary ≡ false
parenthoodDoesNotRequireGenetics = refl

wikidataSlotDoesNotRecoverCarrier :
  wikidataSlotRecoversCarrier canonicalParentOntologyBoundary ≡ false
wikidataSlotDoesNotRecoverCarrier = refl

typeDoesNotRecoverParentEligibility :
  typeRecoversParentEligibility canonicalParentOntologyBoundary ≡ false
typeDoesNotRecoverParentEligibility = refl

disclosureDoesNotFollowIdentityKnowledge :
  disclosureFollowsIdentityKnowledge canonicalParentOntologyBoundary ≡ false
disclosureDoesNotFollowIdentityKnowledge = refl
