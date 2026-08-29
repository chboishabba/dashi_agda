module DASHI.Biology.NeuroqueerRelationshipEcologyExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Intersectional
import DASHI.Biology.NeurodivergentSocialEcologySourceRegistryExact as Sources
import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- NEUROQUEER RELATIONSHIP ECOLOGY
--
-- Gender, sexuality, neurotype, relationship form, temporal expectations and
-- social recognition are kept distinct.  "Queering" is represented as a
-- practice of challenging or loosening normative scripts, not as a diagnosis,
-- sexual orientation, or claim that every autistic relationship is queer.
------------------------------------------------------------------------

data NeurotypeCoordinate : Set where
  autisticCoordinate otherNeurodivergentCoordinate comparisonCoordinate : NeurotypeCoordinate

data GenderCoordinate : Set where
  cisGender transGender nonbinaryGender otherGender : GenderCoordinate

data SexualityCoordinate : Set where
  heterosexual queerSexuality asexualSpectrum aromanticSpectrum otherSexuality : SexualityCoordinate

data RelationshipForm : Set where
  conventionalEscalator nonEscalatorRelationship friendshipIntimacy consensualPlurality intentionallyUnpartnered otherRelationshipForm : RelationshipForm

data TemporalScript : Set where
  linearMilestoneScript selfPacedScript nonLinearScript : TemporalScript

data NormRegime : Set where
  heteronormativeRegime neuroheteronormativeRegime pluralAffirmingRegime : NormRegime

data QueeringPractice : Set where
  questionNormativeScript loosenCategoryBoundary buildAlternativeRelationScript resistForcedNormalization : QueeringPractice

record IntimateEcology : Set where
  constructor intimateEcology
  field
    neurotype : NeurotypeCoordinate
    gender : GenderCoordinate
    sexuality : SexualityCoordinate
    relationshipForm : RelationshipForm
    temporality : TemporalScript
    normRegime : NormRegime
    axes : List Intersectional.IntersectionalAxis

open IntimateEcology public

------------------------------------------------------------------------
-- Queering is a relation to normativity, not a synonym for queer identity.
------------------------------------------------------------------------

practiceAvailable : NormRegime → QueeringPractice → Bool
practiceAvailable heteronormativeRegime practice = true
practiceAvailable neuroheteronormativeRegime practice = true
practiceAvailable pluralAffirmingRegime practice = true

data QueeringEqualsSexualOrientationPermission : Set where

queeringDoesNotCollapseToSexualOrientation :
  QueeringEqualsSexualOrientationPermission → ⊥
queeringDoesNotCollapseToSexualOrientation ()

data EveryAutisticRelationIsQueerPermission : Set where

everyAutisticRelationIsQueerRejected :
  EveryAutisticRelationIsQueerPermission → ⊥
everyAutisticRelationIsQueerRejected ()

------------------------------------------------------------------------
-- Relationship form and temporality do not factor through sexuality alone.
------------------------------------------------------------------------

data SexualityOnly : Set where queerLabel : SexualityOnly

data RelationshipReading : Set where escalatorReading nonEscalatorReading : RelationshipReading

data SituatedRelationship : Set where
  queerEscalatorState queerNonEscalatorState : SituatedRelationship

sexualityProjection : SituatedRelationship → SexualityOnly
sexualityProjection queerEscalatorState = queerLabel
sexualityProjection queerNonEscalatorState = queerLabel

relationshipReading : SituatedRelationship → RelationshipReading
relationshipReading queerEscalatorState = escalatorReading
relationshipReading queerNonEscalatorState = nonEscalatorReading

sameSexualityDifferentRelationshipForm :
  sexualityProjection queerEscalatorState ≡ sexualityProjection queerNonEscalatorState
sameSexualityDifferentRelationshipForm = refl

relationshipFormsDiffer :
  relationshipReading queerEscalatorState ≡ relationshipReading queerNonEscalatorState → ⊥
relationshipFormsDiffer ()

sexualityAloneDoesNotExhaustRelationshipEcology :
  NonFactor.NonFactorabilityWitness sexualityProjection relationshipReading
sexualityAloneDoesNotExhaustRelationshipEcology =
  NonFactor.nonFactorabilityWitness
    queerEscalatorState
    queerNonEscalatorState
    sameSexualityDifferentRelationshipForm
    relationshipFormsDiffer

------------------------------------------------------------------------
-- Neurotype and sexuality are distinct axes while their situated consequences
-- may be non-additive through institutions, norms and relationship scripts.
------------------------------------------------------------------------

canonicalAutisticQueerEcology : IntimateEcology
canonicalAutisticQueerEcology =
  intimateEcology
    autisticCoordinate
    nonbinaryGender
    queerSexuality
    nonEscalatorRelationship
    selfPacedScript
    pluralAffirmingRegime
    Intersectional.canonicalIntersectionalAxes

record NeuroqueerBoundary : Set where
  constructor neuroqueerBoundary
  field
    neurotypeEqualsSexuality : Bool
    neurotypeEqualsSexualityIsFalse : neurotypeEqualsSexuality ≡ false
    queeringIsRepresentedAsPractice : Bool
    queeringIsRepresentedAsPracticeIsTrue : queeringIsRepresentedAsPractice ≡ true
    relationshipEscalatorIsUniversalHealthyEndpoint : Bool
    relationshipEscalatorIsUniversalHealthyEndpointIsFalse :
      relationshipEscalatorIsUniversalHealthyEndpoint ≡ false
    nonnormativeRelationshipAutomaticallyUnsafe : Bool
    nonnormativeRelationshipAutomaticallyUnsafeIsFalse :
      nonnormativeRelationshipAutomaticallyUnsafe ≡ false
    sexualityAxisCanBeOmittedFromNeurodivergenceEcology : Bool
    sexualityAxisCanBeOmittedFromNeurodivergenceEcologyIsFalse :
      sexualityAxisCanBeOmittedFromNeurodivergenceEcology ≡ false

canonicalNeuroqueerBoundary : NeuroqueerBoundary
canonicalNeuroqueerBoundary =
  neuroqueerBoundary false refl true refl false refl false refl false refl

neuroqueerSource : Sources.SourceReference
neuroqueerSource = Sources.neuroqueer2021

yergeauSource : Sources.SourceReference
yergeauSource = Sources.yergeau2018

intimateLivesSource : Sources.SourceReference
intimateLivesSource = Sources.neuroqueerIntimacy2026

genderDiversitySource : Sources.SourceReference
genderDiversitySource = Sources.genderDiversity2025

intersectionalitySource : Sources.SourceReference
intersectionalitySource = Sources.crenshaw1991
