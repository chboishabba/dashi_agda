module DASHI.Reasoning.SemanticInterventionEquivarianceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

data InterventionKind : Set where
  labelChanging : InterventionKind
  labelInvariant : InterventionKind
  structural : InterventionKind

record SemanticIntervention (X Y : Set) : Set₁ where
  constructor semantic-intervention
  field
    actX : X → X
    actY : Y → Y
    kind : InterventionKind
    provenance : String

open SemanticIntervention public

record PairCorrect
    {X Y : Set}
    (model : X → Y)
    (intervention : SemanticIntervention X Y)
    (x : X) : Set where
  constructor pair-correct
  field
    transformedCorrect :
      model (actX intervention x)
      ≡ actY intervention (model x)

open PairCorrect public

record ModelEquivariance
    {X Y : Set}
    (model : X → Y)
    (intervention : SemanticIntervention X Y) : Set where
  constructor model-equivariance
  field
    commutes :
      (x : X) →
      model (actX intervention x)
      ≡ actY intervention (model x)

open ModelEquivariance public

modelEquivarianceYieldsPairCorrect :
  ∀ {X Y : Set}
    {model : X → Y}
    {intervention : SemanticIntervention X Y} →
  ModelEquivariance model intervention →
  (x : X) →
  PairCorrect model intervention x
modelEquivarianceYieldsPairCorrect equivariance x =
  pair-correct (commutes equivariance x)

record RepresentationEquivariance
    {X Y Z : Set}
    (model : X → Y)
    (intervention : SemanticIntervention X Y) : Set₁ where
  constructor representation-equivariance
  field
    encode : X → Z
    decode : Z → Y
    representationAction : Z → Z
    modelFactorsThroughRepresentation :
      (x : X) → decode (encode x) ≡ model x
    representationCommutes :
      (x : X) →
      encode (actX intervention x)
      ≡ representationAction (encode x)
    decoderCompatible :
      (z : Z) →
      decode (representationAction z)
      ≡ actY intervention (decode z)
    justification : String

open RepresentationEquivariance public

representationEquivarianceImpliesModelEquivariance :
  ∀ {X Y Z : Set}
    {model : X → Y}
    {intervention : SemanticIntervention X Y} →
  RepresentationEquivariance {X} {Y} {Z} model intervention →
  ModelEquivariance model intervention
representationEquivarianceImpliesModelEquivariance
    {intervention = intervention} witness =
  model-equivariance λ x →
    trans
      (sym (modelFactorsThroughRepresentation witness (actX intervention x)))
      (trans
        (cong (decode witness) (representationCommutes witness x))
        (trans
          (decoderCompatible witness (encode witness x))
          (cong (actY intervention)
            (modelFactorsThroughRepresentation witness x))))

representationToModelEquivarianceTheoremAvailable : Bool
representationToModelEquivarianceTheoremAvailable = true

record InterventionComposition
    {X Y : Set}
    (first second composed : SemanticIntervention X Y) : Set where
  constructor intervention-composition
  field
    inputComposition :
      (x : X) → actX composed x ≡ actX first (actX second x)
    outputComposition :
      (y : Y) → actY composed y ≡ actY first (actY second y)

open InterventionComposition public

modelEquivarianceComposes :
  ∀ {X Y : Set}
    {model : X → Y}
    {first second composed : SemanticIntervention X Y} →
  InterventionComposition first second composed →
  ModelEquivariance model first →
  ModelEquivariance model second →
  ModelEquivariance model composed
modelEquivarianceComposes
    {first = first} {second = second} {composed = composed}
    composition firstEq secondEq =
  model-equivariance λ x →
    trans
      (cong model (inputComposition composition x))
      (trans
        (commutes firstEq (actX second x))
        (trans
          (cong (actY first) (commutes secondEq x))
          (sym (outputComposition composition (model x)))))

data PairAccuracyCreatesRepresentationLaw : Set where
data RepresentationGeometryCreatesCausalMechanism : Set where
data InterventionFitCreatesScientificAuthority : Set where

pairAccuracyCannotCreateRepresentationLaw :
  PairAccuracyCreatesRepresentationLaw → ⊥
pairAccuracyCannotCreateRepresentationLaw ()

geometryCannotCreateCausalMechanism :
  RepresentationGeometryCreatesCausalMechanism → ⊥
geometryCannotCreateCausalMechanism ()

fitCannotCreateScientificAuthority :
  InterventionFitCreatesScientificAuthority → ⊥
fitCannotCreateScientificAuthority ()

record SemanticInterventionEquivarianceBoundary : Set where
  constructor semantic-intervention-equivariance-boundary
  field
    interventionKindsTyped : Bool
    pairCorrectTyped : Bool
    representationEquivarianceTyped : Bool
    decoderCompatibilityTyped : Bool
    representationToModelTheoremPaid : Bool
    compositionTheoremPaid : Bool
    empiricalFitAutomaticallyCreatesMechanism : Bool
    geometryAutomaticallyCreatesAuthority : Bool

canonicalSemanticInterventionEquivarianceBoundary :
  SemanticInterventionEquivarianceBoundary
canonicalSemanticInterventionEquivarianceBoundary =
  semantic-intervention-equivariance-boundary
    true true true true true true false false
