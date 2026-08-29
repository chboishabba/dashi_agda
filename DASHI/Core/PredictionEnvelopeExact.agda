module DASHI.Core.PredictionEnvelopeExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Prediction envelopes over evidence fibres.
--
-- This is the Agda-side counterpart of the Stage-6 principle that the
-- existing determination/factorisation geometry is exactly the point-valued
-- special case of set-valued prediction.  No probability semantics are
-- introduced here.
------------------------------------------------------------------------

Compatible : Set → Set → Set₁
Compatible Evidence State = Evidence → State → Set

PredictionEnvelope :
  ∀ {Evidence State Prediction : Set} →
  Compatible Evidence State →
  (State → Prediction) →
  Evidence → Prediction → Set
PredictionEnvelope compatible consumer evidence prediction =
  Σ _ λ state →
    compatible evidence state × consumer state ≡ prediction

EvidenceRefines :
  ∀ {Evidence State : Set} →
  Compatible Evidence State →
  Evidence → Evidence → Set
EvidenceRefines compatible stronger weaker =
  ∀ state → compatible stronger state → compatible weaker state

refinementTightensEnvelope :
  ∀ {Evidence State Prediction : Set}
    {compatible : Compatible Evidence State}
    {consumer : State → Prediction}
    {stronger weaker : Evidence}
    {prediction : Prediction} →
  EvidenceRefines compatible stronger weaker →
  PredictionEnvelope compatible consumer stronger prediction →
  PredictionEnvelope compatible consumer weaker prediction
refinementTightensEnvelope refines (state , strong , value) =
  state , refines state strong , value

PointIdentifiable :
  ∀ {Evidence State Prediction : Set} →
  Compatible Evidence State →
  (State → Prediction) →
  Evidence → Set
PointIdentifiable compatible consumer evidence =
  ∀ x y →
    compatible evidence x →
    compatible evidence y →
    consumer x ≡ consumer y

EnvelopeUnique :
  ∀ {Evidence State Prediction : Set} →
  Compatible Evidence State →
  (State → Prediction) →
  Evidence → Set
EnvelopeUnique compatible consumer evidence =
  ∀ {p q} →
    PredictionEnvelope compatible consumer evidence p →
    PredictionEnvelope compatible consumer evidence q →
    p ≡ q

pointIdentifiableImpliesEnvelopeUnique :
  ∀ {Evidence State Prediction : Set}
    {compatible : Compatible Evidence State}
    {consumer : State → Prediction}
    {evidence : Evidence} →
  PointIdentifiable compatible consumer evidence →
  EnvelopeUnique compatible consumer evidence
pointIdentifiableImpliesEnvelopeUnique identifiable
    (x , hx , refl)
    (y , hy , refl) =
  identifiable x y hx hy

envelopeUniqueImpliesPointIdentifiable :
  ∀ {Evidence State Prediction : Set}
    {compatible : Compatible Evidence State}
    {consumer : State → Prediction}
    {evidence : Evidence} →
  EnvelopeUnique compatible consumer evidence →
  PointIdentifiable compatible consumer evidence
envelopeUniqueImpliesPointIdentifiable unique x y hx hy =
  unique (x , hx , refl) (y , hy , refl)

------------------------------------------------------------------------
-- Joint evidence is ordinary fibre intersection.  This keeps "more evidence
-- narrows predictions" separate from any probabilistic weighting.
------------------------------------------------------------------------

JointCompatible :
  ∀ {Evidence₁ Evidence₂ State : Set} →
  Compatible Evidence₁ State →
  Compatible Evidence₂ State →
  Evidence₁ × Evidence₂ → State → Set
JointCompatible compatible₁ compatible₂ evidence state =
  compatible₁ (proj₁ evidence) state ×
  compatible₂ (proj₂ evidence) state

jointEvidenceRefinesLeft :
  ∀ {Evidence₁ Evidence₂ State : Set}
    {compatible₁ : Compatible Evidence₁ State}
    {compatible₂ : Compatible Evidence₂ State}
    {evidence₁ : Evidence₁}
    {evidence₂ : Evidence₂} →
  ∀ state →
    JointCompatible compatible₁ compatible₂ (evidence₁ , evidence₂) state →
    compatible₁ evidence₁ state
jointEvidenceRefinesLeft state joint = proj₁ joint

jointEvidenceRefinesRight :
  ∀ {Evidence₁ Evidence₂ State : Set}
    {compatible₁ : Compatible Evidence₁ State}
    {compatible₂ : Compatible Evidence₂ State}
    {evidence₁ : Evidence₁}
    {evidence₂ : Evidence₂} →
  ∀ state →
    JointCompatible compatible₁ compatible₂ (evidence₁ , evidence₂) state →
    compatible₂ evidence₂ state
jointEvidenceRefinesRight state joint = proj₂ joint

------------------------------------------------------------------------
-- A measurement can refine an evidence fibre.  Whether that refinement makes
-- a particular downstream consumer point-identifiable is itself the exact
-- "does this next measurement close the envelope?" question.
------------------------------------------------------------------------

MeasuredCompatible :
  ∀ {Evidence State Measurement : Set} →
  Compatible Evidence State →
  (State → Measurement) →
  Evidence × Measurement → State → Set
MeasuredCompatible compatible measure evidence state =
  compatible (proj₁ evidence) state ×
  measure state ≡ proj₂ evidence

MeasurementClosesEnvelope :
  ∀ {Evidence State Measurement Prediction : Set} →
  Compatible Evidence State →
  (State → Measurement) →
  (State → Prediction) →
  Evidence × Measurement → Set
MeasurementClosesEnvelope compatible measure consumer evidence =
  PointIdentifiable
    (MeasuredCompatible compatible measure)
    consumer
    evidence

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record PredictionEnvelopeBoundary : Set where
  constructor predictionEnvelopeBoundary
  field
    pointPredictionIsFibreUniqueness : Bool
    pointPredictionIsFibreUniquenessIsTrue :
      pointPredictionIsFibreUniqueness ≡ true

    refinementCanOnlyRemoveCompatibleStates : Bool
    refinementCanOnlyRemoveCompatibleStatesIsTrue :
      refinementCanOnlyRemoveCompatibleStates ≡ true

    envelopeCarriesProbabilityWeightsByDefinition : Bool
    envelopeCarriesProbabilityWeightsByDefinitionIsFalse :
      envelopeCarriesProbabilityWeightsByDefinition ≡ false

canonicalPredictionEnvelopeBoundary : PredictionEnvelopeBoundary
canonicalPredictionEnvelopeBoundary =
  predictionEnvelopeBoundary
    true refl
    true refl
    false refl
