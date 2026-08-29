module DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Experiment-relative equivalence of candidate physical theories.
--
-- This is the Agda-side bridge from the generic experiment calculus toward the
-- fundamental-physics programme.  It does not claim a quantum-gravity theory;
-- it states what an experimental language must be able to distinguish and what
-- a candidate must still recover before any physical promotion.
------------------------------------------------------------------------

Language : Set → Set₁
Language Experiment = Experiment → Set

Predictions : Set → Set → Set → Set₁
Predictions Theory Experiment Observation =
  Theory → Experiment → Observation → Set

EquivalentOn :
  ∀ {Theory Experiment Observation : Set} →
  Language Experiment →
  Predictions Theory Experiment Observation →
  Theory → Theory → Set
EquivalentOn language predicts left right =
  ∀ experiment → language experiment → ∀ observation →
    (predicts left experiment observation →
     predicts right experiment observation) ×
    (predicts right experiment observation →
     predicts left experiment observation)

LanguageExtends :
  ∀ {Experiment : Set} →
  Language Experiment → Language Experiment → Set
LanguageExtends stronger weaker =
  ∀ experiment → weaker experiment → stronger experiment

strongerEquivalenceImpliesWeakerEquivalence :
  ∀ {Theory Experiment Observation : Set}
    {stronger weaker : Language Experiment}
    {predicts : Predictions Theory Experiment Observation}
    {left right : Theory} →
  LanguageExtends stronger weaker →
  EquivalentOn stronger predicts left right →
  EquivalentOn weaker predicts left right
strongerEquivalenceImpliesWeakerEquivalence extends equivalent experiment inWeaker observation =
  equivalent experiment (extends experiment inWeaker) observation

------------------------------------------------------------------------
-- A discriminating experiment is a witness that one candidate admits an
-- observation excluded by the other, in either direction.
------------------------------------------------------------------------

Discriminates :
  ∀ {Theory Experiment Observation : Set} →
  Predictions Theory Experiment Observation →
  Experiment → Theory → Theory → Set
Discriminates predicts experiment left right =
  Σ _ λ observation →
    (predicts left experiment observation ×
     ¬ (predicts right experiment observation)) ⊎
    (predicts right experiment observation ×
     ¬ (predicts left experiment observation))

includedDiscriminatorRefutesEquivalence :
  ∀ {Theory Experiment Observation : Set}
    {language : Language Experiment}
    {predicts : Predictions Theory Experiment Observation}
    {experiment : Experiment}
    {left right : Theory} →
  language experiment →
  Discriminates predicts experiment left right →
  ¬ (EquivalentOn language predicts left right)
includedDiscriminatorRefutesEquivalence included
    (observation , inj₁ (leftYes , rightNo))
    equivalent =
  rightNo (proj₁ (equivalent _ included observation) leftYes)
includedDiscriminatorRefutesEquivalence included
    (observation , inj₂ (rightYes , leftNo))
    equivalent =
  leftNo (proj₂ (equivalent _ included observation) rightYes)

------------------------------------------------------------------------
-- Physical promotion gate.
--
-- Shared mathematics, a finite model, or an attractive bridge does not provide
-- these fields.  They are explicit obligations: recover established regimes,
-- expose a novel observable, and connect it to a falsifiable measurement.
------------------------------------------------------------------------

record FundamentalPhysicalCandidate : Set₁ where
  constructor fundamentalPhysicalCandidate
  field
    Candidate : Set
    recoversGeneralRelativityRegime : Set
    recoversLowEnergyQuantumFieldRegime : Set
    novelObservable : Set
    falsifiableMeasurement : Set

open FundamentalPhysicalCandidate public

PhysicalPromotionGate : FundamentalPhysicalCandidate → Set
PhysicalPromotionGate candidate =
  recoversGeneralRelativityRegime candidate ×
  recoversLowEnergyQuantumFieldRegime candidate ×
  novelObservable candidate ×
  falsifiableMeasurement candidate

promotionRequiresGRRecovery :
  ∀ {candidate : FundamentalPhysicalCandidate} →
  PhysicalPromotionGate candidate →
  recoversGeneralRelativityRegime candidate
promotionRequiresGRRecovery gate = proj₁ gate

promotionRequiresQFTRecovery :
  ∀ {candidate : FundamentalPhysicalCandidate} →
  PhysicalPromotionGate candidate →
  recoversLowEnergyQuantumFieldRegime candidate
promotionRequiresQFTRecovery gate = proj₁ (proj₂ gate)

promotionRequiresNovelObservable :
  ∀ {candidate : FundamentalPhysicalCandidate} →
  PhysicalPromotionGate candidate →
  novelObservable candidate
promotionRequiresNovelObservable gate = proj₁ (proj₂ (proj₂ gate))

promotionRequiresFalsifiableMeasurement :
  ∀ {candidate : FundamentalPhysicalCandidate} →
  PhysicalPromotionGate candidate →
  falsifiableMeasurement candidate
promotionRequiresFalsifiableMeasurement gate =
  proj₂ (proj₂ (proj₂ gate))

------------------------------------------------------------------------
-- Scope boundary.  YM/NS/RH can supply mathematics, stress tests or candidate
-- bridges elsewhere in the repository; none is promoted here into a physical
-- unification result merely by sharing formal structure.
------------------------------------------------------------------------

record PhysicalTheoryExperimentBoundary : Set where
  constructor physicalTheoryExperimentBoundary
  field
    sharedMathematicsIsPhysicalUnification : Bool
    sharedMathematicsIsPhysicalUnificationIsFalse :
      sharedMathematicsIsPhysicalUnification ≡ false

    candidateFitIsEstablishedTheoryRecovery : Bool
    candidateFitIsEstablishedTheoryRecoveryIsFalse :
      candidateFitIsEstablishedTheoryRecovery ≡ false

    newExperimentCanRefineTheoryEquivalence : Bool
    newExperimentCanRefineTheoryEquivalenceIsTrue :
      newExperimentCanRefineTheoryEquivalence ≡ true

canonicalPhysicalTheoryExperimentBoundary : PhysicalTheoryExperimentBoundary
canonicalPhysicalTheoryExperimentBoundary =
  physicalTheoryExperimentBoundary
    false refl
    false refl
    true refl
