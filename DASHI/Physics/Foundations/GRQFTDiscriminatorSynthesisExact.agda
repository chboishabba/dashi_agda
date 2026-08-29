module DASHI.Physics.Foundations.GRQFTDiscriminatorSynthesisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CommonExperimentRealisationExact as Common
import DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact as Physical

------------------------------------------------------------------------
-- GR/QFT DISCRIMINATOR SYNTHESIS
--
-- Cross-pollinates the common-metric-language discipline from the recovery lane
-- with experiment-relative physical theory discrimination.  A candidate
-- experiment is compared only after one external experiment has been realised
-- into both candidate implementations.
------------------------------------------------------------------------

ExtendedLanguage :
  ∀ {Experiment : Set} →
  Physical.Language Experiment → Experiment → Physical.Language Experiment
ExtendedLanguage current selected experiment =
  current experiment ⊎ experiment ≡ selected

selectedIsInExtendedLanguage :
  ∀ {Experiment : Set}
    {current : Physical.Language Experiment}
    {selected : Experiment} →
  ExtendedLanguage current selected selected
selectedIsInExtendedLanguage = inj₂ refl

record MinimalPhysicalDiscriminator : Set₂ where
  constructor minimalPhysicalDiscriminator
  field
    Theory : Set
    common : Common.CommonExperimentRealisation Theory Theory
    Observation : Set

    currentLanguage : Physical.Language (Common.Experiment common)
    predicts : Physical.Predictions
      Theory (Common.Experiment common) Observation

    left right : Theory
    currentlyEquivalent :
      Physical.EquivalentOn currentLanguage predicts left right

    Declared : Common.Experiment common → Set
    experimentCost : Common.Experiment common → Nat
    selected : Common.Experiment common
    selectedDeclared : Declared selected
    selectedDiscriminates :
      Physical.Discriminates predicts selected left right

    minimal :
      (alternative : Common.Experiment common) →
      Declared alternative →
      Physical.Discriminates predicts alternative left right →
      experimentCost selected ≤ experimentCost alternative

    physicalCandidate : Physical.FundamentalPhysicalCandidate
    grRecoveryReference :
      Physical.recoversGeneralRelativityRegime physicalCandidate
    qftRecoveryReference :
      Physical.recoversLowEnergyQuantumFieldRegime physicalCandidate

    theoryCarrierIdentificationReference : String
    nuisanceAndSystematicsReference : String
    apparatusAuthorityReference : String
    synthesisReference : String

open MinimalPhysicalDiscriminator public

selectedExtensionRefutesEquivalence :
  (search : MinimalPhysicalDiscriminator) →
  ¬ (Physical.EquivalentOn
      (ExtendedLanguage (currentLanguage search) (selected search))
      (predicts search)
      (left search)
      (right search))
selectedExtensionRefutesEquivalence search =
  Physical.includedDiscriminatorRefutesEquivalence
    selectedIsInExtendedLanguage
    (selectedDiscriminates search)

------------------------------------------------------------------------
-- The common-realisation record supplies the analogue of PR #639's common
-- metric perturbation language: candidate-internal apparatus coordinates may
-- differ, but one external experiment names the comparison.
------------------------------------------------------------------------

record GRQFTDiscriminatorSynthesisBoundary : Set where
  constructor grqftDiscriminatorSynthesisBoundary
  field
    grAndQFTRecoveryAreReferenceConstraintsNotFreeControlKnobs : Bool
    grAndQFTRecoveryAreReferenceConstraintsNotFreeControlKnobsIsTrue :
      grAndQFTRecoveryAreReferenceConstraintsNotFreeControlKnobs ≡ true

    independentInternalApparatusCoordinatesAutomaticallyMeanSameExperiment : Bool
    independentInternalApparatusCoordinatesAutomaticallyMeanSameExperimentIsFalse :
      independentInternalApparatusCoordinatesAutomaticallyMeanSameExperiment ≡ false

    minimalDiscriminatorAloneCompletesPhysicalPromotion : Bool
    minimalDiscriminatorAloneCompletesPhysicalPromotionIsFalse :
      minimalDiscriminatorAloneCompletesPhysicalPromotion ≡ false

    addedExperimentCanStrictlyRefineCandidateTheoryLanguage : Bool
    addedExperimentCanStrictlyRefineCandidateTheoryLanguageIsTrue :
      addedExperimentCanStrictlyRefineCandidateTheoryLanguage ≡ true

canonicalGRQFTDiscriminatorSynthesisBoundary :
  GRQFTDiscriminatorSynthesisBoundary
canonicalGRQFTDiscriminatorSynthesisBoundary =
  grqftDiscriminatorSynthesisBoundary true refl false refl false refl true refl
