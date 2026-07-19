module DASHI.Biology.Cannabis.TerpeneClusterPromotionBoundary where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

-- Neutral empirical codomain.  The constructors do not carry therapeutic,
-- taxonomic, or mechanistic meaning.
data TerpeneCluster : Set where
  cluster₀ cluster₁ cluster₂ cluster₃ cluster₄ cluster₅ : TerpeneCluster

data TraditionalLabel : Set where
  indica sativa hybrid unlabeled : TraditionalLabel

record TerpeneProfile (Terpene : Set) : Set where
  field
    abundance : Terpene → Nat

record ChemicalClusterReceipt
  (Sample Terpene : Set) : Set₁ where
  field
    profile  : Sample → TerpeneProfile Terpene
    classify : Sample → TerpeneCluster

record LabelObservation (Sample : Set) : Set where
  field
    label : Sample → TraditionalLabel

-- Association is relation-valued and therefore does not manufacture an
-- effect function, intervention, counterfactual, or clinical recommendation.
record AssociationReceipt
  (Sample Effect : Set) : Set₁ where
  field
    reportedAssociation : Sample → Effect → Set

-- An experiment protocol must be supplied together with an inhabitant of its
-- validity proposition.  This closes the former loophole where an empty
-- Sample → Set field could accompany a promoted constructor.
record ValidatedProtocol
  (Sample Protocol : Set) : Set₁ where
  field
    protocol      : Sample → Protocol
    validProtocol : Sample → Set
    validation    : (sample : Sample) → validProtocol sample

-- The tested exposure must be linked to the chemical object under discussion.
-- Merely recording dose and outcome is not enough to support a terpene claim.
record ExposureLink
  (Sample Exposure : Set) : Set₁ where
  field
    exposure       : Sample → Exposure
    exposureMatchesClaim : Sample → Set
    matchWitness   : (sample : Sample) → exposureMatchesClaim sample

record CausalStudyReceipt
  (Sample Effect Dose Route Context Comparator Outcome Protocol Exposure : Set)
  : Set₁ where
  field
    assignedDose         : Sample → Dose
    assignedRoute        : Sample → Route
    administration       : Sample → Context
    comparator           : Sample → Comparator
    measuredOutcome      : Sample → Outcome
    effectInterpretation : Outcome → Effect
    protocolReceipt      : ValidatedProtocol Sample Protocol
    exposureReceipt      : ExposureLink Sample Exposure

-- A single controlled study supports a bounded causal-study claim only.
-- Replication and clinical translation have separate constructors and proof
-- obligations.
record ReplicationReceipt (Study Population : Set) : Set₁ where
  field
    replicationStudy : Study
    targetPopulation : Population
    agreesWithPrior  : Set
    agreementWitness : agreesWithPrior

record ClinicalTranslationReceipt
  (Population Endpoint Harm Uncertainty Recommendation : Set) : Set₁ where
  field
    targetPopulation      : Population
    clinicallyRelevantEnd : Endpoint
    adverseEffectModel    : Harm
    uncertaintyModel      : Uncertainty
    recommendation        : Recommendation
    translationValid      : Set
    translationWitness    : translationValid

data ClusterEffectEvidence
  (Sample Terpene Effect Dose Route Context Comparator Outcome Protocol Exposure
   Study Population Endpoint Harm Uncertainty Recommendation : Set) : Set₁ where

  chemical-only :
    ChemicalClusterReceipt Sample Terpene →
    ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator
      Outcome Protocol Exposure Study Population Endpoint Harm Uncertainty Recommendation

  association-only :
    ChemicalClusterReceipt Sample Terpene →
    AssociationReceipt Sample Effect →
    ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator
      Outcome Protocol Exposure Study Population Endpoint Harm Uncertainty Recommendation

  causal-study-supported :
    ChemicalClusterReceipt Sample Terpene →
    CausalStudyReceipt Sample Effect Dose Route Context Comparator Outcome Protocol Exposure →
    ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator
      Outcome Protocol Exposure Study Population Endpoint Harm Uncertainty Recommendation

  replicated-effect-supported :
    ChemicalClusterReceipt Sample Terpene →
    CausalStudyReceipt Sample Effect Dose Route Context Comparator Outcome Protocol Exposure →
    ReplicationReceipt Study Population →
    ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator
      Outcome Protocol Exposure Study Population Endpoint Harm Uncertainty Recommendation

  clinical-translation-supported :
    ChemicalClusterReceipt Sample Terpene →
    CausalStudyReceipt Sample Effect Dose Route Context Comparator Outcome Protocol Exposure →
    ReplicationReceipt Study Population →
    ClinicalTranslationReceipt Population Endpoint Harm Uncertainty Recommendation →
    ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator
      Outcome Protocol Exposure Study Population Endpoint Harm Uncertainty Recommendation

data PromotionStatus : Set where
  chemical-established
  association-candidate
  causal-study-bounded
  replicated-effect-bounded
  clinical-translation-bounded : PromotionStatus

status :
  {Sample Terpene Effect Dose Route Context Comparator Outcome Protocol Exposure
   Study Population Endpoint Harm Uncertainty Recommendation : Set} →
  ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator
    Outcome Protocol Exposure Study Population Endpoint Harm Uncertainty Recommendation →
  PromotionStatus
status (chemical-only _)                    = chemical-established
status (association-only _ _)               = association-candidate
status (causal-study-supported _ _)          = causal-study-bounded
status (replicated-effect-supported _ _ _)   = replicated-effect-bounded
status (clinical-translation-supported _ _ _ _) = clinical-translation-bounded

chemical-stays-chemical :
  {Sample Terpene Effect Dose Route Context Comparator Outcome Protocol Exposure
   Study Population Endpoint Harm Uncertainty Recommendation : Set} →
  (r : ChemicalClusterReceipt Sample Terpene) →
  status {Effect = Effect} {Dose = Dose} {Route = Route} {Context = Context}
    {Comparator = Comparator} {Outcome = Outcome} {Protocol = Protocol}
    {Exposure = Exposure} {Study = Study} {Population = Population}
    {Endpoint = Endpoint} {Harm = Harm} {Uncertainty = Uncertainty}
    {Recommendation = Recommendation} (chemical-only r)
    ≡ chemical-established
chemical-stays-chemical r = refl

association-is-candidate-only :
  {Sample Terpene Effect Dose Route Context Comparator Outcome Protocol Exposure
   Study Population Endpoint Harm Uncertainty Recommendation : Set} →
  (c : ChemicalClusterReceipt Sample Terpene) →
  (a : AssociationReceipt Sample Effect) →
  status {Dose = Dose} {Route = Route} {Context = Context}
    {Comparator = Comparator} {Outcome = Outcome} {Protocol = Protocol}
    {Exposure = Exposure} {Study = Study} {Population = Population}
    {Endpoint = Endpoint} {Harm = Harm} {Uncertainty = Uncertainty}
    {Recommendation = Recommendation} (association-only c a)
    ≡ association-candidate
association-is-candidate-only c a = refl

causal-study-does-not-skip-replication :
  {Sample Terpene Effect Dose Route Context Comparator Outcome Protocol Exposure
   Study Population Endpoint Harm Uncertainty Recommendation : Set} →
  (c : ChemicalClusterReceipt Sample Terpene) →
  (w : CausalStudyReceipt Sample Effect Dose Route Context Comparator Outcome Protocol Exposure) →
  status {Study = Study} {Population = Population} {Endpoint = Endpoint}
    {Harm = Harm} {Uncertainty = Uncertainty} {Recommendation = Recommendation}
    (causal-study-supported c w) ≡ causal-study-bounded
causal-study-does-not-skip-replication c w = refl

record CannabisEvidenceBundle
  (Sample Terpene Effect Dose Route Context Comparator Outcome Protocol Exposure
   Study Population Endpoint Harm Uncertainty Recommendation : Set) : Set₁ where
  field
    chemical : ChemicalClusterReceipt Sample Terpene
    labels   : LabelObservation Sample
    evidence : ClusterEffectEvidence Sample Terpene Effect Dose Route Context
      Comparator Outcome Protocol Exposure Study Population Endpoint Harm
      Uncertainty Recommendation
