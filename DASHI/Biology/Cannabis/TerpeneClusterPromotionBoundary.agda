module DASHI.Biology.Cannabis.TerpeneClusterPromotionBoundary where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

-- The six empirical clusters are represented as a finite codomain.  Their
-- names are deliberately neutral: the formalisation does not identify them
-- with indica, sativa, therapeutic classes, or mechanisms.
data TerpeneCluster : Set where
  cluster₀ cluster₁ cluster₂ cluster₃ cluster₄ cluster₅ : TerpeneCluster

data TraditionalLabel : Set where
  indica sativa hybrid unlabeled : TraditionalLabel

record TerpeneProfile (Terpene : Set) : Set where
  field
    abundance : Terpene → Nat

-- A receipt for the paper's actual theorem surface: measured profiles admit
-- an assignment into six chemical clusters.
record ChemicalClusterReceipt
  (Sample Terpene : Set) : Set₁ where
  field
    profile : Sample → TerpeneProfile Terpene
    classify : Sample → TerpeneCluster

-- Marketing/taxonomic labels are retained as a separate observable.  No map
-- from TraditionalLabel to TerpeneCluster is present or derivable from this
-- receipt alone.
record LabelObservation (Sample : Set) : Set where
  field
    label : Sample → TraditionalLabel

-- Observational association is intentionally relation-valued.  It does not
-- manufacture a deterministic effect function and it contains no
-- intervention or counterfactual witness.
record AssociationReceipt
  (Sample Effect : Set) : Set₁ where
  field
    reportedAssociation : Sample → Effect → Set

-- Promotion to a causal/clinical claim requires the missing experiment-level
-- coordinates.  These fields are abstract because different studies may use
-- different concrete encodings, but every promoted witness must supply them.
record CausalEffectReceipt
  (Sample Effect Dose Route Context Comparator Outcome : Set) : Set₁ where
  field
    assignedDose       : Sample → Dose
    assignedRoute      : Sample → Route
    administration     : Sample → Context
    comparator         : Sample → Comparator
    measuredOutcome    : Sample → Outcome
    effectInterpretation : Outcome → Effect
    controlledIntervention : Sample → Set

-- Evidence stages are constructors, not status booleans.  A chemical receipt
-- may be extended observationally, but only a causal receipt inhabits the
-- promoted constructor.
data ClusterEffectEvidence
  (Sample Terpene Effect Dose Route Context Comparator Outcome : Set) : Set₁ where
  chemical-only :
    ChemicalClusterReceipt Sample Terpene →
    ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator Outcome

  association-only :
    ChemicalClusterReceipt Sample Terpene →
    AssociationReceipt Sample Effect →
    ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator Outcome

  causally-promoted :
    ChemicalClusterReceipt Sample Terpene →
    CausalEffectReceipt Sample Effect Dose Route Context Comparator Outcome →
    ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator Outcome

data PromotionStatus : Set where
  cluster-established association-candidate clinical-promoted : PromotionStatus

status :
  {Sample Terpene Effect Dose Route Context Comparator Outcome : Set} →
  ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator Outcome →
  PromotionStatus
status (chemical-only _)       = cluster-established
status (association-only _ _)  = association-candidate
status (causally-promoted _ _) = clinical-promoted

-- Machine-checked boundaries corresponding to the central scientific point.
chemical-stays-chemical :
  {Sample Terpene Effect Dose Route Context Comparator Outcome : Set} →
  (r : ChemicalClusterReceipt Sample Terpene) →
  status {Effect = Effect} {Dose = Dose} {Route = Route} {Context = Context}
         {Comparator = Comparator} {Outcome = Outcome}
         (chemical-only r) ≡ cluster-established
chemical-stays-chemical r = refl

association-is-not-promotion :
  {Sample Terpene Effect Dose Route Context Comparator Outcome : Set} →
  (c : ChemicalClusterReceipt Sample Terpene) →
  (a : AssociationReceipt Sample Effect) →
  status {Dose = Dose} {Route = Route} {Context = Context}
         {Comparator = Comparator} {Outcome = Outcome}
         (association-only c a) ≡ association-candidate
association-is-not-promotion c a = refl

causal-witness-promotes :
  {Sample Terpene Effect Dose Route Context Comparator Outcome : Set} →
  (c : ChemicalClusterReceipt Sample Terpene) →
  (w : CausalEffectReceipt Sample Effect Dose Route Context Comparator Outcome) →
  status (causally-promoted c w) ≡ clinical-promoted
causal-witness-promotes c w = refl

-- A compact DASHI bundle: chemistry and labels may coexist, while the effect
-- lane remains explicitly staged and fail-closed.
record CannabisEvidenceBundle
  (Sample Terpene Effect Dose Route Context Comparator Outcome : Set) : Set₁ where
  field
    chemical : ChemicalClusterReceipt Sample Terpene
    labels   : LabelObservation Sample
    effectEvidence :
      ClusterEffectEvidence Sample Terpene Effect Dose Route Context Comparator Outcome
