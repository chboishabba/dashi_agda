module DASHI.Physics.YangMills.BalabanClayT2ClusterCriterionComparisonExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization and exact hierarchy.
--
-- R. Kotecký and D. Preiss,
-- "Cluster expansion for abstract polymer models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
--
-- R. Fernández and A. Procacci,
-- "Cluster expansion for abstract polymer models. New bounds from an old
-- approach",
-- Communications in Mathematical Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2
--
-- R. Bissacot, R. Fernández and A. Procacci,
-- "On the convergence of cluster expansions for polymer gases",
-- Journal of Statistical Physics 139 (2010), 598--617.
-- DOI: 10.1007/s10955-010-9956-1
--
-- C. Gruber and H. Kunz,
-- "General properties of polymer systems",
-- Communications in Mathematical Physics 22 (1971), 133--161.
-- DOI: 10.1007/BF01651334
--
-- For abstract polymers, the published comparison is represented here by
--
--   Fernandez--Procacci majorant <= Dobrushin majorant <= KP majorant.
--
-- Hence a KP witness implies a Dobrushin witness, which implies an FP witness.
-- The converses do not follow.  For subset polymers, the Bissacot--Fernández--
-- Procacci analysis identifies the suitable extended Gruber--Kunz lane with the
-- sharper subset criterion after the corresponding model-specific majorants
-- are shown equal.  No universal extra "interpolating" criterion is invented.
------------------------------------------------------------------------

record PolymerCriterionComparison (Polymer : Set) : Set₁ where
  field
    activity budget : Polymer → ℚ

    kpExponentialMajorant : Polymer → ℚ
    dobrushinMajorant : Polymer → ℚ
    fernandezProcacciMajorant : Polymer → ℚ

    -- Activities here are absolute activities.  This explicit sign convention
    -- is required before multiplying a majorant inequality by the activity.
    activityNonnegative : ∀ polymer → 0ℚ ≤ activity polymer
    activityTimesMonotone : ∀ polymer {left right} →
      left ≤ right →
      activity polymer * left ≤ activity polymer * right

    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right

    dobrushinBelowKP : ∀ polymer →
      dobrushinMajorant polymer ≤ kpExponentialMajorant polymer

    fernandezProcacciBelowDobrushin : ∀ polymer →
      fernandezProcacciMajorant polymer ≤ dobrushinMajorant polymer

open PolymerCriterionComparison public

KoteckyPreissCriterion : ∀ {Polymer} →
  PolymerCriterionComparison Polymer → Set
KoteckyPreissCriterion dataSet = ∀ polymer →
  activity dataSet polymer * kpExponentialMajorant dataSet polymer
  ≤ budget dataSet polymer

DobrushinCriterion : ∀ {Polymer} →
  PolymerCriterionComparison Polymer → Set
DobrushinCriterion dataSet = ∀ polymer →
  activity dataSet polymer * dobrushinMajorant dataSet polymer
  ≤ budget dataSet polymer

FernandezProcacciCriterion : ∀ {Polymer} →
  PolymerCriterionComparison Polymer → Set
FernandezProcacciCriterion dataSet = ∀ polymer →
  activity dataSet polymer * fernandezProcacciMajorant dataSet polymer
  ≤ budget dataSet polymer

koteckyPreissImpliesDobrushin :
  ∀ {Polymer} (dataSet : PolymerCriterionComparison Polymer) →
  KoteckyPreissCriterion dataSet →
  DobrushinCriterion dataSet
koteckyPreissImpliesDobrushin dataSet kp polymer =
  transitive dataSet
    (activityTimesMonotone dataSet polymer
      (dobrushinBelowKP dataSet polymer))
    (kp polymer)

dobrushinImpliesFernandezProcacci :
  ∀ {Polymer} (dataSet : PolymerCriterionComparison Polymer) →
  DobrushinCriterion dataSet →
  FernandezProcacciCriterion dataSet
dobrushinImpliesFernandezProcacci dataSet dobrushin polymer =
  transitive dataSet
    (activityTimesMonotone dataSet polymer
      (fernandezProcacciBelowDobrushin dataSet polymer))
    (dobrushin polymer)

koteckyPreissImpliesFernandezProcacci :
  ∀ {Polymer} (dataSet : PolymerCriterionComparison Polymer) →
  KoteckyPreissCriterion dataSet →
  FernandezProcacciCriterion dataSet
koteckyPreissImpliesFernandezProcacci dataSet kp =
  dobrushinImpliesFernandezProcacci dataSet
    (koteckyPreissImpliesDobrushin dataSet kp)

------------------------------------------------------------------------
-- Subset-polymer identification and optional later refinements.
------------------------------------------------------------------------

record ExtendedGruberKunzIdentification
    {Polymer : Set}
    (dataSet : PolymerCriterionComparison Polymer) : Set₁ where
  field
    extendedGruberKunzMajorant : Polymer → ℚ
    extendedGKMatchesFernandezProcacci : ∀ polymer →
      extendedGruberKunzMajorant polymer
      ≡ fernandezProcacciMajorant dataSet polymer

open ExtendedGruberKunzIdentification public

ExtendedGruberKunzCriterion :
  ∀ {Polymer}
    (dataSet : PolymerCriterionComparison Polymer) →
    ExtendedGruberKunzIdentification dataSet → Set
ExtendedGruberKunzCriterion dataSet identification = ∀ polymer →
  activity dataSet polymer
    * extendedGruberKunzMajorant identification polymer
  ≤ budget dataSet polymer

fernandezProcacciImpliesExtendedGruberKunz :
  ∀ {Polymer}
    (dataSet : PolymerCriterionComparison Polymer)
    (identification : ExtendedGruberKunzIdentification dataSet) →
  FernandezProcacciCriterion dataSet →
  ExtendedGruberKunzCriterion dataSet identification
fernandezProcacciImpliesExtendedGruberKunz dataSet identification fp polymer =
  subst
    (λ selectedMajorant →
      activity dataSet polymer * selectedMajorant
      ≤ budget dataSet polymer)
    (extendedGKMatchesFernandezProcacci identification polymer)
    (fp polymer)

record FurtherCriterionRefinement
    {Polymer : Set}
    (dataSet : PolymerCriterionComparison Polymer) : Set₁ where
  field
    refinedMajorant : Polymer → ℚ
    refinedBelowFernandezProcacci : ∀ polymer →
      refinedMajorant polymer ≤ fernandezProcacciMajorant dataSet polymer

open FurtherCriterionRefinement public

RefinedCriterion :
  ∀ {Polymer}
    (dataSet : PolymerCriterionComparison Polymer) →
    FurtherCriterionRefinement dataSet → Set
RefinedCriterion dataSet refinement = ∀ polymer →
  activity dataSet polymer * refinedMajorant refinement polymer
  ≤ budget dataSet polymer

fernandezProcacciImpliesRefined :
  ∀ {Polymer}
    (dataSet : PolymerCriterionComparison Polymer)
    (refinement : FurtherCriterionRefinement dataSet) →
  FernandezProcacciCriterion dataSet →
  RefinedCriterion dataSet refinement
fernandezProcacciImpliesRefined dataSet refinement fp polymer =
  transitive dataSet
    (activityTimesMonotone dataSet polymer
      (refinedBelowFernandezProcacci refinement polymer))
    (fp polymer)

record StrictCriterionSlack
    {Polymer : Set}
    (dataSet : PolymerCriterionComparison Polymer) : Set₁ where
  field
    witnessPolymer : Polymer
    StrictlyLess : ℚ → ℚ → Set
    dobrushinStrictlyBelowKP :
      StrictlyLess
        (dobrushinMajorant dataSet witnessPolymer)
        (kpExponentialMajorant dataSet witnessPolymer)
    fpStrictlyBelowDobrushin :
      StrictlyLess
        (fernandezProcacciMajorant dataSet witnessPolymer)
        (dobrushinMajorant dataSet witnessPolymer)

open StrictCriterionSlack public

kpToDobrushinDominanceLevel : ProofLevel
kpToDobrushinDominanceLevel = machineChecked

dobrushinToFernandezProcacciDominanceLevel : ProofLevel
dobrushinToFernandezProcacciDominanceLevel = machineChecked

fernandezProcacciToExtendedGKIdentificationLevel : ProofLevel
fernandezProcacciToExtendedGKIdentificationLevel = machineChecked

polymerCriterionSignConventionLevel : ProofLevel
polymerCriterionSignConventionLevel = machineChecked

-- Strict improvement and the extended-GK identification are physical/model
-- statements: they require the actual incompatibility neighbourhood and subset
-- support structure.  They are not inferred merely from criterion names.
physicalStrictCriterionSlackLevel : ProofLevel
physicalStrictCriterionSlackLevel = conditional

physicalExtendedGKIdentificationLevel : ProofLevel
physicalExtendedGKIdentificationLevel = conditional
