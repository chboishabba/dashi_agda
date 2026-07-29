module DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering

------------------------------------------------------------------------
-- Primary provenance.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Roberto Fernández and Aldo Procacci,
-- "Cluster Expansion for Abstract Polymer Models. New Bounds from an Old
-- Approach", Communications in Mathematical Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2; arXiv:math-ph/0605041.
--
-- The primary KP hypothesis uses two independent nonnegative weights a and d:
--
--   sum_{gamma' incompatible gamma}
--     exp(a(gamma') + d(gamma')) |Phi(gamma')| <= a(gamma).
--
-- This is not definitionally the same as DASHI's earlier single rooted-shell
-- bound. The bridge below requires an explicit identification of the physical
-- incompatible-neighbourhood sum and its a-budget with that rooted carrier.
------------------------------------------------------------------------

record KoteckyPreissTwoWeightData
    (Polymer Scalar Cluster FiniteVolume : Set) : Set₁ where
  field
    activityNorm aWeight dWeight : Polymer → Scalar
    Incompatible : Polymer → Polymer → Set

    add multiply : Scalar → Scalar → Scalar
    exponential : Scalar → Scalar

    incompatibleWeightedTerm : Polymer → Polymer → Scalar
    incompatibleWeightedTermMeaning : ∀ centre neighbour →
      incompatibleWeightedTerm centre neighbour
      ≡ multiply
          (exponential (add (aWeight neighbour) (dWeight neighbour)))
          (activityNorm neighbour)

    incompatibleWeightedSum : Polymer → Scalar
    incompatibleWeightedSumEnumerationMeaning : ∀ polymer → Set
    LessEqual : Scalar → Scalar → Set

    partitionFunction : FiniteVolume → Scalar
    Nonzero : Scalar → Set

    clusterFunctional : Cluster → Scalar
    ClusterTouches : Cluster → Polymer → Set
    clusterDWeight : Cluster → Scalar
    clusterWeightedSum : Polymer → Scalar

    logarithm : Scalar → Scalar
    clusterExpansionSum : FiniteVolume → Scalar

open KoteckyPreissTwoWeightData public

KoteckyPreissTwoWeightCondition :
  ∀ {Polymer Scalar Cluster FiniteVolume} →
  KoteckyPreissTwoWeightData Polymer Scalar Cluster FiniteVolume → Set
KoteckyPreissTwoWeightCondition dataSet = ∀ polymer →
  LessEqual dataSet
    (incompatibleWeightedSum dataSet polymer)
    (aWeight dataSet polymer)

record KoteckyPreissTwoWeightConclusion
    {Polymer Scalar Cluster FiniteVolume}
    (dataSet : KoteckyPreissTwoWeightData
      Polymer Scalar Cluster FiniteVolume) : Set₁ where
  field
    finitePartitionNonzero : ∀ volume →
      Nonzero dataSet (partitionFunction dataSet volume)

    logarithmClusterExpansion : ∀ volume →
      logarithm dataSet (partitionFunction dataSet volume)
      ≡ clusterExpansionSum dataSet volume

    truncatedClusterDecay : ∀ polymer →
      LessEqual dataSet
        (clusterWeightedSum dataSet polymer)
        (aWeight dataSet polymer)

open KoteckyPreissTwoWeightConclusion public

record PublishedKoteckyPreissTwoWeightTheorem
    {Polymer Scalar Cluster FiniteVolume}
    (dataSet : KoteckyPreissTwoWeightData
      Polymer Scalar Cluster FiniteVolume) : Set₁ where
  field
    conclusionFromCondition :
      KoteckyPreissTwoWeightCondition dataSet →
      KoteckyPreissTwoWeightConclusion dataSet

open PublishedKoteckyPreissTwoWeightTheorem public

record RootedTerminalToTwoWeightKPIdentification
    {Polymer Link Scalar Cluster FiniteVolume}
    (terminal : Clustering.TerminalKPSmallness Polymer Link Scalar)
    (kp : KoteckyPreissTwoWeightData
      Polymer Scalar Cluster FiniteVolume) : Set₁ where
  field
    anchor : Polymer → Link

    incompatibleWeightedSumMeaning : ∀ polymer →
      incompatibleWeightedSum kp polymer
      ≡ Clustering.rootedWeightedSum terminal (anchor polymer)

    aBudgetMeaning : ∀ polymer →
      aWeight kp polymer
      ≡ Clustering.terminalKPBound terminal (anchor polymer)

    orderMeaning : ∀ {left right} →
      Clustering.LessEqual terminal left right →
      LessEqual kp left right

open RootedTerminalToTwoWeightKPIdentification public

rootedTerminalImpliesExactTwoWeightCondition :
  ∀ {Polymer Link Scalar Cluster FiniteVolume}
    {terminal : Clustering.TerminalKPSmallness Polymer Link Scalar}
    {kp : KoteckyPreissTwoWeightData
      Polymer Scalar Cluster FiniteVolume} →
  RootedTerminalToTwoWeightKPIdentification terminal kp →
  KoteckyPreissTwoWeightCondition kp
rootedTerminalImpliesExactTwoWeightCondition
  {terminal = terminal} {kp = kp} identification polymer =
  subst
    (λ lower → LessEqual kp lower (aWeight kp polymer))
    (sym (incompatibleWeightedSumMeaning identification polymer))
    (subst
      (λ upper → LessEqual kp
        (Clustering.rootedWeightedSum terminal
          (anchor identification polymer)) upper)
      (sym (aBudgetMeaning identification polymer))
      (orderMeaning identification
        (Clustering.terminalKPSmall terminal
          (anchor identification polymer))))

rootedTerminalPublishedKPConclusion :
  ∀ {Polymer Link Scalar Cluster FiniteVolume}
    {terminal : Clustering.TerminalKPSmallness Polymer Link Scalar}
    {kp : KoteckyPreissTwoWeightData
      Polymer Scalar Cluster FiniteVolume} →
  RootedTerminalToTwoWeightKPIdentification terminal kp →
  PublishedKoteckyPreissTwoWeightTheorem kp →
  KoteckyPreissTwoWeightConclusion kp
rootedTerminalPublishedKPConclusion identification theorem =
  conclusionFromCondition theorem
    (rootedTerminalImpliesExactTwoWeightCondition identification)

koteckyPreissPrimaryStatementLevel : ProofLevel
koteckyPreissPrimaryStatementLevel = standardImported

rootedTerminalToTwoWeightKPAssemblyLevel : ProofLevel
rootedTerminalToTwoWeightKPAssemblyLevel = machineChecked

physicalTerminalIncompatibilitySumMeaningInputsLevel : ProofLevel
physicalTerminalIncompatibilitySumMeaningInputsLevel = conditional

physicalTerminalAAndDWeightMeaningInputsLevel : ProofLevel
physicalTerminalAAndDWeightMeaningInputsLevel = conditional

physicalFernandezProcacciDirectCriterionInputsLevel : ProofLevel
physicalFernandezProcacciDirectCriterionInputsLevel = conditional
