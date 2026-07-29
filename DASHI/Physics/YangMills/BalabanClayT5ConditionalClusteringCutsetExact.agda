module DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- R. Kotecky and D. Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Project Euclid stable identifier: euclid:cmp/1104161193.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Secondary locator only, not theorem authority:
-- Lluis Eriksson, "Exponential Clustering and Mass Gap for Four-Dimensional
-- SU(N) Lattice Yang--Mills Theory Via Balaban's Renormalization Group and
-- Multiscale Correlator Decoupling -- a Conditional Clustering Theorem --",
-- ai.viXra:2602.0088v3, no DOI recorded. Version 3 explicitly retags terminal
-- KP smallness as H-KP, conditioned-observable localization as H-LOC and the
-- scale-wise cluster expansion with holes as a decoupling load.
------------------------------------------------------------------------

record TerminalKPSmallness
    (Polymer Link Bound : Set) : Set₁ where
  field
    activityNorm weightedActivity : Polymer → Bound
    Contains : Polymer → Link → Set
    terminalKPBound : Link → Bound
    LessEqual : Bound → Bound → Set

    rootedWeightedSum : Link → Bound
    rootedWeightedSumMeaning : ∀ link → Set
    terminalKPSmall : ∀ link →
      LessEqual (rootedWeightedSum link) (terminalKPBound link)

open TerminalKPSmallness public

record ConditionedObservableLocalization
    (Observable LocalTerm Region Bound : Set) : Set₁ where
  field
    conditioned : Observable → Observable
    localTerms : Observable → Region → LocalTerm
    localTermNorm localizationDecay : Observable → Region → Bound
    LessEqual : Bound → Bound → Set

    localizationExpansionExact : ∀ observable → Set
    localTermExponentiallyLocalized : ∀ observable region →
      LessEqual (localTermNorm observable region)
        (localizationDecay observable region)

open ConditionedObservableLocalization public

record PerScaleCorrelatorDecoupling
    (Observable Bound : Set) : Set₁ where
  field
    covariance : Observable → Observable → Bound
    scaleRemainder : Nat → Observable → Observable → Bound
    scaleDecay : Nat → Observable → Observable → Bound
    LessEqual : Bound → Bound → Set

    singleScaleDecoupling : ∀ scale left right →
      LessEqual (scaleRemainder scale left right)
        (scaleDecay scale left right)

open PerScaleCorrelatorDecoupling public

record ConditionalClusteringAssembly
    (Observable Bound : Set) : Set₁ where
  field
    covariance terminalContribution ultravioletContribution :
      Observable → Observable → Bound
    irClusteringBound uvSummedBound targetClusteringBound :
      Observable → Observable → Bound

    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    multiscaleCovarianceSplit : ∀ left right →
      LessEqual (covariance left right)
        (add (terminalContribution left right)
          (ultravioletContribution left right))

    terminalKPAndLocalizationGiveIR : ∀ left right →
      LessEqual (terminalContribution left right)
        (irClusteringBound left right)

    perScaleDecouplingSumsToUV : ∀ left right →
      LessEqual (ultravioletContribution left right)
        (uvSummedBound left right)

    combineIRAndUVDecay : ∀ left right →
      LessEqual
        (add (irClusteringBound left right) (uvSummedBound left right))
        (targetClusteringBound left right)

open ConditionalClusteringAssembly public

conditionalUniformClustering :
  ∀ {Observable Bound}
    (dataSet : ConditionalClusteringAssembly Observable Bound)
    left right →
  LessEqual dataSet
    (covariance dataSet left right)
    (targetClusteringBound dataSet left right)
conditionalUniformClustering dataSet left right =
  transitive dataSet
    (multiscaleCovarianceSplit dataSet left right)
    (transitive dataSet
      (addMonotone dataSet
        (terminalKPAndLocalizationGiveIR dataSet left right)
        (perScaleDecouplingSumsToUV dataSet left right))
      (combineIRAndUVDecay dataSet left right))

terminalKPCutsetVocabularyLevel : ProofLevel
terminalKPCutsetVocabularyLevel = machineChecked

conditionedObservableLocalizationVocabularyLevel : ProofLevel
conditionedObservableLocalizationVocabularyLevel = machineChecked

perScaleDecouplingVocabularyLevel : ProofLevel
perScaleDecouplingVocabularyLevel = machineChecked

conditionalClusteringAssemblyLevel : ProofLevel
conditionalClusteringAssemblyLevel = machineChecked

terminalKPPrimaryDerivationInputsLevel : ProofLevel
terminalKPPrimaryDerivationInputsLevel = conditional

conditionedObservableLocalizationInputsLevel : ProofLevel
conditionedObservableLocalizationInputsLevel = conditional

perScaleClusterWithHolesInputsLevel : ProofLevel
perScaleClusterWithHolesInputsLevel = conditional
