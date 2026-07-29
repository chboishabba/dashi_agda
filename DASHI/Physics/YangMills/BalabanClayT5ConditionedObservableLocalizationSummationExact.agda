module DASHI.Physics.YangMills.BalabanClayT5ConditionedObservableLocalizationSummationExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- The finite-shell argument below is independent of the physical source of the
-- conditioned observable. The hard input is an exact local expansion whose
-- shell norms have a uniform exponentially summable majorant.
------------------------------------------------------------------------

record FiniteLocalizationAlgebra
    (Observable LocalTerm Region Bound : Set) : Set₁ where
  field
    zeroBound : Bound
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    conditioned : Observable → Observable
    regionAtDepth : Observable → Nat → Region
    localTermAtDepth : Observable → Nat → LocalTerm
    localTermNorm localizationDecay : Observable → Nat → Bound

    localizationExpansionExact : ∀ observable cutoff → Set

    localTermNormMeaning : ∀ observable depth → Set

    localTermExponentiallyLocalized : ∀ observable depth →
      LessEqual (localTermNorm observable depth)
        (localizationDecay observable depth)

open FiniteLocalizationAlgebra public

sumThrough :
  ∀ {Observable LocalTerm Region Bound} →
  FiniteLocalizationAlgebra Observable LocalTerm Region Bound →
  Nat → (Nat → Bound) → Bound
sumThrough dataSet zero terms = terms zero
sumThrough dataSet (suc cutoff) terms =
  add dataSet (sumThrough dataSet cutoff terms) (terms (suc cutoff))

localNormSumBelowDecaySum :
  ∀ {Observable LocalTerm Region Bound}
    (dataSet : FiniteLocalizationAlgebra Observable LocalTerm Region Bound)
    observable cutoff →
  LessEqual dataSet
    (sumThrough dataSet cutoff (localTermNorm dataSet observable))
    (sumThrough dataSet cutoff (localizationDecay dataSet observable))
localNormSumBelowDecaySum dataSet observable zero =
  localTermExponentiallyLocalized dataSet observable zero
localNormSumBelowDecaySum dataSet observable (suc cutoff) =
  addMonotone dataSet
    (localNormSumBelowDecaySum dataSet observable cutoff)
    (localTermExponentiallyLocalized dataSet observable (suc cutoff))

record ConditionedObservableTailMajorant
    {Observable LocalTerm Region Bound : Set}
    (dataSet : FiniteLocalizationAlgebra
      Observable LocalTerm Region Bound) : Set₁ where
  field
    cutoff : Observable → Nat
    conditionedTailNorm localizationTailBound : Observable → Bound

    conditionedTailBelowLocalNormSum : ∀ observable →
      LessEqual dataSet
        (conditionedTailNorm observable)
        (sumThrough dataSet (cutoff observable)
          (localTermNorm dataSet observable))

    finiteDecaySumBelowTailBound : ∀ observable →
      LessEqual dataSet
        (sumThrough dataSet (cutoff observable)
          (localizationDecay dataSet observable))
        (localizationTailBound observable)

open ConditionedObservableTailMajorant public

conditionedTailExponentiallyLocalized :
  ∀ {Observable LocalTerm Region Bound}
    {dataSet : FiniteLocalizationAlgebra
      Observable LocalTerm Region Bound} →
  (majorant : ConditionedObservableTailMajorant dataSet) →
  ∀ observable →
  LessEqual dataSet
    (conditionedTailNorm majorant observable)
    (localizationTailBound majorant observable)
conditionedTailExponentiallyLocalized {dataSet = dataSet} majorant observable =
  transitive dataSet
    (conditionedTailBelowLocalNormSum majorant observable)
    (transitive dataSet
      (localNormSumBelowDecaySum dataSet observable
        (cutoff majorant observable))
      (finiteDecaySumBelowTailBound majorant observable))

record ConditionedObservableLocalizationMeaning
    {Observable LocalTerm Region Bound : Set}
    (dataSet : FiniteLocalizationAlgebra
      Observable LocalTerm Region Bound) : Set₁ where
  field
    regionOf : Observable → Region → Nat
    localTerms : Observable → Region → LocalTerm
    localTermNormByRegion localizationDecayByRegion :
      Observable → Region → Bound

    localTermsMeaning : ∀ observable region →
      localTerms observable region
      ≡ localTermAtDepth dataSet observable (regionOf observable region)

    localTermNormRegionMeaning : ∀ observable region →
      localTermNormByRegion observable region
      ≡ localTermNorm dataSet observable (regionOf observable region)

    localizationDecayRegionMeaning : ∀ observable region →
      localizationDecayByRegion observable region
      ≡ localizationDecay dataSet observable (regionOf observable region)

open ConditionedObservableLocalizationMeaning public

asConditionedObservableLocalization :
  ∀ {Observable LocalTerm Region Bound}
    {dataSet : FiniteLocalizationAlgebra
      Observable LocalTerm Region Bound} →
  ConditionedObservableLocalizationMeaning dataSet →
  Clustering.ConditionedObservableLocalization
    Observable LocalTerm Region Bound
asConditionedObservableLocalization {dataSet = dataSet} meaning = record
  { Clustering.ConditionedObservableLocalization.conditioned =
      conditioned dataSet
  ; Clustering.ConditionedObservableLocalization.localTerms =
      localTerms meaning
  ; Clustering.ConditionedObservableLocalization.localTermNorm =
      localTermNormByRegion meaning
  ; Clustering.ConditionedObservableLocalization.localizationDecay =
      localizationDecayByRegion meaning
  ; Clustering.ConditionedObservableLocalization.LessEqual =
      LessEqual dataSet
  ; Clustering.ConditionedObservableLocalization.localizationExpansionExact =
      λ observable → localizationExpansionExact dataSet observable
        (regionOf meaning observable
          (regionAtDepth dataSet observable zero))
  ; Clustering.ConditionedObservableLocalization.localTermExponentiallyLocalized =
      λ observable region →
        let depth = regionOf meaning observable region
        in Agda.Builtin.Equality.subst
          (λ normValue → LessEqual dataSet normValue
            (localizationDecayByRegion meaning observable region))
          (Agda.Builtin.Equality.sym
            (localTermNormRegionMeaning meaning observable region))
          (Agda.Builtin.Equality.subst
            (λ decayValue → LessEqual dataSet
              (localTermNorm dataSet observable depth) decayValue)
            (Agda.Builtin.Equality.sym
              (localizationDecayRegionMeaning meaning observable region))
            (localTermExponentiallyLocalized dataSet observable depth))
  }

finiteLocalizationSumLevel : ProofLevel
finiteLocalizationSumLevel = machineChecked

conditionedTailLocalizationAssemblyLevel : ProofLevel
conditionedTailLocalizationAssemblyLevel = machineChecked

conditionedObservableLocalizationAdapterLevel : ProofLevel
conditionedObservableLocalizationAdapterLevel = machineChecked

physicalConditionedObservableExpansionInputsLevel : ProofLevel
physicalConditionedObservableExpansionInputsLevel = conditional

physicalLocalizationShellNormInputsLevel : ProofLevel
physicalLocalizationShellNormInputsLevel = conditional

physicalLocalizationInfiniteTailInputsLevel : ProofLevel
physicalLocalizationInfiniteTailInputsLevel = conditional
