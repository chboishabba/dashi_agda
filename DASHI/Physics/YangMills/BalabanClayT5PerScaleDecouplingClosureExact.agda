module DASHI.Physics.YangMills.BalabanClayT5PerScaleDecouplingClosureExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

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
-- DOI: 10.1007/s00220-007-0279-2.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- This module proves the finite multiscale summation logic. The actual cluster
-- expansion with holes at each scale and the uniform tail majorant remain
-- explicit physical inputs. No dummy covariance is introduced by the adapter.
------------------------------------------------------------------------

record FiniteScaleDecouplingData (Observable Bound : Set) : Set₁ where
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

    covariance : Observable → Observable → Bound
    scaleRemainder scaleDecay : Nat → Observable → Observable → Bound
    singleScaleDecoupling : ∀ scale left right →
      LessEqual (scaleRemainder scale left right)
        (scaleDecay scale left right)

open FiniteScaleDecouplingData public

sumThrough :
  ∀ {Observable Bound} →
  FiniteScaleDecouplingData Observable Bound →
  Nat → (Nat → Observable → Observable → Bound) →
  Observable → Observable → Bound
sumThrough dataSet zero terms left right = terms zero left right
sumThrough dataSet (suc cutoff) terms left right =
  add dataSet
    (sumThrough dataSet cutoff terms left right)
    (terms (suc cutoff) left right)

finiteRemainderSumBelowFiniteDecaySum :
  ∀ {Observable Bound}
    (dataSet : FiniteScaleDecouplingData Observable Bound)
    cutoff left right →
  LessEqual dataSet
    (sumThrough dataSet cutoff (scaleRemainder dataSet) left right)
    (sumThrough dataSet cutoff (scaleDecay dataSet) left right)
finiteRemainderSumBelowFiniteDecaySum dataSet zero left right =
  singleScaleDecoupling dataSet zero left right
finiteRemainderSumBelowFiniteDecaySum dataSet (suc cutoff) left right =
  addMonotone dataSet
    (finiteRemainderSumBelowFiniteDecaySum dataSet cutoff left right)
    (singleScaleDecoupling dataSet (suc cutoff) left right)

record UltravioletTailMajorant
    {Observable Bound : Set}
    (dataSet : FiniteScaleDecouplingData Observable Bound) : Set₁ where
  field
    cutoff : Nat
    ultravioletContribution uvSummedBound :
      Observable → Observable → Bound

    ultravioletBelowFiniteRemainderSum : ∀ left right →
      LessEqual dataSet
        (ultravioletContribution left right)
        (sumThrough dataSet cutoff (scaleRemainder dataSet) left right)

    finiteDecaySumBelowUVBound : ∀ left right →
      LessEqual dataSet
        (sumThrough dataSet cutoff (scaleDecay dataSet) left right)
        (uvSummedBound left right)

open UltravioletTailMajorant public

perScaleDecouplingSumsToUV :
  ∀ {Observable Bound}
    {dataSet : FiniteScaleDecouplingData Observable Bound} →
  (majorant : UltravioletTailMajorant dataSet) →
  ∀ left right →
  LessEqual dataSet
    (ultravioletContribution majorant left right)
    (uvSummedBound majorant left right)
perScaleDecouplingSumsToUV {dataSet = dataSet} majorant left right =
  transitive dataSet
    (ultravioletBelowFiniteRemainderSum majorant left right)
    (transitive dataSet
      (finiteRemainderSumBelowFiniteDecaySum dataSet
        (cutoff majorant) left right)
      (finiteDecaySumBelowUVBound majorant left right))

asPerScaleCorrelatorDecoupling :
  ∀ {Observable Bound} →
  FiniteScaleDecouplingData Observable Bound →
  Clustering.PerScaleCorrelatorDecoupling Observable Bound
asPerScaleCorrelatorDecoupling dataSet = record
  { Clustering.PerScaleCorrelatorDecoupling.covariance = covariance dataSet
  ; Clustering.PerScaleCorrelatorDecoupling.scaleRemainder =
      scaleRemainder dataSet
  ; Clustering.PerScaleCorrelatorDecoupling.scaleDecay =
      scaleDecay dataSet
  ; Clustering.PerScaleCorrelatorDecoupling.LessEqual = LessEqual dataSet
  ; Clustering.PerScaleCorrelatorDecoupling.singleScaleDecoupling =
      singleScaleDecoupling dataSet
  }

record ConditionalClusteringFromScaleSums
    (Observable Bound : Set) : Set₁ where
  field
    scaleData : FiniteScaleDecouplingData Observable Bound
    uvMajorant : UltravioletTailMajorant scaleData

    terminalContribution : Observable → Observable → Bound
    irClusteringBound targetClusteringBound : Observable → Observable → Bound

    multiscaleCovarianceSplit : ∀ left right →
      LessEqual scaleData
        (covariance scaleData left right)
        (add scaleData
          (terminalContribution left right)
          (ultravioletContribution uvMajorant left right))

    terminalKPAndLocalizationGiveIR : ∀ left right →
      LessEqual scaleData
        (terminalContribution left right)
        (irClusteringBound left right)

    combineIRAndUVDecay : ∀ left right →
      LessEqual scaleData
        (add scaleData
          (irClusteringBound left right)
          (uvSummedBound uvMajorant left right))
        (targetClusteringBound left right)

open ConditionalClusteringFromScaleSums public

asConditionalClusteringAssembly :
  ∀ {Observable Bound} →
  ConditionalClusteringFromScaleSums Observable Bound →
  Clustering.ConditionalClusteringAssembly Observable Bound
asConditionalClusteringAssembly dataSet = record
  { Clustering.ConditionalClusteringAssembly.covariance =
      covariance (scaleData dataSet)
  ; Clustering.ConditionalClusteringAssembly.terminalContribution =
      terminalContribution dataSet
  ; Clustering.ConditionalClusteringAssembly.ultravioletContribution =
      ultravioletContribution (uvMajorant dataSet)
  ; Clustering.ConditionalClusteringAssembly.irClusteringBound =
      irClusteringBound dataSet
  ; Clustering.ConditionalClusteringAssembly.uvSummedBound =
      uvSummedBound (uvMajorant dataSet)
  ; Clustering.ConditionalClusteringAssembly.targetClusteringBound =
      targetClusteringBound dataSet
  ; Clustering.ConditionalClusteringAssembly.add = add (scaleData dataSet)
  ; Clustering.ConditionalClusteringAssembly.LessEqual =
      LessEqual (scaleData dataSet)
  ; Clustering.ConditionalClusteringAssembly.transitive =
      transitive (scaleData dataSet)
  ; Clustering.ConditionalClusteringAssembly.addMonotone =
      addMonotone (scaleData dataSet)
  ; Clustering.ConditionalClusteringAssembly.multiscaleCovarianceSplit =
      multiscaleCovarianceSplit dataSet
  ; Clustering.ConditionalClusteringAssembly.terminalKPAndLocalizationGiveIR =
      terminalKPAndLocalizationGiveIR dataSet
  ; Clustering.ConditionalClusteringAssembly.perScaleDecouplingSumsToUV =
      perScaleDecouplingSumsToUV (uvMajorant dataSet)
  ; Clustering.ConditionalClusteringAssembly.combineIRAndUVDecay =
      combineIRAndUVDecay dataSet
  }

finiteScaleSumDefinitionLevel : ProofLevel
finiteScaleSumDefinitionLevel = machineChecked

finiteScaleDecouplingSummationLevel : ProofLevel
finiteScaleDecouplingSummationLevel = machineChecked

uvTailMajorantAssemblyLevel : ProofLevel
uvTailMajorantAssemblyLevel = machineChecked

conditionalClusteringFromScaleSumsLevel : ProofLevel
conditionalClusteringFromScaleSumsLevel = machineChecked

physicalPerScaleClusterWithHolesInputsLevel : ProofLevel
physicalPerScaleClusterWithHolesInputsLevel = conditional

physicalUltravioletTailSummabilityInputsLevel : ProofLevel
physicalUltravioletTailSummabilityInputsLevel = conditional

physicalCovarianceScaleSplitInputsLevel : ProofLevel
physicalCovarianceScaleSplitInputsLevel = conditional
