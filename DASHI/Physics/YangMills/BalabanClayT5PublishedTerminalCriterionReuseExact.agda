module DASHI.Physics.YangMills.BalabanClayT5PublishedTerminalCriterionReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as P2
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT2ClusterCriterionComparisonExact as Comparison
import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering

------------------------------------------------------------------------
-- Published criterion provenance.
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
-- Fernández--Procacci improves the admissible convergence region; it does not
-- by itself prove that the physical Yang--Mills terminal activities lie in that
-- region.  The representation/majorant identification remains explicit below.
------------------------------------------------------------------------

record FiniteTerminalRootedShell
    (Scale Volume Root : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root
    terminalDepth : Scale → Volume → Root → Nat

open FiniteTerminalRootedShell public

terminalRootedPartialBelowHalf :
  ∀ {Scale Volume Root}
    (dataSet : FiniteTerminalRootedShell Scale Volume Root)
    scale volume root →
  P2.rootedPartialSum
    (Shell.asUniformRootedShellBound (shellData dataSet))
    scale volume root (terminalDepth dataSet scale volume root)
  ≤ P2.half
terminalRootedPartialBelowHalf dataSet scale volume root =
  Shell.traversalSuppressionImpliesFiniteKP
    (shellData dataSet) scale volume root
    (terminalDepth dataSet scale volume root)

record PhysicalTerminalRootedSumIdentification
    (Scale Volume Root Polymer Link : Set) : Set₁ where
  field
    finiteTerminal : FiniteTerminalRootedShell Scale Volume Root
    selectedScale : Scale
    selectedVolume : Volume
    rootOf : Link → Root

    activityNorm weightedActivity : Polymer → ℚ
    Contains : Polymer → Link → Set

    physicalRootedWeightedSum : Link → ℚ
    physicalRootedWeightedSumMeaning : ∀ link →
      physicalRootedWeightedSum link
      ≡ P2.rootedPartialSum
          (Shell.asUniformRootedShellBound
            (shellData finiteTerminal))
          selectedScale selectedVolume (rootOf link)
          (terminalDepth finiteTerminal
            selectedScale selectedVolume (rootOf link))

open PhysicalTerminalRootedSumIdentification public

physicalTerminalRootedSumBelowHalf :
  ∀ {Scale Volume Root Polymer Link}
    (identification : PhysicalTerminalRootedSumIdentification
      Scale Volume Root Polymer Link)
    link →
  physicalRootedWeightedSum identification link ≤ P2.half
physicalTerminalRootedSumBelowHalf identification link =
  subst
    (λ value → value ≤ P2.half)
    (sym (physicalRootedWeightedSumMeaning identification link))
    (terminalRootedPartialBelowHalf
      (finiteTerminal identification)
      (selectedScale identification)
      (selectedVolume identification)
      (rootOf identification link))

asTerminalKPSmallness :
  ∀ {Scale Volume Root Polymer Link}
    (identification : PhysicalTerminalRootedSumIdentification
      Scale Volume Root Polymer Link) →
  Clustering.TerminalKPSmallness Polymer Link ℚ
asTerminalKPSmallness identification = record
  { Clustering.TerminalKPSmallness.activityNorm =
      activityNorm identification
  ; Clustering.TerminalKPSmallness.weightedActivity =
      weightedActivity identification
  ; Clustering.TerminalKPSmallness.Contains =
      Contains identification
  ; Clustering.TerminalKPSmallness.terminalKPBound = λ _ → P2.half
  ; Clustering.TerminalKPSmallness.LessEqual = _≤_
  ; Clustering.TerminalKPSmallness.rootedWeightedSum =
      physicalRootedWeightedSum identification
  ; Clustering.TerminalKPSmallness.rootedWeightedSumMeaning =
      physicalRootedWeightedSumMeaning identification
  ; Clustering.TerminalKPSmallness.terminalKPSmall =
      physicalTerminalRootedSumBelowHalf identification
  }

data PublishedCriterionWitness
    {Polymer : Set}
    (comparison : Comparison.PolymerCriterionComparison Polymer) : Set₁ where
  byKoteckyPreiss :
    Comparison.KoteckyPreissCriterion comparison →
    PublishedCriterionWitness comparison
  byFernandezProcacci :
    Comparison.FernandezProcacciCriterion comparison →
    PublishedCriterionWitness comparison

asFernandezProcacciCriterion :
  ∀ {Polymer}
    {comparison : Comparison.PolymerCriterionComparison Polymer} →
  PublishedCriterionWitness comparison →
  Comparison.FernandezProcacciCriterion comparison
asFernandezProcacciCriterion {comparison = comparison}
  (byKoteckyPreiss kp) =
  Comparison.koteckyPreissImpliesFernandezProcacci comparison kp
asFernandezProcacciCriterion (byFernandezProcacci fp) = fp

record PhysicalTerminalFPCriterionIdentification
    {Polymer : Set}
    (comparison : Comparison.PolymerCriterionComparison Polymer) : Set₁ where
  field
    publishedWitness : PublishedCriterionWitness comparison
    physicalTerminalActivitiesMatchComparison : Set
    physicalIncompatibilityMatchesComparison : Set

open PhysicalTerminalFPCriterionIdentification public

physicalTerminalPublishedFP :
  ∀ {Polymer}
    {comparison : Comparison.PolymerCriterionComparison Polymer} →
  PhysicalTerminalFPCriterionIdentification comparison →
  Comparison.FernandezProcacciCriterion comparison
physicalTerminalPublishedFP identification =
  asFernandezProcacciCriterion (publishedWitness identification)

finiteTerminalKPReuseLevel : ProofLevel
finiteTerminalKPReuseLevel = machineChecked

physicalTerminalKPSmallnessAssemblyLevel : ProofLevel
physicalTerminalKPSmallnessAssemblyLevel = machineChecked

publishedKPToFernandezProcacciLevel : ProofLevel
publishedKPToFernandezProcacciLevel = machineChecked

publishedFernandezProcacciAlternativeLevel : ProofLevel
publishedFernandezProcacciAlternativeLevel = machineChecked

physicalTerminalRootedSumIdentificationInputsLevel : ProofLevel
physicalTerminalRootedSumIdentificationInputsLevel = conditional

physicalTerminalFPMajorantIdentificationInputsLevel : ProofLevel
physicalTerminalFPMajorantIdentificationInputsLevel = conditional
