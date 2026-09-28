{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonSourceFirstPhysicalKPExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _+_; _*_)

import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering
import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP
import DASHI.Physics.YangMills.BalabanClayT5PublishedTerminalCriterionReuseExact as Terminal
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonAffineMarkedActivityExact as Affine
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonPhysicalPolymerIdentificationExact as Identification
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SOURCE-FIRST H1-A CONSTRUCTOR
--
-- Do not select an abstract KP datum and subsequently prove that its physical
-- coordinates agree with the terminal Wilson polymer gas.  Construct the KP
-- datum from those coordinates.
--
-- Definitional fields:
--   activityNorm              = literal marked physical activity norm
--   Incompatible              = physical incompatibility
--   incompatibleWeightedSum   = terminal rooted physical sum ∘ anchor
--   aWeight                   = terminal KP budget ∘ anchor
--   LessEqual                 = rational <=.
--
-- What remains non-definitional is exactly the theorem-side KP structure:
-- the d-weight / exponential weighted-term representation, its actual rooted
-- enumeration, cluster/partition objects, and the published KP theorem.
------------------------------------------------------------------------

record SourceFirstKPAuxiliary
    {Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set}
    (physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link)
    (affineMark : Affine.LiteralTwoWilsonAffinePolymerMark Polymer)
    (anchor : Polymer → Link)
    (PhysicalIncompatible : Polymer → Polymer → Set) : Set₁ where
  field
    dWeight : Polymer → ℚ
    exponential : ℚ → ℚ

    incompatibleWeightedTerm : Polymer → Polymer → ℚ
    incompatibleWeightedTermMeaning : ∀ centre neighbour →
      incompatibleWeightedTerm centre neighbour
      ≡
      exponential
        (Clustering.terminalKPBound
          (Terminal.asTerminalKPSmallness physicalTerminal)
          (anchor neighbour)
        + dWeight neighbour)
      * Affine.literalMarkedActivityNorm affineMark neighbour

    incompatibleWeightedSumEnumerationMeaning : ∀ polymer → Set

    partitionFunction : FiniteVolume → ℚ
    Nonzero : ℚ → Set

    clusterFunctional : Cluster → ℚ
    ClusterTouches : Cluster → Polymer → Set
    clusterDWeight : Cluster → ℚ
    clusterWeightedSum : Polymer → ℚ

    logarithm : ℚ → ℚ
    clusterExpansionSum : FiniteVolume → ℚ

open SourceFirstKPAuxiliary public

sourceFirstKPData :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume}
    {PhysicalIncompatible : Polymer → Polymer → Set}
    (physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link)
    (affineMark : Affine.LiteralTwoWilsonAffinePolymerMark Polymer)
    (anchor : Polymer → Link) →
    SourceFirstKPAuxiliary
      physicalTerminal affineMark anchor PhysicalIncompatible →
  KP.KoteckyPreissTwoWeightData Polymer ℚ Cluster FiniteVolume
sourceFirstKPData {PhysicalIncompatible = PhysicalIncompatible}
    physicalTerminal affineMark anchor auxiliary = record
  { KP.KoteckyPreissTwoWeightData.activityNorm =
      Affine.literalMarkedActivityNorm affineMark
  ; KP.KoteckyPreissTwoWeightData.aWeight =
      λ polymer →
        Clustering.terminalKPBound
          (Terminal.asTerminalKPSmallness physicalTerminal)
          (anchor polymer)
  ; KP.KoteckyPreissTwoWeightData.dWeight = dWeight auxiliary
  ; KP.KoteckyPreissTwoWeightData.Incompatible = PhysicalIncompatible
  ; KP.KoteckyPreissTwoWeightData.add = _+_
  ; KP.KoteckyPreissTwoWeightData.multiply = _*_
  ; KP.KoteckyPreissTwoWeightData.exponential = exponential auxiliary
  ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedTerm =
      incompatibleWeightedTerm auxiliary
  ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedTermMeaning =
      incompatibleWeightedTermMeaning auxiliary
  ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedSum =
      λ polymer → Terminal.physicalRootedWeightedSum physicalTerminal (anchor polymer)
  ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedSumEnumerationMeaning =
      incompatibleWeightedSumEnumerationMeaning auxiliary
  ; KP.KoteckyPreissTwoWeightData.LessEqual = _≤_
  ; KP.KoteckyPreissTwoWeightData.partitionFunction = partitionFunction auxiliary
  ; KP.KoteckyPreissTwoWeightData.Nonzero = Nonzero auxiliary
  ; KP.KoteckyPreissTwoWeightData.clusterFunctional = clusterFunctional auxiliary
  ; KP.KoteckyPreissTwoWeightData.ClusterTouches = ClusterTouches auxiliary
  ; KP.KoteckyPreissTwoWeightData.clusterDWeight = clusterDWeight auxiliary
  ; KP.KoteckyPreissTwoWeightData.clusterWeightedSum = clusterWeightedSum auxiliary
  ; KP.KoteckyPreissTwoWeightData.logarithm = logarithm auxiliary
  ; KP.KoteckyPreissTwoWeightData.clusterExpansionSum = clusterExpansionSum auxiliary
  }

record SourceFirstLiteralTwoWilsonPhysicalKP
    (Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set)
    (PhysicalIncompatible : Polymer → Polymer → Set) : Set₁ where
  field
    physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link

    affineMark : Affine.LiteralTwoWilsonAffinePolymerMark Polymer
    anchor : Polymer → Link

    baseActivityIsTerminalActivityNorm : ∀ polymer →
      Affine.baseActivity affineMark polymer
      ≡ Terminal.activityNorm physicalTerminal polymer

    auxiliary :
      SourceFirstKPAuxiliary
        physicalTerminal affineMark anchor PhysicalIncompatible

    publishedKP :
      KP.PublishedKoteckyPreissTwoWeightTheorem
        (sourceFirstKPData physicalTerminal affineMark anchor auxiliary)

open SourceFirstLiteralTwoWilsonPhysicalKP public

asLiteralPhysicalIdentification :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible} →
  SourceFirstLiteralTwoWilsonPhysicalKP
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible →
  Identification.LiteralTwoWilsonPhysicalPolymerIdentification
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible
asLiteralPhysicalIdentification source = record
  { Identification.LiteralTwoWilsonPhysicalPolymerIdentification.physicalTerminal =
      physicalTerminal source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.kpData =
      sourceFirstKPData
        (physicalTerminal source)
        (affineMark source)
        (anchor source)
        (auxiliary source)
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.publishedKP =
      publishedKP source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.affineMark =
      affineMark source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.anchor =
      anchor source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.literalMarkedActivity =
      λ polymer →
        Affine.baseActivity (affineMark source) polymer
        * Affine.literalAffineMultiplier (affineMark source) polymer
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.literalMarkedActivityIsAffinePhysicalActivity =
      λ _ → refl
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.baseActivityIsTerminalActivityNorm =
      baseActivityIsTerminalActivityNorm source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.kpActivityNormIsLiteralMarkedActivityNorm =
      λ _ → refl
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.kpIncompatibilityIsPhysical =
      λ _ _ witness → witness
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.physicalIncompatibilityIsKP =
      λ _ _ witness → witness
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.incompatibleWeightedSumIsTerminalRootedSum =
      λ _ → refl
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.aWeightIsTerminalBudget =
      λ _ → refl
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.rationalOrderToKP =
      λ order → order
  }

sourceFirstPhysicalKPCoreIsDefinitional : Bool
sourceFirstPhysicalKPCoreIsDefinitional = true

independentKPDatumSelectionRequired : Bool
independentKPDatumSelectionRequired = false

sourceFirstPhysicalKPCompilerLevel : ProofLevel
sourceFirstPhysicalKPCompilerLevel = machineChecked

sourceFirstWeightedNeighbourEnumerationLevel : ProofLevel
sourceFirstWeightedNeighbourEnumerationLevel = conditional
