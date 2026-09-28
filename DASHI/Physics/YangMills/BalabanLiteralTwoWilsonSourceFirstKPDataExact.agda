{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonSourceFirstKPDataExact where

------------------------------------------------------------------------
-- H1-A max-cut: construct the exact two-weight KP datum directly from the
-- literal affine-marked terminal polymer gas.
--
-- The identity-sensitive fields are DEFINITIONAL:
--
--   activityNorm            = literalMarkedActivityNorm
--   Incompatible            = PhysicalIncompatible
--   incompatibleWeightedSum = physicalRootedWeightedSum ∘ anchor
--   aWeight                 = terminalKPBound ∘ anchor
--   LessEqual               = rational ≤
--
-- Hence no independently selected surrogate needs a later same-object weld.
--
-- Important ABI correction: KP.incompatibleWeightedSumEnumerationMeaning is
-- merely Set-valued.  It is not itself a proof.  We therefore retain an actual
-- incompatible-neighbour enumeration and an equality proof
--
--   sum weightedTerm neighbours = physicalRootedWeightedSum(anchor polymer)
--
-- as source mathematics below.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering
import DASHI.Physics.YangMills.BalabanClayT5PublishedTerminalCriterionReuseExact as Terminal
import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonAffineMarkedActivityExact as AffineMark
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonAffineSourceBoundExact as Affine
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonPhysicalPolymerIdentificationExact as Identification

record LiteralTerminalKPAnalyticData
    (Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set)
    (PhysicalIncompatible : Polymer → Polymer → Set)
    (physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link)
    (anchor : Polymer → Link)
    : Set₁ where
  field
    --------------------------------------------------------------------
    -- Literal Wilson marking data.  The base activity is NOT a free field:
    -- the constructor below sets it to the terminal physical activityNorm.
    --------------------------------------------------------------------
    baseActivityNonnegative :
      ∀ polymer →
      ℚ.0ℚ ≤ Terminal.activityNorm physicalTerminal polymer

    baseActivityBelowOneSixteenth :
      ∀ polymer →
      Terminal.activityNorm physicalTerminal polymer
      ≤ DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact.rhoBase

    leftWilsonValue rightWilsonValue : Polymer → ℚ
    leftWilsonUnitBound :
      ∀ polymer → ℚ.∣ leftWilsonValue polymer ∣ ≤ ℚ.1ℚ
    rightWilsonUnitBound :
      ∀ polymer → ℚ.∣ rightWilsonValue polymer ∣ ≤ ℚ.1ℚ

    leftSource rightSource : ℚ
    leftSourceInsideRadius : Affine.SourceInsideRadius leftSource
    rightSourceInsideRadius : Affine.SourceInsideRadius rightSource

    --------------------------------------------------------------------
    -- The remaining genuine KP analytic structure.
    --------------------------------------------------------------------
    dWeight : Polymer → ℚ
    add multiply : ℚ → ℚ → ℚ
    exponential : ℚ → ℚ

    incompatibleWeightedTerm : Polymer → Polymer → ℚ
    incompatibleWeightedTermMeaning :
      ∀ centre neighbour →
      incompatibleWeightedTerm centre neighbour
      ≡
      multiply
        (exponential
          (add
            (Clustering.terminalKPBound
              (Terminal.asTerminalKPSmallness physicalTerminal)
              (anchor neighbour))
            (dWeight neighbour)))
        (AffineMark.literalMarkedActivityNorm (literalAffineMark source) neighbour)

    incompatibleNeighbors : Polymer → List Polymer

    --------------------------------------------------------------------
    -- Genuine rooted enumeration theorem.  Unlike the historical
    -- Set-valued ABI label, this is an inhabited equality.
    --------------------------------------------------------------------
    rootedIncompatibleEnumerationExact :
      ∀ polymer →
      TwoMark.sumℚ
        (TwoMark.map
          (incompatibleWeightedTerm polymer)
          (incompatibleNeighbors polymer))
      ≡
      Terminal.physicalRootedWeightedSum
        physicalTerminal
        (anchor polymer)

    partitionFunction : FiniteVolume → ℚ
    Nonzero : ℚ → Set

    clusterFunctional : Cluster → ℚ
    ClusterTouches : Cluster → Polymer → Set
    clusterDWeight : Cluster → ℚ
    clusterWeightedSum : Polymer → ℚ

    logarithm : ℚ → ℚ
    clusterExpansionSum : FiniteVolume → ℚ

    publishedKP :
      KP.PublishedKoteckyPreissTwoWeightTheorem
        (record
          { KP.KoteckyPreissTwoWeightData.activityNorm =
              AffineMark.literalMarkedActivityNorm (literalAffineMark source)
          ; KP.KoteckyPreissTwoWeightData.aWeight =
              λ polymer →
                Clustering.terminalKPBound
                  (Terminal.asTerminalKPSmallness physicalTerminal)
                  (anchor polymer)
          ; KP.KoteckyPreissTwoWeightData.dWeight = dWeight
          ; KP.KoteckyPreissTwoWeightData.Incompatible = PhysicalIncompatible
          ; KP.KoteckyPreissTwoWeightData.add = add
          ; KP.KoteckyPreissTwoWeightData.multiply = multiply
          ; KP.KoteckyPreissTwoWeightData.exponential = exponential
          ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedTerm =
              incompatibleWeightedTerm
          ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedTermMeaning =
              incompatibleWeightedTermMeaning
          ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedSum =
              λ polymer →
                Terminal.physicalRootedWeightedSum
                  physicalTerminal
                  (anchor polymer)
          ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedSumEnumerationMeaning =
              λ polymer →
                TwoMark.sumℚ
                  (TwoMark.map
                    (incompatibleWeightedTerm polymer)
                    (incompatibleNeighbors polymer))
                ≡
                Terminal.physicalRootedWeightedSum
                  physicalTerminal
                  (anchor polymer)
          ; KP.KoteckyPreissTwoWeightData.LessEqual = _≤_
          ; KP.KoteckyPreissTwoWeightData.partitionFunction = partitionFunction
          ; KP.KoteckyPreissTwoWeightData.Nonzero = Nonzero
          ; KP.KoteckyPreissTwoWeightData.clusterFunctional = clusterFunctional
          ; KP.KoteckyPreissTwoWeightData.ClusterTouches = ClusterTouches
          ; KP.KoteckyPreissTwoWeightData.clusterDWeight = clusterDWeight
          ; KP.KoteckyPreissTwoWeightData.clusterWeightedSum = clusterWeightedSum
          ; KP.KoteckyPreissTwoWeightData.logarithm = logarithm
          ; KP.KoteckyPreissTwoWeightData.clusterExpansionSum = clusterExpansionSum
          })

open LiteralTerminalKPAnalyticData public

literalAffineMark :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link} →
  (source :
    LiteralTerminalKPAnalyticData
      Scale ShellVolume Root Polymer Link Cluster FiniteVolume
      PhysicalIncompatible physicalTerminal anchor) →
  AffineMark.LiteralTwoWilsonAffinePolymerMark Polymer
literalAffineMark {physicalTerminal = physicalTerminal} source = record
  { AffineMark.LiteralTwoWilsonAffinePolymerMark.baseActivity =
      Terminal.activityNorm physicalTerminal
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.baseActivityNonnegative =
      baseActivityNonnegative source
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.baseActivityBelowOneSixteenth =
      baseActivityBelowOneSixteenth source
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.leftWilsonValue =
      leftWilsonValue source
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.rightWilsonValue =
      rightWilsonValue source
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.leftWilsonUnitBound =
      leftWilsonUnitBound source
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.rightWilsonUnitBound =
      rightWilsonUnitBound source
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.leftSource =
      leftSource source
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.rightSource =
      rightSource source
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.leftSourceInsideRadius =
      leftSourceInsideRadius source
  ; AffineMark.LiteralTwoWilsonAffinePolymerMark.rightSourceInsideRadius =
      rightSourceInsideRadius source
  }

literalTerminalKPData :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link} →
  LiteralTerminalKPAnalyticData
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible physicalTerminal anchor →
  KP.KoteckyPreissTwoWeightData Polymer ℚ Cluster FiniteVolume
literalTerminalKPData
    {PhysicalIncompatible = PhysicalIncompatible}
    {physicalTerminal = physicalTerminal}
    {anchor = anchor}
    source = record
  { KP.KoteckyPreissTwoWeightData.activityNorm =
      AffineMark.literalMarkedActivityNorm (literalAffineMark source)
  ; KP.KoteckyPreissTwoWeightData.aWeight =
      λ polymer →
        Clustering.terminalKPBound
          (Terminal.asTerminalKPSmallness physicalTerminal)
          (anchor polymer)
  ; KP.KoteckyPreissTwoWeightData.dWeight = dWeight source
  ; KP.KoteckyPreissTwoWeightData.Incompatible = PhysicalIncompatible
  ; KP.KoteckyPreissTwoWeightData.add = add source
  ; KP.KoteckyPreissTwoWeightData.multiply = multiply source
  ; KP.KoteckyPreissTwoWeightData.exponential = exponential source
  ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedTerm =
      incompatibleWeightedTerm source
  ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedTermMeaning =
      incompatibleWeightedTermMeaning source
  ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedSum =
      λ polymer →
        Terminal.physicalRootedWeightedSum
          physicalTerminal
          (anchor polymer)
  ; KP.KoteckyPreissTwoWeightData.incompatibleWeightedSumEnumerationMeaning =
      λ polymer →
        TwoMark.sumℚ
          (TwoMark.map
            (incompatibleWeightedTerm source polymer)
            (incompatibleNeighbors source polymer))
        ≡
        Terminal.physicalRootedWeightedSum
          physicalTerminal
          (anchor polymer)
  ; KP.KoteckyPreissTwoWeightData.LessEqual = _≤_
  ; KP.KoteckyPreissTwoWeightData.partitionFunction = partitionFunction source
  ; KP.KoteckyPreissTwoWeightData.Nonzero = Nonzero source
  ; KP.KoteckyPreissTwoWeightData.clusterFunctional = clusterFunctional source
  ; KP.KoteckyPreissTwoWeightData.ClusterTouches = ClusterTouches source
  ; KP.KoteckyPreissTwoWeightData.clusterDWeight = clusterDWeight source
  ; KP.KoteckyPreissTwoWeightData.clusterWeightedSum = clusterWeightedSum source
  ; KP.KoteckyPreissTwoWeightData.logarithm = logarithm source
  ; KP.KoteckyPreissTwoWeightData.clusterExpansionSum = clusterExpansionSum source
  }

literalTerminalKPActivityNormIsMarkedNorm :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {affineMark :
      AffineMark.LiteralTwoWilsonAffinePolymerMark Polymer}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal affineMark anchor)
    polymer →
  KP.activityNorm (literalTerminalKPData source) polymer
  ≡ AffineMark.literalMarkedActivityNorm (literalAffineMark source) polymer
literalTerminalKPActivityNormIsMarkedNorm source polymer = refl

literalTerminalKPIncompatibilityIsPhysical :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {affineMark :
      AffineMark.LiteralTwoWilsonAffinePolymerMark Polymer}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal affineMark anchor)
    left right →
  KP.Incompatible (literalTerminalKPData source) left right
  ≡ PhysicalIncompatible left right
literalTerminalKPIncompatibilityIsPhysical source left right = refl

literalTerminalKPWeightedSumIsRootedSum :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {affineMark :
      AffineMark.LiteralTwoWilsonAffinePolymerMark Polymer}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal affineMark anchor)
    polymer →
  KP.incompatibleWeightedSum (literalTerminalKPData source) polymer
  ≡
  Terminal.physicalRootedWeightedSum physicalTerminal (anchor polymer)
literalTerminalKPWeightedSumIsRootedSum source polymer = refl

literalTerminalKPAWeightIsTerminalBudget :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {affineMark :
      AffineMark.LiteralTwoWilsonAffinePolymerMark Polymer}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal affineMark anchor)
    polymer →
  KP.aWeight (literalTerminalKPData source) polymer
  ≡
  Clustering.terminalKPBound
    (Terminal.asTerminalKPSmallness physicalTerminal)
    (anchor polymer)
literalTerminalKPAWeightIsTerminalBudget source polymer = refl

literalTerminalKPOrderIsRationalOrder :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {affineMark :
      AffineMark.LiteralTwoWilsonAffinePolymerMark Polymer}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal affineMark anchor)
    {left right : ℚ} →
  KP.LessEqual (literalTerminalKPData source) left right
  ≡ (left ≤ right)
literalTerminalKPOrderIsRationalOrder source = refl

sourceFirstPhysicalPolymerIdentification :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {affineMark :
      AffineMark.LiteralTwoWilsonAffinePolymerMark Polymer}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal affineMark anchor) →
  Identification.LiteralTwoWilsonPhysicalPolymerIdentification
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible
sourceFirstPhysicalPolymerIdentification
    {physicalTerminal = physicalTerminal}
    {anchor = anchor}
    source = record
  { Identification.LiteralTwoWilsonPhysicalPolymerIdentification.physicalTerminal =
      physicalTerminal
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.kpData =
      literalTerminalKPData source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.publishedKP =
      publishedKP source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.affineMark =
      literalAffineMark source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.anchor =
      anchor
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.literalMarkedActivity =
      λ polymer →
        AffineMark.baseActivity (literalAffineMark source) polymer
        * AffineMark.literalAffineMultiplier (literalAffineMark source) polymer
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.literalMarkedActivityIsAffinePhysicalActivity =
      λ polymer → refl
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.baseActivityIsTerminalActivityNorm =
      λ polymer → refl
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.kpActivityNormIsLiteralMarkedActivityNorm =
      literalTerminalKPActivityNormIsMarkedNorm source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.kpIncompatibilityIsPhysical =
      λ left right proof → proof
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.physicalIncompatibilityIsKP =
      λ left right proof → proof
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.incompatibleWeightedSumIsTerminalRootedSum =
      literalTerminalKPWeightedSumIsRootedSum source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.aWeightIsTerminalBudget =
      literalTerminalKPAWeightIsTerminalBudget source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.rationalOrderToKP =
      λ proof → proof
  }
