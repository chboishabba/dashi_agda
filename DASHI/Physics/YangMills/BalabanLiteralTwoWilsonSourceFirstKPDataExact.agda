{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonSourceFirstKPDataExact where

------------------------------------------------------------------------
-- H1-A MAX-CUT
--
-- Construct the exact two-weight KP datum directly from the literal
-- affine-marked terminal polymer gas.
--
-- Identity-sensitive fields are DEFINITIONAL:
--
--   activityNorm            = literalMarkedActivityNorm
--   Incompatible            = PhysicalIncompatible
--   incompatibleWeightedSum = physicalRootedWeightedSum ∘ anchor
--   aWeight                 = terminalKPBound ∘ anchor
--   LessEqual               = rational ≤
--
-- Thus the corresponding same-object proofs below are refl.
--
-- KP.incompatibleWeightedSumEnumerationMeaning is only Set-valued in the
-- historical ABI.  It is not a proof.  This owner therefore carries an actual
-- finite incompatible-neighbour enumeration and an inhabited equality theorem
-- separately.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _≤_; ∣_∣; _*_)

import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering
import DASHI.Physics.YangMills.BalabanClayT5PublishedTerminalCriterionReuseExact as Terminal
import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
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
    -- Literal Wilson marking.  The base activity is fixed by construction
    -- to Terminal.activityNorm physicalTerminal.
    --------------------------------------------------------------------
    baseActivityNonnegative :
      ∀ polymer →
      0ℚ ≤ Terminal.activityNorm physicalTerminal polymer

    baseActivityBelowOneSixteenth :
      ∀ polymer →
      Terminal.activityNorm physicalTerminal polymer ≤ FP.rhoBase

    leftWilsonValue rightWilsonValue : Polymer → ℚ
    leftWilsonUnitBound :
      ∀ polymer → ∣ leftWilsonValue polymer ∣ ≤ 1ℚ
    rightWilsonUnitBound :
      ∀ polymer → ∣ rightWilsonValue polymer ∣ ≤ 1ℚ

    leftSource rightSource : ℚ
    leftSourceInsideRadius : Affine.SourceInsideRadius leftSource
    rightSourceInsideRadius : Affine.SourceInsideRadius rightSource

    --------------------------------------------------------------------
    -- Remaining analytic KP structure.
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
        (∣
          (1ℚ
            * Terminal.activityNorm physicalTerminal neighbour)
          ∣)

    incompatibleNeighbors : Polymer → List Polymer

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

open LiteralTerminalKPAnalyticData public

literalAffineMark :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link} →
  LiteralTerminalKPAnalyticData
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible physicalTerminal anchor →
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

literalMarkedActivity :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link} →
  LiteralTerminalKPAnalyticData
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible physicalTerminal anchor →
  Polymer → ℚ
literalMarkedActivity source polymer =
  AffineMark.baseActivity (literalAffineMark source) polymer
  * AffineMark.literalAffineMultiplier (literalAffineMark source) polymer

record LiteralTerminalKPAnalyticMeaning
    {Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set}
    {PhysicalIncompatible : Polymer → Polymer → Set}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    : Set₁ where
  field
    incompatibleWeightedTermExact :
      ∀ centre neighbour →
      incompatibleWeightedTerm source centre neighbour
      ≡
      multiply source
        (exponential source
          (add source
            (Clustering.terminalKPBound
              (Terminal.asTerminalKPSmallness physicalTerminal)
              (anchor neighbour))
            (dWeight source neighbour)))
        (AffineMark.literalMarkedActivityNorm
          (literalAffineMark source)
          neighbour)

open LiteralTerminalKPAnalyticMeaning public

literalTerminalKPData :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    (meaning : LiteralTerminalKPAnalyticMeaning source) →
  KP.KoteckyPreissTwoWeightData Polymer ℚ Cluster FiniteVolume
literalTerminalKPData
    {PhysicalIncompatible = PhysicalIncompatible}
    {physicalTerminal = physicalTerminal}
    {anchor = anchor}
    source meaning = record
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
      incompatibleWeightedTermExact meaning
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

record PublishedLiteralTerminalKP
    {Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set}
    {PhysicalIncompatible : Polymer → Polymer → Set}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    (meaning : LiteralTerminalKPAnalyticMeaning source)
    : Set₁ where
  field
    published :
      KP.PublishedKoteckyPreissTwoWeightTheorem
        (literalTerminalKPData source meaning)

open PublishedLiteralTerminalKP public

literalTerminalKPActivityNormIsMarkedNorm :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    (meaning : LiteralTerminalKPAnalyticMeaning source)
    polymer →
  KP.activityNorm (literalTerminalKPData source meaning) polymer
  ≡ AffineMark.literalMarkedActivityNorm (literalAffineMark source) polymer
literalTerminalKPActivityNormIsMarkedNorm source meaning polymer = refl

literalTerminalKPIncompatibilityIsPhysical :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    (meaning : LiteralTerminalKPAnalyticMeaning source)
    left right →
  KP.Incompatible (literalTerminalKPData source meaning) left right
  ≡ PhysicalIncompatible left right
literalTerminalKPIncompatibilityIsPhysical source meaning left right = refl

literalTerminalKPWeightedSumIsRootedSum :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    (meaning : LiteralTerminalKPAnalyticMeaning source)
    polymer →
  KP.incompatibleWeightedSum (literalTerminalKPData source meaning) polymer
  ≡ Terminal.physicalRootedWeightedSum physicalTerminal (anchor polymer)
literalTerminalKPWeightedSumIsRootedSum source meaning polymer = refl

literalTerminalKPAWeightIsTerminalBudget :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    (meaning : LiteralTerminalKPAnalyticMeaning source)
    polymer →
  KP.aWeight (literalTerminalKPData source meaning) polymer
  ≡
  Clustering.terminalKPBound
    (Terminal.asTerminalKPSmallness physicalTerminal)
    (anchor polymer)
literalTerminalKPAWeightIsTerminalBudget source meaning polymer = refl

literalTerminalKPOrderIsRationalOrder :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    (meaning : LiteralTerminalKPAnalyticMeaning source)
    {left right : ℚ} →
  KP.LessEqual (literalTerminalKPData source meaning) left right
  ≡ (left ≤ right)
literalTerminalKPOrderIsRationalOrder source meaning = refl

sourceFirstPhysicalPolymerIdentification :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    (meaning : LiteralTerminalKPAnalyticMeaning source)
    (theorem : PublishedLiteralTerminalKP source meaning) →
  Identification.LiteralTwoWilsonPhysicalPolymerIdentification
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible
sourceFirstPhysicalPolymerIdentification
    {physicalTerminal = physicalTerminal}
    {anchor = anchor}
    source meaning theorem = record
  { Identification.LiteralTwoWilsonPhysicalPolymerIdentification.physicalTerminal =
      physicalTerminal
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.kpData =
      literalTerminalKPData source meaning
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.publishedKP =
      published theorem
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.affineMark =
      literalAffineMark source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.anchor =
      anchor
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.literalMarkedActivity =
      literalMarkedActivity source
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.literalMarkedActivityIsAffinePhysicalActivity =
      λ polymer → refl
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.baseActivityIsTerminalActivityNorm =
      λ polymer → refl
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.kpActivityNormIsLiteralMarkedActivityNorm =
      literalTerminalKPActivityNormIsMarkedNorm source meaning
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.kpIncompatibilityIsPhysical =
      λ left right proof → proof
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.physicalIncompatibilityIsKP =
      λ left right proof → proof
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.incompatibleWeightedSumIsTerminalRootedSum =
      literalTerminalKPWeightedSumIsRootedSum source meaning
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.aWeightIsTerminalBudget =
      literalTerminalKPAWeightIsTerminalBudget source meaning
  ; Identification.LiteralTwoWilsonPhysicalPolymerIdentification.rationalOrderToKP =
      λ proof → proof
  }

rootedEnumerationTheorem :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    {physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link}
    {anchor : Polymer → Link}
    (source :
      LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible physicalTerminal anchor)
    polymer →
  TwoMark.sumℚ
    (TwoMark.map
      (incompatibleWeightedTerm source polymer)
      (incompatibleNeighbors source polymer))
  ≡
  Terminal.physicalRootedWeightedSum
    physicalTerminal
    (anchor polymer)
rootedEnumerationTheorem source =
  rootedIncompatibleEnumerationExact source
