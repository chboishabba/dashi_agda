{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonPhysicalPolymerIdentificationExact where

------------------------------------------------------------------------
-- H1/W1 same-object kernel: literal affine Wilson marking is the physical
-- terminal polymer gas used by the exact two-weight KP theorem.
--
-- This sits strictly below PhysicalTerminalTwoWeightKPPackage.  In particular,
-- the caller does NOT supply RootedTerminalToTwoWeightKPIdentification.
-- Instead it supplies the concrete same-carrier equalities from which that
-- identification is assembled.
--
-- Carrier/orientation discipline:
--   * one Polymer carrier;
--   * one terminal rooted-shell package;
--   * one KP datum on that same Polymer carrier;
--   * one literal affine two-Wilson mark on that same Polymer carrier;
--   * one anchor Polymer -> Link;
--   * the exact rooted weighted sum and a-budget equalities.
--
-- The incompatibility relation is retained explicitly in both directions even
-- though the current RootedTerminalToTwoWeightKPIdentification ABI only
-- consumes the already-enumerated incompatibleWeightedSum.  This makes the
-- physical/KP same-object seam auditable rather than silently quotienting it
-- away.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; ∣_∣)

import DASHI.Physics.YangMills.BalabanClayT5PublishedTerminalCriterionReuseExact as Terminal
import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering
import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalTwoWeightKoteckyPreissExact as PhysicalKP
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonAffineMarkedActivityExact as AffineMark
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP

record LiteralTwoWilsonPhysicalPolymerIdentification
    (Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set)
    (PhysicalIncompatible : Polymer → Polymer → Set)
    : Set₁ where
  field
    physicalTerminal :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link

    kpData :
      KP.KoteckyPreissTwoWeightData Polymer ℚ Cluster FiniteVolume

    publishedKP :
      KP.PublishedKoteckyPreissTwoWeightTheorem kpData

    affineMark :
      AffineMark.LiteralTwoWilsonAffinePolymerMark Polymer

    anchor : Polymer → Link

    --------------------------------------------------------------------
    -- Literal affine activity = the activity carried by this physical gas.
    --------------------------------------------------------------------
    literalMarkedActivity : Polymer → ℚ

    literalMarkedActivityIsAffinePhysicalActivity :
      ∀ polymer →
      literalMarkedActivity polymer
      ≡
      AffineMark.baseActivity affineMark polymer
        * AffineMark.literalAffineMultiplier affineMark polymer

    baseActivityIsTerminalActivityNorm :
      ∀ polymer →
      AffineMark.baseActivity affineMark polymer
      ≡ Terminal.activityNorm physicalTerminal polymer

    kpActivityNormIsLiteralMarkedActivityNorm :
      ∀ polymer →
      KP.activityNorm kpData polymer
      ≡ AffineMark.literalMarkedActivityNorm affineMark polymer

    --------------------------------------------------------------------
    -- Same physical incompatibility relation.
    --------------------------------------------------------------------
    kpIncompatibilityIsPhysical :
      ∀ left right →
      KP.Incompatible kpData left right →
      PhysicalIncompatible left right

    physicalIncompatibilityIsKP :
      ∀ left right →
      PhysicalIncompatible left right →
      KP.Incompatible kpData left right

    --------------------------------------------------------------------
    -- Exact terminal/KP weighted-sum and budget weld.
    --------------------------------------------------------------------
    incompatibleWeightedSumIsTerminalRootedSum :
      ∀ polymer →
      KP.incompatibleWeightedSum kpData polymer
      ≡
      Terminal.physicalRootedWeightedSum
        physicalTerminal
        (anchor polymer)

    aWeightIsTerminalBudget :
      ∀ polymer →
      KP.aWeight kpData polymer
      ≡
      Clustering.terminalKPBound
        (Terminal.asTerminalKPSmallness physicalTerminal)
        (anchor polymer)

    rationalOrderToKP :
      ∀ {left right : ℚ} →
      left ≤ right →
      KP.LessEqual kpData left right

open LiteralTwoWilsonPhysicalPolymerIdentification public

twoWeightMeaningFromLiteralPhysicalIdentification :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    (source :
      LiteralTwoWilsonPhysicalPolymerIdentification
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible) →
  KP.RootedTerminalToTwoWeightKPIdentification
    (Terminal.asTerminalKPSmallness (physicalTerminal source))
    (kpData source)
twoWeightMeaningFromLiteralPhysicalIdentification source = record
  { KP.RootedTerminalToTwoWeightKPIdentification.anchor =
      anchor source
  ; KP.RootedTerminalToTwoWeightKPIdentification.incompatibleWeightedSumMeaning =
      incompatibleWeightedSumIsTerminalRootedSum source
  ; KP.RootedTerminalToTwoWeightKPIdentification.aBudgetMeaning =
      aWeightIsTerminalBudget source
  ; KP.RootedTerminalToTwoWeightKPIdentification.orderMeaning =
      rationalOrderToKP source
  }

asPhysicalTerminalTwoWeightKPPackage :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible} →
  LiteralTwoWilsonPhysicalPolymerIdentification
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible →
  PhysicalKP.PhysicalTerminalTwoWeightKPPackage
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
asPhysicalTerminalTwoWeightKPPackage source = record
  { PhysicalKP.PhysicalTerminalTwoWeightKPPackage.physicalRootedIdentification =
      physicalTerminal source
  ; PhysicalKP.PhysicalTerminalTwoWeightKPPackage.kpData =
      kpData source
  ; PhysicalKP.PhysicalTerminalTwoWeightKPPackage.twoWeightMeaning =
      twoWeightMeaningFromLiteralPhysicalIdentification source
  ; PhysicalKP.PhysicalTerminalTwoWeightKPPackage.publishedKP =
      publishedKP source
  }

literalPhysicalKPCondition :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    (source :
      LiteralTwoWilsonPhysicalPolymerIdentification
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible) →
  KP.KoteckyPreissTwoWeightCondition (kpData source)
literalPhysicalKPCondition source =
  PhysicalKP.physicalTerminalTwoWeightKPCondition
    (asPhysicalTerminalTwoWeightKPPackage source)

literalPhysicalMarkedActivityBelowFPThreshold :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    (source :
      LiteralTwoWilsonPhysicalPolymerIdentification
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible)
    polymer →
  AffineMark.literalMarkedActivityNorm (affineMark source) polymer
  ≤
  FP.rhoFPMax
literalPhysicalMarkedActivityBelowFPThreshold source =
  AffineMark.literalMarkedActivityBelowFPThreshold (affineMark source)

literalPhysicalKPActivityBelowFPThreshold :
  ∀ {Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    (source :
      LiteralTwoWilsonPhysicalPolymerIdentification
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible)
    polymer →
  KP.activityNorm (kpData source) polymer ≤ FP.rhoFPMax
literalPhysicalKPActivityBelowFPThreshold source polymer
  rewrite kpActivityNormIsLiteralMarkedActivityNorm source polymer =
  literalPhysicalMarkedActivityBelowFPThreshold source polymer
