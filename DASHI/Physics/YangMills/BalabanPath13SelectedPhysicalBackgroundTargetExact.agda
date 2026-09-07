{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact where

------------------------------------------------------------------------
-- PATH13 SELECTED PHYSICAL BACKGROUND: CONSTRUCTIVE TARGET
--
-- Round218 names one remaining source receipt as
--
--   Path13BackgroundIsSelectedPhysicalBackground.
--
-- Repository archaeology shows that this must not be read as an equality
-- between two already-comparable records.  The existing selected physical
-- background instantiation is specialized to the side-four carrier
-- `Physical.RationalSU2Background4`, whereas the actual Path13 source uses
-- `Path13.RationalSU2Background13` on `PhysicalBlockL 13`.
--
-- Therefore the real target is to instantiate the generic selected variational
-- background bridge DIRECTLY on the Path13 carrier (or provide an equivalent
-- RG transport that produces exactly the same Path13 link object).  This file
-- gives that constructive same-object shape without pretending the side-four
-- fixture can simply be equated to the side-thirteen source.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (PositiveBond; pair)
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Path13
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational

Path13PositiveBond : Set
Path13PositiveBond = PositiveBond Side13.side13

record SelectedPhysicalBackground13Instantiation
    (CoarseField Lie : Set) : Set₁ where
  field
    bridge13 : Selected.SelectedBackgroundVariationalChartBridge
      CoarseField Path13.RationalSU2Background13 Path13PositiveBond
      Lie Q.RationalQuaternion ℚ

    coarse13 : CoarseField

    small13 :
      Variational.CoarseSmallField
        (Selected.variational bridge13) coarse13

    path13Background : Path13.RationalSU2Background13

    selectedBackgroundIsPath13 :
      Selected.selectedBackground bridge13 coarse13 small13
      ≡ path13Background

    selectedBondGroupIsPath13Link : ∀ site axis →
      Selected.selectedBondGroup bridge13 coarse13 small13 (pair site axis)
      ≡ Path13.link path13Background axis site

open SelectedPhysicalBackground13Instantiation public

selectedPath13Background :
  ∀ {CoarseField Lie} →
  SelectedPhysicalBackground13Instantiation CoarseField Lie →
  Path13.RationalSU2Background13
selectedPath13Background = path13Background

selectedPath13BackgroundIsVariationalBackground :
  ∀ {CoarseField Lie}
    (inputs : SelectedPhysicalBackground13Instantiation CoarseField Lie) →
  Selected.selectedBackground
    (bridge13 inputs) (coarse13 inputs) (small13 inputs)
  ≡ selectedPath13Background inputs
selectedPath13BackgroundIsVariationalBackground = selectedBackgroundIsPath13

cmp98Path13SelectedPhysicalBackgroundTargetLevel : ProofLevel
cmp98Path13SelectedPhysicalBackgroundTargetLevel = machineChecked

-- This is the genuine remaining physical producer.  No inhabitant is supplied
-- here: the generic variational/chart theorem must be instantiated on the
-- literal Path13 carrier, or an equivalent scale-transport theorem must produce
-- exactly this same-object data.
literalCMP98Path13SelectedPhysicalBackgroundProducerLevel : ProofLevel
literalCMP98Path13SelectedPhysicalBackgroundProducerLevel = conditional
