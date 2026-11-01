{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13Equation120DerivedQSourceRound216Exact where

------------------------------------------------------------------------
-- ROUND216 REPAIR: REMOVE qSource ON THE CORRECT PATH13 HISTORICAL INDEX.
--
-- The old periodic geometry APIs are predecessor-indexed:
--
--   PeriodicBlock n = periodicTorus4Definition (suc n),
--   PeriodicBondField n = BondField (suc n).
--
-- Therefore physical side 13 is represented there by R192.path13PeriodicIndex
-- = 12.  The earlier version passed literal 13 and thereby mixed side-14
-- historical geometry with a side-13 physical background/coarse-bond carrier.
--
-- This repair keeps physical/coarse side 13 while all R147/R152/R158 periodic
-- geometry parameters use the predecessor index 12.  qSource recovery itself
-- is unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact as R148
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP98Path13Equation119SourceRound193Exact as R193
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Path13
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanCMP98Equation120QSourceRecoveryRound215Exact as R215

record Path13Equation120PhysicalSourceData
    (C : R146.SignedAdditiveOperatorCarrier) : Set₁ where
  field
    background : Path13.RationalSU2Background13

    bondComponent :
      Nat → R126.Vector (R146.additive C) →
      Blocks.PeriodicBlock R192.path13PeriodicIndex → Word.SignedAxis4 →
      R126.Vector (R146.additive C)

    adjointLink :
      Nat → SU2.RationalUnitQuaternion → R126.Operator (R146.additive C)

    scaleV : ℚ → R126.Operator (R146.additive C)

    minusEmbedding :
      Nat → Embed.CenteredPeriodicNoWrapEmbedding
        R192.path13PeriodicIndex R158.sourceRadius

    coarseBond : Nat → Torus.PositiveBond Side13.side13

open Path13Equation120PhysicalSourceData public

zeroQSource :
  ∀ {C : R146.SignedAdditiveOperatorCarrier} →
  Nat → R126.Operator (R146.additive C)
zeroQSource {C} step input = R126.zeroV (R146.additive C)

asPlaceholderPositiveCoarseBondSource :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R182.PositiveCoarseBondEquation119Source
    C R192.path13PeriodicIndex Side13.side13
    SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
asPlaceholderPositiveCoarseBondSource source = record
  { R182.PositiveCoarseBondEquation119Source.realization =
      λ _ → R192.path13PhysicalPeriodicRealization (background source)
  ; R182.PositiveCoarseBondEquation119Source.bondComponent = bondComponent source
  ; R182.PositiveCoarseBondEquation119Source.adjointLink = adjointLink source
  ; R182.PositiveCoarseBondEquation119Source.scaleV = scaleV source
  ; R182.PositiveCoarseBondEquation119Source.qSource = zeroQSource
  ; R182.PositiveCoarseBondEquation119Source.minusEmbedding = minusEmbedding source
  ; R182.PositiveCoarseBondEquation119Source.coarseBond = coarseBond source
  }

asPlaceholderCanonicalSource :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R158.CanonicalL13Equation119Source
    C R192.path13PeriodicIndex
    SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
asPlaceholderCanonicalSource source =
  R182.asCanonicalL13Equation119Source
    (asPlaceholderPositiveCoarseBondSource source)

asPlaceholderLeastPrivilegeSource :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R152.LiteralEquation119LeastPrivilegeSource
    C R192.path13PeriodicIndex
    SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
asPlaceholderLeastPrivilegeSource source =
  R158.asRound152Source (asPlaceholderCanonicalSource source)

placeholderLiteralPathData :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R148.CMP98Equation119DexpConvention
    (R126.Vector (R146.additive C)) →
  R147.LiteralEquation119PathData
    C R192.path13PeriodicIndex
    SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
placeholderLiteralPathData source convention =
  R152.asLiteralPathData
    (asPlaceholderLeastPrivilegeSource source) convention

recoveredLiteralPathData :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R148.CMP98Equation119DexpConvention
    (R126.Vector (R146.additive C)) →
  R147.LiteralEquation119PathData
    C R192.path13PeriodicIndex
    SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
recoveredLiteralPathData source convention =
  R215.recoverEquation120QSource
    (placeholderLiteralPathData source convention)

path13Equation120QSource :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R148.CMP98Equation119DexpConvention
    (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
path13Equation120QSource source convention =
  R147.qSource (recoveredLiteralPathData source convention)

asPath13Equation119Source :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R148.CMP98Equation119DexpConvention
    (R126.Vector (R146.additive C)) →
  R193.Path13Equation119SourceData C
asPath13Equation119Source source convention = record
  { R193.Path13Equation119SourceData.background = background source
  ; R193.Path13Equation119SourceData.bondComponent = bondComponent source
  ; R193.Path13Equation119SourceData.adjointLink = adjointLink source
  ; R193.Path13Equation119SourceData.scaleV = scaleV source
  ; R193.Path13Equation119SourceData.qSource =
      path13Equation120QSource source convention
  ; R193.Path13Equation119SourceData.minusEmbedding = minusEmbedding source
  ; R193.Path13Equation119SourceData.coarseBond = coarseBond source
  }

path13QSourceIsRecoveredEquation120 :
  ∀ {C}
    (source : Path13Equation120PhysicalSourceData C)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step input →
  R193.qSource (asPath13Equation119Source source convention) step input
  ≡ R215.equation120LinearQSource
      (placeholderLiteralPathData source convention) step input
path13QSourceIsRecoveredEquation120 source convention step input = refl

path13RecoveredSourceRealizationIsPhysical :
  ∀ {C}
    (source : Path13Equation120PhysicalSourceData C)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step →
  R193.path13RealizationAt
    (asPath13Equation119Source source convention) step
  ≡ R192.path13PhysicalPeriodicRealization (background source)
path13RecoveredSourceRealizationIsPhysical source convention step = refl

path13DerivedQHistoricalIndexIs12 :
  R192.path13PeriodicIndex ≡ 12
path13DerivedQHistoricalIndexIs12 = refl

path13DerivedQPhysicalSideIs13 :
  suc R192.path13PeriodicIndex ≡ Side13.side13
path13DerivedQPhysicalSideIs13 = refl

cmp98Path13DerivedQSourceHistoricalIndexRepairRound216Level : ProofLevel
cmp98Path13DerivedQSourceHistoricalIndexRepairRound216Level = machineChecked

cmp98Path13Equation120DerivedQSourceRound216Level : ProofLevel
cmp98Path13Equation120DerivedQSourceRound216Level = machineChecked

cmp98Path13Equation120SamePhysicalRealizationRound216Level : ProofLevel
cmp98Path13Equation120SamePhysicalRealizationRound216Level = machineChecked

literalCMP98Path13Equation120SelectedSemanticsRound216Level : ProofLevel
literalCMP98Path13Equation120SelectedSemanticsRound216Level = conditional
