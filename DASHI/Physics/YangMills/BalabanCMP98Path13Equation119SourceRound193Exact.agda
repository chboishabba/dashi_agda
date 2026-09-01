{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13Equation119SourceRound193Exact where

------------------------------------------------------------------------
-- ROUND193 A1 BIDI: DELETE THE GENERIC-n REALIZATION SOCKET AT THE ACTUAL
-- PATH13 SOURCE SCALE.
--
-- R192 constructs the literal side-13 periodic realization from the already-
-- owned L=13 physical background.  R182 still exposes caller-selectable
-- realization data; at the Path13 specialization that is redundant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Path13
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192

record Path13Equation119SourceData
    (C : R146.SignedAdditiveOperatorCarrier) : Set₁ where
  field
    background : Path13.RationalSU2Background13

    bondComponent :
      Nat → R126.Vector (R146.additive C) →
      Blocks.PeriodicBlock Side13.side13 → Word.SignedAxis4 →
      R126.Vector (R146.additive C)

    adjointLink :
      Nat → SU2.RationalUnitQuaternion → R126.Operator (R146.additive C)

    scaleV : ℚ → R126.Operator (R146.additive C)
    qSource : Nat → R126.Operator (R146.additive C)

    minusEmbedding :
      Nat → Embed.CenteredPeriodicNoWrapEmbedding
        Side13.side13 R158.sourceRadius

    coarseBond : Nat → Torus.PositiveBond Side13.side13

open Path13Equation119SourceData public

path13RealizationAt :
  ∀ {C} → Path13Equation119SourceData C →
  Nat → Bond.PeriodicBondGaugeRealization
    Side13.side13 SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
path13RealizationAt source _ =
  R192.path13PhysicalPeriodicRealization (background source)

asPositiveCoarseBondEquation119Source :
  ∀ {C} → Path13Equation119SourceData C →
  R182.PositiveCoarseBondEquation119Source
    C Side13.side13 Side13.side13
    SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
asPositiveCoarseBondEquation119Source source = record
  { R182.PositiveCoarseBondEquation119Source.realization =
      path13RealizationAt source
  ; R182.PositiveCoarseBondEquation119Source.bondComponent =
      bondComponent source
  ; R182.PositiveCoarseBondEquation119Source.adjointLink =
      adjointLink source
  ; R182.PositiveCoarseBondEquation119Source.scaleV = scaleV source
  ; R182.PositiveCoarseBondEquation119Source.qSource = qSource source
  ; R182.PositiveCoarseBondEquation119Source.minusEmbedding =
      minusEmbedding source
  ; R182.PositiveCoarseBondEquation119Source.coarseBond = coarseBond source
  }

path13SourceRealizationIsPhysical :
  ∀ {C} (source : Path13Equation119SourceData C) step →
  R182.realization (asPositiveCoarseBondEquation119Source source) step
  ≡ R192.path13PhysicalPeriodicRealization (background source)
path13SourceRealizationIsPhysical source step = refl

path13CanonicalPeriodicSideIs13 :
  Side13.side13 ≡ 13
path13CanonicalPeriodicSideIs13 = refl

cmp98Path13Equation119SourceRound193Level : ProofLevel
cmp98Path13Equation119SourceRound193Level = machineChecked

cmp98Path13RealizationDerivedRound193Level : ProofLevel
cmp98Path13RealizationDerivedRound193Level = machineChecked

literalCMP98Path13OperatorSourceSemanticsRound193Level : ProofLevel
literalCMP98Path13OperatorSourceSemanticsRound193Level = conditional

literalCMP98Path13SelectedBackgroundCutWeldRound193Level : ProofLevel
literalCMP98Path13SelectedBackgroundCutWeldRound193Level = conditional
