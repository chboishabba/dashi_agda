{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13Equation120DerivedQSourceRound216Exact where

------------------------------------------------------------------------
-- ROUND216 BIDI: REMOVE qSource FROM THE PATH13 PHYSICAL INPUT RECORD.
--
-- R193 still asks the caller for a `qSource`, although R215 shows that CMP98
-- (120)+(121) already determines it from the exact R147 path/dexp data.
--
-- This owner starts from precisely the remaining Path13 physical data:
--   background, bond projection, adjoint link action, scalar action,
--   c- embedding, and the selected positive coarse bond,
-- together with the already-owned printed dexp convention.
--
-- To reuse the historical R182/R158/R152/R147 geometry compiler we install a
-- harmless zero qSource placeholder.  Eq. (119) never reads qSource.  R215 then
-- overwrites that placeholder with the Eq. (120) linear form.  Finally we build
-- an ordinary R193 source whose qSource is definitionally the recovered one.
--
-- Thus qSource is no longer an independent Path13 physical authority.
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
      Blocks.PeriodicBlock Side13.side13 → Word.SignedAxis4 →
      R126.Vector (R146.additive C)

    adjointLink :
      Nat → SU2.RationalUnitQuaternion → R126.Operator (R146.additive C)

    scaleV : ℚ → R126.Operator (R146.additive C)

    minusEmbedding :
      Nat → Embed.CenteredPeriodicNoWrapEmbedding
        Side13.side13 R158.sourceRadius

    coarseBond : Nat → Torus.PositiveBond Side13.side13

open Path13Equation120PhysicalSourceData public

zeroQSource :
  ∀ {C : R146.SignedAdditiveOperatorCarrier} →
  Nat → R126.Operator (R146.additive C)
zeroQSource {C} step input = R126.zeroV (R146.additive C)

-- Historical geometry carrier with qSource deliberately set to zero.  This is
-- not a physical claim: the field is only present because the older record was
-- wider than the Eq. (119) computation actually requires.
asPlaceholderPositiveCoarseBondSource :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R182.PositiveCoarseBondEquation119Source
    C Side13.side13 Side13.side13
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
    C Side13.side13 SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
asPlaceholderCanonicalSource source =
  R182.asCanonicalL13Equation119Source
    (asPlaceholderPositiveCoarseBondSource source)

asPlaceholderLeastPrivilegeSource :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R152.LiteralEquation119LeastPrivilegeSource
    C Side13.side13 SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
asPlaceholderLeastPrivilegeSource source =
  R158.asRound152Source (asPlaceholderCanonicalSource source)

placeholderLiteralPathData :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R148.CMP98Equation119DexpConvention
    (R126.Vector (R146.additive C)) →
  R147.LiteralEquation119PathData
    C Side13.side13 SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
placeholderLiteralPathData source convention =
  R152.asLiteralPathData
    (asPlaceholderLeastPrivilegeSource source) convention

recoveredLiteralPathData :
  ∀ {C} →
  Path13Equation120PhysicalSourceData C →
  R148.CMP98Equation119DexpConvention
    (R126.Vector (R146.additive C)) →
  R147.LiteralEquation119PathData
    C Side13.side13 SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
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

-- The physical periodic realization is still exactly R192's Path13 object.
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

cmp98Path13Equation120DerivedQSourceRound216Level : ProofLevel
cmp98Path13Equation120DerivedQSourceRound216Level = machineChecked

cmp98Path13Equation120SamePhysicalRealizationRound216Level : ProofLevel
cmp98Path13Equation120SamePhysicalRealizationRound216Level = machineChecked

-- No independent qSource remains in the new Path13 input type.  The surviving
-- source-facing seam is the same one already isolated by R148/R215: identify
-- the printed Y/Y_x and R0 path semantics with the selected physical cut.
literalCMP98Path13Equation120SelectedSemanticsRound216Level : ProofLevel
literalCMP98Path13Equation120SelectedSemanticsRound216Level = conditional
