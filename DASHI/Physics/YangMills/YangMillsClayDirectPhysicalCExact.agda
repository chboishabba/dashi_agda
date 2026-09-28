{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayDirectPhysicalCExact where

------------------------------------------------------------------------
-- C1--C4 SOURCE-FED CONSTRUCTOR FOR THE LITERAL LOCAL-QFT ENDPOINT.
--
-- Do not accept endpoint OPE/stress predicates independently of their physical
-- source witnesses.  This record fixes:
--
--   C1  one Round109 completed marked stress/curvature family;
--   C2  one physical OPE remainder = shared composite tail object;
--   C3  one coefficient RG recurrence with common UV normalization/mixing;
--   C4  the literal stress is the Round109 completed marked stress.
--
-- The literal semantic predicates are interpretation functions OF those exact
-- witnesses.  Quantitative tail decay and all-depth coefficient matching are
-- compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_)
open import Data.Rational.Base using (ℚ; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as C
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as Both
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature
import DASHI.Physics.YangMills.YangMillsPhysicalOPERemainderSharedTailRound442Exact as R442
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact as OPE
import DASHI.Physics.YangMills.YMClayLevel2OPECoefficientCoordinateWeldExact as CoefficientWeld
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119SameCompletedCompositeStressRound427Exact as R427

record DirectPhysicalCSource
    {C₀ : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C₀}
    (Y : Top.LiteralYangMillsConstruction C₀ S)
    : Set₂ where
  field
    --------------------------------------------------------------------
    -- C1/C4: one completed marked family.
    --------------------------------------------------------------------
    completion :
      ∀ group →
      R109.LiteralSchwingerStressMarkedCompletion Y group

    curvatureFamily :
      ∀ group →
      Curvature.MarkedCurvatureCompositeFamily
        (Top.CurvaturePolynomial C₀)
        (Top.Position C₀)
        (R109.continuityScale (completion group))
        (R109.CompletedState (completion group))
        (Top.LocalOperator C₀)

    curvatureFamilyUsesCompletedState :
      ∀ group polynomial →
      Marked.completedState
        (Curvature.markedSource (curvatureFamily group) polynomial)
      ≡
      Marked.completedState
        (Both.compositeData
          (R109.completedSources (completion group)))

    curvatureCompositeIsLiteralOperator :
      ∀ group polynomial →
      Curvature.localOperator (curvatureFamily group) polynomial
      ≡ Top.curvatureOperator Y group polynomial

    gaugeInvariantLocalObservable :
      ∀ group position →
      Top.IsGaugeInvariantObservable S (Top.localObservable Y group position)
      × Top.IsLocalObservable S (Top.localObservable Y group position) position

    curvatureOperatorCorrespondence :
      ∀ group →
      Top.CurvatureOperatorCorrespondence S group
        (Top.curvatureOperator Y group)

    curvatureOperatorsGaugeInvariant :
      ∀ group polynomial →
      Top.IsGaugeInvariantLocalOperator S
        (Top.curvatureOperator Y group polynomial)

    curvatureOperatorsLocal :
      ∀ group polynomial position →
      Top.IsLocalOperator S
        (Top.curvatureOperator Y group polynomial) position

    --------------------------------------------------------------------
    -- C2: exact physical remainder carrier.
    --------------------------------------------------------------------
    RemainderIndex RemainderScale RemainderVolume RemainderRoot : Set

    remainderSource :
      R442.PhysicalOPERemainderSharedTail
        RemainderIndex RemainderScale RemainderVolume RemainderRoot

    remainderIndex :
      Top.CompactSimpleGroup C₀ →
      Top.LocalOperator C₀ →
      Top.LocalOperator C₀ →
      Top.Position C₀ →
      RemainderIndex

    literalRemainderIsSourceMagnitude :
      ∀ group left right position depth →
      Top.opeRemainder Y group left right position depth
      ≡
      R442.physicalRemainderMagnitude remainderSource
        (remainderIndex group left right position) depth

    remainderWitnessMeansPhysical :
      ∀ group left right position depth →
      Top.opeRemainder Y group left right position depth
      ≡
      R442.physicalRemainderMagnitude remainderSource
        (remainderIndex group left right position) depth →
      R442.physicalRemainderMagnitude remainderSource
        (remainderIndex group left right position) depth
      ≤
      Local.coefficient
        (R442.physicalRemainderMajorant remainderSource
          (remainderIndex group left right position))
      *
      Geo.halfPower depth →
      Top.IsPhysicalOPERemainder S group left right position depth
        (Top.opeRemainder Y group left right position depth)

    --------------------------------------------------------------------
    -- C3: exact one-step coefficient recurrence.
    --------------------------------------------------------------------
    Coefficient RGCoordinate : Set

    coefficientRecurrence :
      ∀ group left right output position →
      OPE.CoefficientRGRecurrence Coefficient

    coefficientWeld :
      ∀ group left right output position →
      CoefficientWeld.OPECoefficientRGCoordinateWeld
        Coefficient RGCoordinate (Top.OPECoefficient C₀)
        (coefficientRecurrence group left right output position)

    coefficientDepth :
      Top.Position C₀ → Nat

    literalCoefficientIsWeldCoordinate :
      ∀ group left right output position →
      Top.opeCoefficient Y group left right output position
      ≡
      CoefficientWeld.literalOPECoefficientAt
        (coefficientWeld group left right output position)
        (coefficientDepth position)

    coefficientMatchingMeansPhysical :
      ∀ group left right output position →
      Top.opeCoefficient Y group left right output position
      ≡
      OPE.project
        (CoefficientWeld.projection
          (coefficientWeld group left right output position))
        (OPE.asymptoticFreedomCoefficient
          (coefficientRecurrence group left right output position)
          (coefficientDepth position)) →
      Top.IsPhysicalOPECoefficient S group left right output position
        (Top.opeCoefficient Y group left right output position)

    coefficientMatchingMeansShortDistanceAF :
      (∀ group left right output position →
        Top.opeCoefficient Y group left right output position
        ≡
        OPE.project
          (CoefficientWeld.projection
            (coefficientWeld group left right output position))
          (OPE.asymptoticFreedomCoefficient
            (coefficientRecurrence group left right output position)
            (coefficientDepth position))) →
      ∀ group →
      Top.HasShortDistanceAsymptoticFreedom S group
        (Top.schwinger Y group)

    --------------------------------------------------------------------
    -- C4 / combined local theorem semantics from the exact completed stress
    -- and the C2/C3 receipts above.
    --------------------------------------------------------------------
    completedStressAndSourcesMeanStressTensorAndOPE :
      (∀ group →
        Marked.continuumComposite
          (R427.stressField
            (completion group))
        ≡ Top.stressTensor Y group) →
      (∀ group left right output position →
        Top.opeCoefficient Y group left right output position
        ≡
        OPE.project
          (CoefficientWeld.projection
            (coefficientWeld group left right output position))
          (OPE.asymptoticFreedomCoefficient
            (coefficientRecurrence group left right output position)
            (coefficientDepth position))) →
      (∀ group left right position depth →
        Top.IsPhysicalOPERemainder S group left right position depth
          (Top.opeRemainder Y group left right position depth)) →
      ∀ group →
      Top.HasStressTensorAndOPE S group
        (Top.schwinger Y group)
        (Top.stressTensor Y group)

open DirectPhysicalCSource public

literalCoefficientMatchesAF :
  ∀ {C₀ S} {Y : Top.LiteralYangMillsConstruction C₀ S}
    (source : DirectPhysicalCSource Y) →
  ∀ group left right output position →
  Top.opeCoefficient Y group left right output position
  ≡
  OPE.project
    (CoefficientWeld.projection
      (coefficientWeld source group left right output position))
    (OPE.asymptoticFreedomCoefficient
      (coefficientRecurrence source group left right output position)
      (coefficientDepth source position))
literalCoefficientMatchesAF source group left right output position =
  trans
    (literalCoefficientIsWeldCoordinate source group left right output position)
    (CoefficientWeld.literalOPECoefficientMatchesProjectedAFAtEveryDepth
      (coefficientWeld source group left right output position)
      (coefficientDepth source position))

allPhysicalRemainders :
  ∀ {C₀ S} {Y : Top.LiteralYangMillsConstruction C₀ S}
    (source : DirectPhysicalCSource Y) →
  ∀ group left right position depth →
  Top.IsPhysicalOPERemainder S group left right position depth
    (Top.opeRemainder Y group left right position depth)
allPhysicalRemainders source group left right position depth =
  remainderWitnessMeansPhysical source group left right position depth
    (literalRemainderIsSourceMagnitude source group left right position depth)
    (R442.physicalOPERemainderModulus
      (remainderSource source)
      (remainderIndex source group left right position)
      depth)

asGoal1CanonicalCSource :
  ∀ {C₀ S} {Y : Top.LiteralYangMillsConstruction C₀ S} →
  DirectPhysicalCSource Y →
  C.Goal1CanonicalCSource Y
asGoal1CanonicalCSource source = record
  { C.Goal1CanonicalCSource.completion =
      completion source
  ; C.Goal1CanonicalCSource.curvatureFamily =
      curvatureFamily source
  ; C.Goal1CanonicalCSource.curvatureFamilyUsesRound109CompletedState =
      curvatureFamilyUsesCompletedState source
  ; C.Goal1CanonicalCSource.curvatureCompositeIsLiteralOperator =
      curvatureCompositeIsLiteralOperator source
  ; C.Goal1CanonicalCSource.gaugeInvariantLocalObservable =
      gaugeInvariantLocalObservable source
  ; C.Goal1CanonicalCSource.curvatureOperatorCorrespondence =
      curvatureOperatorCorrespondence source
  ; C.Goal1CanonicalCSource.curvatureOperatorsGaugeInvariant =
      curvatureOperatorsGaugeInvariant source
  ; C.Goal1CanonicalCSource.curvatureOperatorsLocal =
      curvatureOperatorsLocal source
  ; C.Goal1CanonicalCSource.shortDistanceAsymptoticFreedom =
      coefficientMatchingMeansShortDistanceAF source
        (literalCoefficientMatchesAF source)
  ; C.Goal1CanonicalCSource.stressTensorAndOPE =
      completedStressAndSourcesMeanStressTensorAndOPE source
        (λ group →
          R427.stressFieldIsLiteralClayStress
            (completion source group))
        (literalCoefficientMatchesAF source)
        (allPhysicalRemainders source)
  ; C.Goal1CanonicalCSource.physicalOPECoefficient =
      λ group left right output position →
        coefficientMatchingMeansPhysical source group left right output position
          (literalCoefficientMatchesAF source group left right output position)
  ; C.Goal1CanonicalCSource.physicalOPERemainder =
      allPhysicalRemainders source
  }

directPhysicalCCompilerLevel : ProofLevel
directPhysicalCCompilerLevel = machineChecked

-- The open physical source content is now exactly the marked C1 family,
-- C2 same-tail identity, C3 one-step recurrence/UV identification, and the
-- semantic interpretation of these SAME receipts as the literal local-QFT
-- predicates.  Tail decay and all-depth coefficient equality are compiled.
directPhysicalCInstantiationLevel : ProofLevel
directPhysicalCInstantiationLevel = conditional
