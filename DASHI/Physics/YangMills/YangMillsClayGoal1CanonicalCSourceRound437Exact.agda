{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact where

------------------------------------------------------------------------
-- C / ROUND437: GOAL-1 LITERAL LOCAL-QFT SOURCE, NO OPTIONAL COMMON-CORE DEBT
--
-- The literal Clay endpoint needs curvature local operators, AF/OPE data and a
-- stress tensor on the same continuum family.  It does NOT require the stronger
-- Q_T = H_OS common-core/essential-self-adjointness theorem.
--
-- This owner therefore couples the actual Round109 same-completed-state source
-- to exactly the semantic fields consumed by ContinuumLocalFieldOPEStressWard.
-- Nuclear completion is downstream from the marked-source data; stress and
-- composite provenance are the SAME completed state by Round109/R427.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as Both
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119SameCompletedCompositeStressRound427Exact as R427

record Goal1CanonicalCSource
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₂ where
  field
    completion :
      ∀ group →
      R109.LiteralSchwingerStressMarkedCompletion Y group

    curvatureFamily :
      ∀ group →
      Curvature.MarkedCurvatureCompositeFamily
        (Top.CurvaturePolynomial C)
        (Top.Position C)
        (R109.continuityScale (completion group))
        (R109.CompletedState (completion group))
        (Top.LocalOperator C)

    curvatureFamilyUsesRound109CompletedState :
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

    shortDistanceAsymptoticFreedom :
      ∀ group →
      Top.HasShortDistanceAsymptoticFreedom S group (Top.schwinger Y group)

    stressTensorAndOPE :
      ∀ group →
      Top.HasStressTensorAndOPE S group
        (Top.schwinger Y group) (Top.stressTensor Y group)

    physicalOPECoefficient :
      ∀ group left right output position →
      Top.IsPhysicalOPECoefficient S group left right output position
        (Top.opeCoefficient Y group left right output position)

    physicalOPERemainder :
      ∀ group left right position depth →
      Top.IsPhysicalOPERemainder S group left right position depth
        (Top.opeRemainder Y group left right position depth)

open Goal1CanonicalCSource public

round109StressIsLiteralStress :
  ∀ {C S Y}
    (source : Goal1CanonicalCSource {C = C} {S = S} Y)
    group →
  Marked.continuumComposite
    (R427.stressField (completion source group))
  ≡ Top.stressTensor Y group
round109StressIsLiteralStress source group =
  R427.stressFieldIsLiteralClayStress (completion source group)

asContinuumLocalFieldOPEStressWard :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  Goal1CanonicalCSource Y →
  Five.ContinuumLocalFieldOPEStressWard Y
asContinuumLocalFieldOPEStressWard source = record
  { Five.ContinuumLocalFieldOPEStressWard.gaugeInvariantLocalObservable =
      gaugeInvariantLocalObservable source
  ; Five.ContinuumLocalFieldOPEStressWard.curvatureOperatorCorrespondence =
      curvatureOperatorCorrespondence source
  ; Five.ContinuumLocalFieldOPEStressWard.curvatureOperatorsGaugeInvariant =
      curvatureOperatorsGaugeInvariant source
  ; Five.ContinuumLocalFieldOPEStressWard.curvatureOperatorsLocal =
      curvatureOperatorsLocal source
  ; Five.ContinuumLocalFieldOPEStressWard.shortDistanceAsymptoticFreedom =
      shortDistanceAsymptoticFreedom source
  ; Five.ContinuumLocalFieldOPEStressWard.stressTensorAndOPE =
      stressTensorAndOPE source
  ; Five.ContinuumLocalFieldOPEStressWard.physicalOPECoefficient =
      physicalOPECoefficient source
  ; Five.ContinuumLocalFieldOPEStressWard.physicalOPERemainder =
      physicalOPERemainder source
  }

round437SameCompletedStateCompilerLevel : ProofLevel
round437SameCompletedStateCompilerLevel =
  R427.round427SameCompletedCompositeStressCompilerLevel

round437LiteralCLocalFieldsCompilerLevel : ProofLevel
round437LiteralCLocalFieldsCompilerLevel = machineChecked

-- Remaining Goal-1 C mathematics is precisely:
-- C1 construct the physical same-completed-state curvature/stress marked family;
-- C2 identify the physical OPE remainder with its marked composite tail;
-- C3 identify literal short-distance coefficients with the same RG/AF coordinate;
-- C4 identify the recovered stress first variation/current with this literal stress.
-- No common-core closure or Q_T = H_OS theorem is required by this constructor.
literalRound437Goal1CSourceLevel : ProofLevel
literalRound437Goal1CSourceLevel = conditional
