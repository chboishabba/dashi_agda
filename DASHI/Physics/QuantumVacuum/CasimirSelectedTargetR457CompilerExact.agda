module DASHI.Physics.QuantumVacuum.CasimirSelectedTargetR457CompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.GRQFTR457SourceNativeRecoveryBindingExact as R457Binding
import DASHI.Physics.QuantumVacuum.CasimirMinimalR457SourceNativeCompilerExact as Minimal
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as R122
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.BalabanOSLiteralSchwingerWeldRound127Exact as R127
import DASHI.Physics.YangMills.YangMillsClayGoal1SourceNativeContinuumRound457Exact as R457
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- SELECTED qftTarget -> R457, WITHOUT A SECOND LITERAL-Y CONSTRUCTION
--
-- UnifiedCandidate already owns the literal Yang-Mills construction selected at
-- every coarse-grained candidate: qftTarget.  For a Casimir application at one
-- selected candidate/regime, use THAT object directly.  Do not first construct
-- a second pinned/H2 Y and then prove global equality to every selected target.
--
-- Local source payments are attached to
--
--   Y[c,r] = qftTarget (coarseGrain c r).
--
-- QFTRecoveryReceipt already proves recoverQFT(joint[c,r]) = Y[c,r].
------------------------------------------------------------------------

selectedTarget :
  (U : Weld.UnifiedCandidate) →
  Weld.Candidate U → Weld.Regime U →
  Top.LiteralYangMillsConstruction
    (Weld.qftCarriers U) (Weld.qftSemantics U)
selectedTarget U candidate regime =
  Weld.qftTarget U (Weld.coarseGrain U candidate regime)

selectedTargetPrimitiveSourceInputsBuildR457 :
  ∀ {U : Weld.UnifiedCandidate}
    (candidate : Weld.Candidate U)
    (regime : Weld.Regime U)
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate
      (selectedTarget U candidate regime) group}
    (selected : R119.CanonicalMetricSelectedStressWeld
      domain representation coordinate) →
  (densityAnchor : R122.DensityAnchoredCanonicalMetricStress selected) →
  R124.BalabanDensityLiteralFiniteMeasureWeld
    {trajectory = trajectory} {split = split} {inputs = inputs}
    (selectedTarget U candidate regime) group →
  Minimal.MinimalContinuumSchwingerAttachment
    (Weld.qftSemantics U) (selectedTarget U candidate regime) group →
  R127.OSLiteralSchwingerWeld
    (selectedTarget U candidate regime) group →
  let metricLane = Minimal.r114AndR119BuildR120 selected
      stressLane = Minimal.r120AndR122BuildR123 metricLane densityAnchor
  in R457.SourceNativeContinuumAndOS stressLane
selectedTargetPrimitiveSourceInputsBuildR457
    candidate regime selected densityAnchor measureWeld continuum osWeld =
  Minimal.minimalPrimitiveSourceInputsBuildR457
    selected densityAnchor measureWeld continuum osWeld

qftRecoveryDirectlyBuildsSelectedTargetSameObject :
  ∀ {U : Weld.UnifiedCandidate}
    (qftRecovery : Weld.QFTRecoveryReceipt U)
    (candidate : Weld.Candidate U)
    (regime : Weld.Regime U)
    (qftAtRegime : Weld.qftRegime U regime)
    {trajectory split inputs group Scale Volume activity domain representation stressLane}
    (sourceNative : R457.SourceNativeContinuumAndOS
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = selectedTarget U candidate regime} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  R457Binding.R457LegacyRecoverySameObjectAttachment sourceNative
    (Weld.microscopicState U (Weld.coarseGrain U candidate regime))
qftRecoveryDirectlyBuildsSelectedTargetSameObject
    qftRecovery candidate regime qftAtRegime sourceNative = record
  { R457Binding.R457LegacyRecoverySameObjectAttachment.legacyRecoverIsR457LiteralConstruction =
      Weld.qftRecoveryAfterCoarseGrainingCommutes
        qftRecovery candidate regime qftAtRegime
  }

record CasimirSelectedTargetR457Boundary : Set where
  constructor casimir-selected-target-r457-boundary
  field
    selectedTargetPrimitiveSourceInputsBuildR457CompilerOwned : Bool
    qftRecoveryDirectlyBuildsSelectedTargetSameObjectCompilerOwned : Bool
    independentLiteralConstructionProducerRequiredForCasimirR457 : Bool
    cmp119H2RequiredForCasimirR457 : Bool
    round581RequiredForCasimirR457 : Bool
    globalRound131RecoveredQFTAttachmentRequiredForSelectedCasimirR457 : Bool
    selectedTargetContinuumSchwingerAttachmentStillRequired : Bool
    r114R119R122R124R127StillRequired : Bool

open CasimirSelectedTargetR457Boundary public

canonicalSelectedTargetR457Boundary : CasimirSelectedTargetR457Boundary
canonicalSelectedTargetR457Boundary =
  casimir-selected-target-r457-boundary
    true true false false false false true true

casimirSelectedTargetR457Reading : String
casimirSelectedTargetR457Reading =
  "For a selected Casimir candidate/regime, UnifiedCandidate.qftTarget already is the literal Yang-Mills construction Y. R457 should be constructed on that exact Y using R114/R119/R122/R124/R127 plus the selected target's continuum-limit and Schwinger-membership witnesses. QFTRecoveryReceipt then directly proves recoverQFT(joint)=Y. A second pinned/H2 literal construction, Round581 producer, global Round131 attachment, or positive Clay mass-gap theorem is therefore not a mandatory Casimir-local prerequisite; H2/R581 remain valid upstream producer/audit routes when one wants to construct the selected target itself."
