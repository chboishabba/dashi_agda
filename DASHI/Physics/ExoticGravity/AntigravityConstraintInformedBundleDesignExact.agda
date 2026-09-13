module DASHI.Physics.ExoticGravity.AntigravityConstraintInformedBundleDesignExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityConstraintPruningVsBundlePaymentExact as Pruning
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentSearchHypergraphExact as Hyper

------------------------------------------------------------------------
-- CONSTRAINT-INFORMED BUNDLE DESIGN
--
-- Legacy constraints do not pay current same-apparatus leaves, but they do
-- change what an adequate new experiment must measure/control.  This is a
-- proof-search refinement, not empirical closure.
------------------------------------------------------------------------

data BundleStage : Set where
  sourceGeometryStage : BundleStage
  phaseProbeStage : BundleStage
  ordinaryModelStage : BundleStage
  scalingReplicationStage : BundleStage
  theoryComparisonStage : BundleStage

data DesignObligation : Set where
  exactSameApparatusIdentity : DesignObligation
  actualSuperconductingTransitionReceipt : DesignObligation
  externalProbeBoundToTransition : DesignObligation
  rfInstrumentationBackgroundControl : DesignObligation
  electromagneticMechanicalThermalClosure : DesignObligation
  independentSameApparatusReplication : DesignObligation
  magnitudeBoundCompatibility : DesignObligation

record ConstraintInformedDesignDemand : Set where
  constructor constraint-informed-design-demand
  field
    stage : BundleStage
    obligation : DesignObligation
    sourceConstraint : Pruning.ConstraintPruningReceipt
    designReason : String

open ConstraintInformedDesignDemand public

tajmarTransitionDemand : ConstraintInformedDesignDemand
tajmarTransitionDemand = constraint-informed-design-demand
  phaseProbeStage
  actualSuperconductingTransitionReceipt
  Pruning.tajmarTransitionPruning
  "phase-probe bundle must bind the recorded response to the actual superconducting transition rather than to a generic cryogenic temperature threshold"

nasaRFBackgroundDemand : ConstraintInformedDesignDemand
nasaRFBackgroundDemand = constraint-informed-design-demand
  ordinaryModelStage
  rfInstrumentationBackgroundControl
  Pruning.nasaRFArtifactGuidance
  "ordinary-model closure must include explicit RF pickup/instrumentation controls because the legacy RF-associated anomaly was treated as likely instrumental"

hathawayReplicationDemand : ConstraintInformedDesignDemand
hathawayReplicationDemand = constraint-informed-design-demand
  scalingReplicationStage
  independentSameApparatusReplication
  Pruning.hathawayNullPruning
  "legacy Hathaway replication constrains a historical apparatus family but cannot substitute for independent replication of the exact new apparatus/protocol"

tajmarMagnitudeDemand : ConstraintInformedDesignDemand
tajmarMagnitudeDemand = constraint-informed-design-demand
  theoryComparisonStage
  magnitudeBoundCompatibility
  Pruning.tajmarMagnitudePruning
  "candidate theory comparison must remain compatible with existing large-effect upper-bound constraints in their applicable regime"

------------------------------------------------------------------------
-- Existing candidate information moves are refined by obligations, not replaced.
------------------------------------------------------------------------

record RefinedInformationMove : Set where
  constructor refined-information-move
  field
    baseMove : Hyper.SearchModality
    stage : BundleStage
    obligation : DesignObligation
    refinementReference : String

open RefinedInformationMove public

phaseProbeRefinement : RefinedInformationMove
phaseProbeRefinement = refined-information-move
  Hyper.perturbAndMeasure
  phaseProbeStage
  actualSuperconductingTransitionReceipt
  "cross-Tc move is admissible only with an independently established material transition coordinate"

backgroundRefinement : RefinedInformationMove
backgroundRefinement = refined-information-move
  Hyper.calibrationExperiment
  ordinaryModelStage
  rfInstrumentationBackgroundControl
  "background closure explicitly includes RF/instrumentation pickup controls"

replicationRefinement : RefinedInformationMove
replicationRefinement = refined-information-move
  Hyper.independentReplication
  scalingReplicationStage
  independentSameApparatusReplication
  "replication targets the exact apparatus/protocol carrier produced by the preceding bundles"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record ConstraintInformedBundleBoundary : Set where
  constructor constraint-informed-bundle-boundary
  field
    legacyConstraintMayRefineNewExperimentDesign : Bool
    legacyConstraintAutomaticallyPaysRefinedObligation : Bool
    transitionTemperatureEqualsSuperconductingTransitionByDefault : Bool
    oldReplicationCountsAsReplicationOfNewApparatus : Bool
    artifactHistoryMayRequireExplicitNuisanceControl : Bool
    oldMagnitudeBoundAutomaticallyFalsifiesEveryNewModel : Bool
    refinedDesignAutomaticallyCreatesBundleReceipt : Bool

canonicalConstraintInformedBundleBoundary : ConstraintInformedBundleBoundary
canonicalConstraintInformedBundleBoundary =
  constraint-informed-bundle-boundary
    true false false false true false false
