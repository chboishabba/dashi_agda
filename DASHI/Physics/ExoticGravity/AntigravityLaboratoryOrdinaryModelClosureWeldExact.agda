module DASHI.Physics.ExoticGravity.AntigravityLaboratoryOrdinaryModelClosureWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as Typed
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryBackgroundClosureExact as Background
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Physics.ExoticGravity.LiTorrStandardGRComparatorBidiExact as Legacy
import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as Evidence
import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as Coupling
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Enhancement

------------------------------------------------------------------------
-- TYPED COMPARATOR CLOSURE <-> EXISTING ORDINARY-MODEL BUNDLE
--
-- Closing the GR comparator is one consumer.  The optimized ordinary-model
-- bundle also owns evidence-background, coupling-ordinary-GR/background, and
-- enhancement-background coordinates.  This weld requires both receipts and
-- exact identity; neither is synthesized from the other.
------------------------------------------------------------------------

record TypedOrdinaryModelClosureWeld
    (prediction : Typed.OrdinaryGRPredictionReceipt) : Set₂ where
  constructor typed-ordinary-model-closure-weld
  field
    typedBackgroundClosure :
      Background.SameApparatusBackgroundClosureReceipt prediction

    optimizedBundle : Plan.OrdinaryModelClosureBundleReceipt

    ComparatorStateIdentityReceipt : Set
    comparatorStateIdentityReceipt : ComparatorStateIdentityReceipt

    ApparatusIdentityReceipt : Set
    apparatusIdentityReceipt : ApparatusIdentityReceipt

    PredictionCarrierIdentityReceipt : Set
    predictionCarrierIdentityReceipt : PredictionCarrierIdentityReceipt

    BackgroundModelIdentityReceipt : Set
    backgroundModelIdentityReceipt : BackgroundModelIdentityReceipt

    comparatorStateMatchesTypedClosure :
      Plan.OrdinaryModelClosureBundleReceipt.comparatorState optimizedBundle
        ≡ Background.closedComparatorState

open TypedOrdinaryModelClosureWeld public

------------------------------------------------------------------------
-- Existing post-ordinary-model frontier, reused exactly.
------------------------------------------------------------------------

postOrdinaryEvidenceFirstOpen :
  Evidence.firstOpenEvidenceLeaf Plan.postOrdinaryEvidenceState
    ≡ Evidence.constitutiveResidualLeaf
postOrdinaryEvidenceFirstOpen = Plan.postOrdinaryEvidenceFirstOpen

postOrdinaryCouplingFirstOpen :
  Coupling.firstOpenAlphaLeaf Plan.postOrdinaryCouplingState
    ≡ Coupling.reproducibilityLeaf
postOrdinaryCouplingFirstOpen = Plan.postOrdinaryCouplingFirstOpen

postOrdinaryComparatorClosed :
  Legacy.firstOpenGRComparatorLeaf Plan.postOrdinaryComparatorState
    ≡ Legacy.comparatorClosed
postOrdinaryComparatorClosed = Plan.postOrdinaryComparatorClosed

postOrdinaryEnhancementFirstOpen :
  Enhancement.firstOpenEnhancementLeaf Plan.postOrdinaryEnhancementState
    ≡ Enhancement.constitutiveRatioLeaf
postOrdinaryEnhancementFirstOpen = Plan.postOrdinaryEnhancementFirstOpen

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record OrdinaryModelClosureWeldBoundary : Set where
  constructor ordinary-model-closure-weld-boundary
  field
    typedComparatorClosureAloneCreatesOptimizedBundle : Bool
    optimizedBundleAloneCreatesTypedBackgroundReceipt : Bool
    exactComparatorStateIdentityRequired : Bool
    exactApparatusIdentityRequired : Bool
    exactPredictionCarrierIdentityRequired : Bool
    fullOrdinaryClosureStillLeavesConstitutiveResidual : Bool
    fullOrdinaryClosureStillLeavesReproducibility : Bool
    fullOrdinaryClosureStillLeavesConstitutiveRatio : Bool
    fullOrdinaryClosureAutomaticallyProvesNegativeEffectiveG : Bool

canonicalOrdinaryModelClosureWeldBoundary : OrdinaryModelClosureWeldBoundary
canonicalOrdinaryModelClosureWeldBoundary =
  ordinary-model-closure-weld-boundary
    false false true true true true true true false
