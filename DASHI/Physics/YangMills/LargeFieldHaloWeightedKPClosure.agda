module DASHI.Physics.YangMills.LargeFieldHaloWeightedKPClosure where

-- Conditional halo-volume alternative to the CMP 122 relative-tree route.
--
-- This is deliberately *not* a CMP 122 model.  It records the extra facts
-- needed to replace a relative-tree fibre estimate by ordinary animal
-- counting: bounded halo ownership, an additive per-block coercive score,
-- and a controlled extensive loss.  In particular `localThreshold` is kept
-- distinct from the source suppression exponent `p₀`; identifying them would
-- add a theorem that CMP 122 II does not state.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base renaming (ℕ to Nat)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _+ℝ_
  ; _*ℝ_
  )
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  ; paperImport
  )

-- The analytic carrier required by the halo route.  Every field below is an
-- input to a conditional reducer, rather than an assertion about Bałaban's
-- actual CMP 122 indices.
record LargeFieldHaloCoercivityModel : Set₁ where
  field
    Scale : Set
    Polymer : Set
    Block : Set

    scaleOf : Polymer → Scale
    largeBlocks : Polymer → List Block

    -- η is a local large-field threshold.  p₀ is the source exponent in
    -- factors such as exp (-c p₀(gₖ)); they intentionally have different
    -- types/roles in this contract.
    localThreshold : Scale → ℝ
    p₀-suppressionExponent : Scale → ℝ

    weightedSize : Polymer → ℝ
    weightedLargeBlockCount : Polymer → ℝ
    localCoerciveScore : Polymer → ℝ
    magnitude : Polymer → ℝ

    volumeCoefficient : Scale → ℝ
    scoreCoefficient : Scale → ℝ
    treeDecayCoefficient : Scale → ℝ
    treeLength : Polymer → Nat
    extensiveLoss : Scale → ℝ
    haloMultiplicity : Scale → ℝ

    -- Geometric and coercive leaves.  They are the actual mathematical
    -- obligations for the halo route, not definitions.
    polymerContainedInBoundedHalo : Polymer → Set
    haloCompression : ∀ Y →
      weightedSize Y ≤ℝ
      haloMultiplicity (scaleOf Y) *ℝ weightedLargeBlockCount Y

    scoreLowerBound : ∀ Y →
      (localThreshold (scaleOf Y) *ℝ localThreshold (scaleOf Y)) *ℝ
      weightedLargeBlockCount Y ≤ℝ localCoerciveScore Y

    activityCoercivity : ∀ (Y : Polymer) → Set
    lossesControlledExtensively : ∀ (Y : Polymer) → Set

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus

open LargeFieldHaloCoercivityModel public

-- This is the precise conditional result required before ordinary rooted
-- animal counting may replace the relative-tree fibre theorem.  It leaves the
-- real-exponential arithmetic to the existing KP arithmetic kernels, but
-- makes the non-arithmetic handoff impossible to hide.
record HaloVolumeToAnimalKPInputs
  (model : LargeFieldHaloCoercivityModel) : Set₁ where
  open LargeFieldHaloCoercivityModel model
  field
    -- The model's coercive activity estimate must be converted into a volume
    -- penalty using the preceding halo and score bounds.  This field is not a
    -- duplicate of `activityCoercivity`: it is the theorem that accounts for
    -- all interpolation, Jacobian, boundary, and localisation losses.
    effectiveVolumeSuppression :
      ∀ (Y : LargeFieldHaloCoercivityModel.Polymer model) → Set

    -- An actual multiscale graph, its degree estimate, and its connected
    -- polymer semantics are needed before an animal estimate is applicable.
    multiscaleAnimalCarrier : Set
    multiscaleDegreeBound : Nat
    polymerConnectedInMultiscaleCarrier :
      LargeFieldHaloCoercivityModel.Polymer model → Set
    rootedAnimalCountingBound : Set

    -- Attachments must be injected into a finite/summable owned family.
    attachmentMultiplicityControlled : Set
    attachmentFibreResummation : Set

    -- The downstream exact threshold is arithmetic only once these inputs
    -- exist.  It must use the effective volume penalty, never p₀ by name.
    exactWeightedKPThreshold : Set

open HaloVolumeToAnimalKPInputs public

-- Source audit for deciding whether CMP 119/122 can instantiate the above
-- model.  These are facts about the primary-source extraction, not proof
-- status of the conditional reducer itself.
record HaloRouteSourceAudit : Set where
  field
    boundedHaloForEveryRelevantPolymer : Bool
    additivePerBlockCoerciveCost : Bool
    allNoncoerciveLossesExtensive : Bool
    multiscaleConnectivityExtracted : Bool
    attachmentOwnershipExtracted : Bool

-- CMP 122 II explicitly supplies bounded enlargement operations (including
-- the ten-layer S(Z) construction), but the inspected estimates do not yet
-- establish the three stronger hypotheses required above for every relative
-- localisation index.  Therefore this route is promising but uninstantiated.
currentCMP122HaloRouteAudit : HaloRouteSourceAudit
currentCMP122HaloRouteAudit = record
  { boundedHaloForEveryRelevantPolymer = false
  ; additivePerBlockCoerciveCost = false
  ; allNoncoerciveLossesExtensive = false
  ; multiscaleConnectivityExtracted = false
  ; attachmentOwnershipExtracted = false
  }

data HaloRouteInstantiationState : Set where
  halo-route-source-uninstantiated : HaloRouteInstantiationState
  halo-route-source-instantiated : HaloRouteInstantiationState

currentHaloRouteInstantiationState : HaloRouteInstantiationState
currentHaloRouteInstantiationState = halo-route-source-uninstantiated

-- The route is useful as a conditional analytic reducer, but it is not a new
-- P10/P11 discharge and cannot affect Clay promotion without an actual source
-- model plus inhabited analytic witnesses.
currentHaloRouteStatus : VerificationStatus
currentHaloRouteStatus = paperImport
