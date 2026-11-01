module DASHI.Computation.LESGLESWorldTransportBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Interop.ObservationTransportSpine as Spine
import DASHI.Physics.Closure.LightTransportFibreClosure as Light

------------------------------------------------------------------------
-- LES / GLES world transport bridge.
--
-- This is a theorem-thin computation lane for the engineering reading:
--
--   high-fidelity simulation
--     -> latent / invariant quotient
--     -> fast GLES-style world runner
--     -> conformance residual
--
-- It deliberately does not assert physical exactness, global O(1) update,
-- or empirical conformance without the named receipts.

data LESGLESStage : Set where
  highFidelitySimulationStage : LESGLESStage
  latentInvariantQuotientStage : LESGLESStage
  glesWorldRunnerStage : LESGLESStage
  conformanceResidualStage : LESGLESStage
  receiptReviewStage : LESGLESStage

canonicalLESGLESStages : List LESGLESStage
canonicalLESGLESStages =
  highFidelitySimulationStage
  ∷ latentInvariantQuotientStage
  ∷ glesWorldRunnerStage
  ∷ conformanceResidualStage
  ∷ receiptReviewStage
  ∷ []

data LESGLESGate : Set where
  highFidelitySimulationReceiptGate : LESGLESGate
  invariantQuotientReceiptGate : LESGLESGate
  runnerDeterminismReceiptGate : LESGLESGate
  residualDefinitionReceiptGate : LESGLESGate
  sideInformationAccountingGate : LESGLESGate
  empiricalConformanceReceiptGate : LESGLESGate
  lightTransportClosureGate : LESGLESGate

canonicalLESGLESGates : List LESGLESGate
canonicalLESGLESGates =
  highFidelitySimulationReceiptGate
  ∷ invariantQuotientReceiptGate
  ∷ runnerDeterminismReceiptGate
  ∷ residualDefinitionReceiptGate
  ∷ sideInformationAccountingGate
  ∷ empiricalConformanceReceiptGate
  ∷ lightTransportClosureGate
  ∷ []

data LESGLESNonPromotionBoundary : Set where
  noFullPhysicalExactnessClaim : LESGLESNonPromotionBoundary
  noGlobalO1WorldUpdateClaim : LESGLESNonPromotionBoundary
  noEmpiricalConformanceWithoutReceipts : LESGLESNonPromotionBoundary
  noResidualDiscard : LESGLESNonPromotionBoundary
  noUncountedRunnerSideInformation : LESGLESNonPromotionBoundary
  noLatentQuotientInvertibilityClaim : LESGLESNonPromotionBoundary
  noGLESRunnerEqualsHighFidelitySimulatorClaim : LESGLESNonPromotionBoundary

canonicalLESGLESBoundaries : List LESGLESNonPromotionBoundary
canonicalLESGLESBoundaries =
  noFullPhysicalExactnessClaim
  ∷ noGlobalO1WorldUpdateClaim
  ∷ noEmpiricalConformanceWithoutReceipts
  ∷ noResidualDiscard
  ∷ noUncountedRunnerSideInformation
  ∷ noLatentQuotientInvertibilityClaim
  ∷ noGLESRunnerEqualsHighFidelitySimulatorClaim
  ∷ []

record LESGLESWorldTransportBridge : Set₁ where
  field
    HighFidelityWorld : Set
    LESState : Set
    InvariantQuotient : Set
    SideInformation : Set
    GLESRunnerState : Set
    FrameArtifact : Set
    ConformanceResidual : Set
    SimulationReceipt : Set
    QuotientReceipt : Set
    RunnerReceipt : Set
    ResidualReceipt : Set
    EmpiricalConformanceReceipt : Set

    lightSurface :
      Light.LightTransportFibreClosure

    observationSurface :
      Spine.ObservationTransportSurface

    observationDomainIsLESGLES :
      Spine.ObservationTransportSurface.domain observationSurface
        ≡ Spine.lesGlesWorldTransportDomain

    lesApproximation :
      HighFidelityWorld →
      LESState

    invariantQuotient :
      LESState →
      InvariantQuotient

    runnerFromQuotient :
      InvariantQuotient →
      SideInformation →
      GLESRunnerState

    renderFrame :
      GLESRunnerState →
      FrameArtifact

    residualAgainst :
      HighFidelityWorld →
      GLESRunnerState →
      ConformanceResidual

    residualAdmissible :
      ConformanceResidual →
      Set

    simulationReceipt :
      HighFidelityWorld →
      SimulationReceipt

    quotientReceipt :
      LESState →
      InvariantQuotient →
      QuotientReceipt

    runnerReceipt :
      InvariantQuotient →
      GLESRunnerState →
      RunnerReceipt

    residualReceipt :
      ConformanceResidual →
      ResidualReceipt

    empiricalConformanceReceipt :
      ConformanceResidual →
      EmpiricalConformanceReceipt

    gateSatisfied :
      LESGLESGate →
      Set

    stages :
      List LESGLESStage

    gates :
      List LESGLESGate

    bridgeReading :
      String

open LESGLESWorldTransportBridge public

glesFrameFromHighFidelityWorld :
  (bridge : LESGLESWorldTransportBridge) →
  SideInformation bridge →
  HighFidelityWorld bridge →
  FrameArtifact bridge
glesFrameFromHighFidelityWorld bridge sideInfo world =
  renderFrame bridge runner
  where
    les :
      LESState bridge
    les = lesApproximation bridge world

    quotient :
      InvariantQuotient bridge
    quotient = invariantQuotient bridge les

    runner :
      GLESRunnerState bridge
    runner = runnerFromQuotient bridge quotient sideInfo

residualFromHighFidelityWorld :
  (bridge : LESGLESWorldTransportBridge) →
  SideInformation bridge →
  HighFidelityWorld bridge →
  ConformanceResidual bridge
residualFromHighFidelityWorld bridge sideInfo world =
  residualAgainst bridge world runner
  where
    les :
      LESState bridge
    les = lesApproximation bridge world

    quotient :
      InvariantQuotient bridge
    quotient = invariantQuotient bridge les

    runner :
      GLESRunnerState bridge
    runner = runnerFromQuotient bridge quotient sideInfo

record LESGLESConformanceWitness
    (bridge : LESGLESWorldTransportBridge) : Set₁ where
  field
    world :
      HighFidelityWorld bridge

    sideInformation :
      SideInformation bridge

    residual :
      ConformanceResidual bridge

    residualMatchesRunner :
      residualFromHighFidelityWorld bridge sideInformation world ≡ residual

    residualGate :
      residualAdmissible bridge residual

    residualReceiptWitness :
      ResidualReceipt bridge

    empiricalReceiptWitness :
      EmpiricalConformanceReceipt bridge

    witnessReading :
      String

open LESGLESConformanceWitness public

record LESGLESNonPromotionCertificate
    (bridge : LESGLESWorldTransportBridge) : Set where
  field
    boundaries :
      List LESGLESNonPromotionBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalLESGLESBoundaries

    stagesAreCanonical :
      stages bridge ≡ canonicalLESGLESStages

    gatesAreCanonical :
      gates bridge ≡ canonicalLESGLESGates

    fullPhysicalExactnessPromoted :
      Bool

    fullPhysicalExactnessPromotedIsFalse :
      fullPhysicalExactnessPromoted ≡ false

    globalO1WorldUpdatePromoted :
      Bool

    globalO1WorldUpdatePromotedIsFalse :
      globalO1WorldUpdatePromoted ≡ false

    empiricalConformanceWithoutReceipt :
      Bool

    empiricalConformanceWithoutReceiptIsFalse :
      empiricalConformanceWithoutReceipt ≡ false

    residualDiscarded :
      Bool

    residualDiscardedIsFalse :
      residualDiscarded ≡ false

    certificateReading :
      String

open LESGLESNonPromotionCertificate public

canonicalLightSurfaceForLESGLES :
  Light.LightTransportFibreClosure
canonicalLightSurfaceForLESGLES =
  record
    { SceneState = ⊤
    ; UnlitViewport = ⊤
    ; PhotonOrPixelCarrier = ⊤
    ; GeometryFibre = ⊤
    ; MaterialFibre = ⊤
    ; SpectralFibre = ⊤
    ; VisibilityFibre = ⊤
    ; TransportOperator = ⊤
    ; ClosureReceipt = ⊤
    ; ResidualDefect = ⊤
    ; LitViewport = ⊤
    ; baselineViewport = λ _ → tt
    ; carrierFromViewport = λ _ → tt
    ; geometryFibre = λ _ _ → tt
    ; materialFibre = λ _ _ → tt
    ; spectralFibre = λ _ → tt
    ; visibilityFibre = λ _ _ → tt
    ; mixingMode = λ _ → Light.diffuseSplit
    ; compositionShape = λ _ → Light.cachedClosureChart
    ; closeTransport = λ _ _ _ _ → tt
    ; applyClosedTransport = λ _ _ → tt
    ; closureReceipt = λ _ → tt
    ; residualDefect = λ _ _ → tt
    ; residualAdmissible = λ _ → ⊤
    ; gateSatisfied = λ _ _ → ⊤
    ; pipeline = Light.canonicalLightTransportPipeline
    ; transportReading =
        "Toy light-transport surface used only to type the LES/GLES bridge closure boundary."
    }

canonicalLESGLESObservationSurface :
  Spine.ObservationTransportSurface
canonicalLESGLESObservationSurface =
  record
    { domain =
        Spine.lesGlesWorldTransportDomain
    ; LatentCarrier =
        ⊤
    ; ObservationQuotient =
        ⊤
    ; AdmissibilityGate =
        ⊤
    ; TransportOperator =
        ⊤
    ; Artifact =
        ⊤
    ; observe =
        λ _ → tt
    ; gate =
        λ _ → tt
    ; transport =
        λ _ _ _ → tt
    ; promotionBoundary =
        Spine.nonPromotingObservation
    ; nonClaims =
        Spine.canonicalObservationNonClaims
    ; plainReading =
        "LES/GLES world transport observes a high-fidelity world through a lossy invariant quotient before a fast runner is allowed to emit an artifact."
    }

canonicalLESGLESWorldTransportBridge :
  LESGLESWorldTransportBridge
canonicalLESGLESWorldTransportBridge =
  record
    { HighFidelityWorld =
        ⊤
    ; LESState =
        ⊤
    ; InvariantQuotient =
        ⊤
    ; SideInformation =
        ⊤
    ; GLESRunnerState =
        ⊤
    ; FrameArtifact =
        ⊤
    ; ConformanceResidual =
        ⊤
    ; SimulationReceipt =
        ⊤
    ; QuotientReceipt =
        ⊤
    ; RunnerReceipt =
        ⊤
    ; ResidualReceipt =
        ⊤
    ; EmpiricalConformanceReceipt =
        ⊤
    ; lightSurface =
        canonicalLightSurfaceForLESGLES
    ; observationSurface =
        canonicalLESGLESObservationSurface
    ; observationDomainIsLESGLES =
        refl
    ; lesApproximation =
        λ _ → tt
    ; invariantQuotient =
        λ _ → tt
    ; runnerFromQuotient =
        λ _ _ → tt
    ; renderFrame =
        λ _ → tt
    ; residualAgainst =
        λ _ _ → tt
    ; residualAdmissible =
        λ _ → ⊤
    ; simulationReceipt =
        λ _ → tt
    ; quotientReceipt =
        λ _ _ → tt
    ; runnerReceipt =
        λ _ _ → tt
    ; residualReceipt =
        λ _ → tt
    ; empiricalConformanceReceipt =
        λ _ → tt
    ; gateSatisfied =
        λ _ → ⊤
    ; stages =
        canonicalLESGLESStages
    ; gates =
        canonicalLESGLESGates
    ; bridgeReading =
        "High-fidelity simulation may feed a LES/invariant quotient and a fast GLES runner only as a receipt-gated approximation with explicit conformance residuals."
    }

canonicalLESGLESNonPromotionCertificate :
  LESGLESNonPromotionCertificate canonicalLESGLESWorldTransportBridge
canonicalLESGLESNonPromotionCertificate =
  record
    { boundaries =
        canonicalLESGLESBoundaries
    ; boundariesAreCanonical =
        refl
    ; stagesAreCanonical =
        refl
    ; gatesAreCanonical =
        refl
    ; fullPhysicalExactnessPromoted =
        false
    ; fullPhysicalExactnessPromotedIsFalse =
        refl
    ; globalO1WorldUpdatePromoted =
        false
    ; globalO1WorldUpdatePromotedIsFalse =
        refl
    ; empiricalConformanceWithoutReceipt =
        false
    ; empiricalConformanceWithoutReceiptIsFalse =
        refl
    ; residualDiscarded =
        false
    ; residualDiscardedIsFalse =
        refl
    ; certificateReading =
        "The LES/GLES bridge is non-promoting: exact physics, global O(1) world updates, residual-free rendering, and empirical conformance all stay blocked unless their receipts are supplied."
    }
