module DASHI.Physics.ObserverConditionedMultiscaleTransport where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Core.MultiscaleMDL
open import DASHI.Physics.ObserverConditionedTransportBridge
import DASHI.Physics.MultiscaleWaveCorrespondence as Wave
import DASHI.Core.CandidateOnlyCore as CandidateOnly

------------------------------------------------------------------------
-- Cross-pollination surface.
--
-- The observer-conditioned bridge says which full states are indistinguishable
-- at a selected observer.  The multiscale core says how fine states split into
-- coarse representatives and residuals, how kernels commute with projection,
-- and how exact code lengths are counted.  This module joins those statements
-- without identifying observer equivalence with a constructed quotient, MDL
-- with physical action, or a generic kernel with a physical wave law.

record MultiscaleObserverSystem
  (system : TransportSystem)
  (observer : Observer system) : Set₂ where
  field
    tower : MultiscaleCarrier

    realise :
      ∀ {j} →
      Carrier tower j →
      State system

    projectionPreservesObservation :
      ∀ {j} (fine : Carrier tower (suc j)) →
      observe system observer (realise (project tower fine)) ≡
      observe system observer (realise fine)

open MultiscaleObserverSystem public

-- Exact projection stability immediately yields observer equivalence between
-- a fine representative and its coarse projection.  It does not yield full
-- state equality or future-dynamics equivalence.

projection-is-observer-equivalent :
  {system : TransportSystem} →
  {observer : Observer system} →
  (multiscale : MultiscaleObserverSystem system observer) →
  ∀ {j} (fine : Carrier (tower multiscale) (suc j)) →
  realise multiscale (project (tower multiscale) fine)
    ≈[ observer ]
  realise multiscale fine
projection-is-observer-equivalent multiscale fine =
  projectionPreservesObservation multiscale fine

------------------------------------------------------------------------
-- Residual / MDL attachment.
--
-- The residual remains available even when projection is sufficient for the
-- selected current observation.  It may still be required for another
-- observer, later dynamics, topology changes, phase recovery, or bounded-error
-- refinement.  Hence observer irrelevance is not identified with deletion.

record ObserverConditionedResidualMDL
  {system : TransportSystem}
  {observer : Observer system}
  (multiscale : MultiscaleObserverSystem system observer) : Set₂ where
  field
    codec : ResidualCodec (tower multiscale)
    cost : MDLCost (tower multiscale) codec

    currentObserverResidualDroppable :
      Bool

    currentObserverResidualDroppableIsOnlyCandidate :
      currentObserverResidualDroppable ≡ false

open ObserverConditionedResidualMDL public

observerStepDescriptionLength :
  {system : TransportSystem} →
  {observer : Observer system} →
  {multiscale : MultiscaleObserverSystem system observer} →
  (mdl : ObserverConditionedResidualMDL multiscale) →
  ∀ {j} →
  Carrier (tower multiscale) (suc j) →
  Nat
observerStepDescriptionLength mdl =
  stepDescriptionLength (cost mdl)

observer-step-description-is-coarse-plus-residual :
  {system : TransportSystem} →
  {observer : Observer system} →
  {multiscale : MultiscaleObserverSystem system observer} →
  (mdl : ObserverConditionedResidualMDL multiscale) →
  ∀ {j}
  (fine : Carrier (tower multiscale) (suc j)) →
  observerStepDescriptionLength mdl fine ≡
  coarseCost (cost mdl) (project (tower multiscale) fine) +
  residualCost (cost mdl) (residual (codec mdl) fine)
observer-step-description-is-coarse-plus-residual mdl fine = refl

------------------------------------------------------------------------
-- Kernel, lift, and temporal persistence seam.
--
-- Kernel naturality gives scale compatibility.  The additional observation
-- law below is an explicit premise: it is not inferred merely from naturality.

record ObserverKernelTower
  {system : TransportSystem}
  {observer : Observer system}
  (multiscale : MultiscaleObserverSystem system observer) : Set₂ where
  field
    kernels : KernelTower (tower multiscale)

    kernelPreservesSelectedObservation :
      ∀ {j} (state : Carrier (tower multiscale) j) →
      observe system observer
        (realise multiscale (kernel kernels j state)) ≡
      observe system observer
        (realise multiscale state)

open ObserverKernelTower public

kernel-is-observer-equivalent :
  {system : TransportSystem} →
  {observer : Observer system} →
  {multiscale : MultiscaleObserverSystem system observer} →
  (observerKernels : ObserverKernelTower multiscale) →
  ∀ {j} (state : Carrier (tower multiscale) j) →
  realise multiscale (kernel (kernels observerKernels) j state)
    ≈[ observer ]
  realise multiscale state
kernel-is-observer-equivalent observerKernels state =
  kernelPreservesSelectedObservation observerKernels state

record CrossFrameMultiscaleTransport
  {system : TransportSystem}
  {observer : Observer system}
  (multiscale : MultiscaleObserverSystem system observer) : Set₂ where
  field
    FrameInput : Set
    scale : Nat

    frameState : Carrier (tower multiscale) scale

    evolveFrame :
      FrameInput →
      Carrier (tower multiscale) scale →
      Carrier (tower multiscale) scale

    decodeFrame :
      Carrier (tower multiscale) scale →
      Sample system

    decodeFrameIsObservation :
      (state : Carrier (tower multiscale) scale) →
      decodeFrame state ≡
      observe system observer (realise multiscale state)

open CrossFrameMultiscaleTransport public

------------------------------------------------------------------------
-- Relation to the existing physics-facing wave dictionary.

record ObserverWaveRoute : Set where
  constructor observer-wave-route
  field
    selectedRoute : Wave.PhysicsCorrespondenceRoute
    selectedRouteAdmissible :
      Wave.AdmissiblePhysicsCorrespondenceRoute selectedRoute

    observerConditioningIsPhysicalLaw : Bool
    observerConditioningIsPhysicalLawIsFalse :
      observerConditioningIsPhysicalLaw ≡ false

    mdlIsPhysicalAction : Bool
    mdlIsPhysicalActionIsFalse : mdlIsPhysicalAction ≡ false

    temporalPersistenceProvesSpeedup : Bool
    temporalPersistenceProvesSpeedupIsFalse :
      temporalPersistenceProvesSpeedup ≡ false

open ObserverWaveRoute public

canonicalObserverWaveRoute : ObserverWaveRoute
canonicalObserverWaveRoute =
  observer-wave-route
    Wave.candidateWaveRoute
    tt
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Cross-domain readings.  These are interpretation routes, not theorems.

data CrossPollinatedReading : Set where
  microphoneWaveTubeReading : CrossPollinatedReading
  pixelTransportManifoldReading : CrossPollinatedReading
  stationaryPathResidualReading : CrossPollinatedReading
  multiscaleCausticBranchReading : CrossPollinatedReading
  temporalPathIdentityReading : CrossPollinatedReading
  observerConditionedMDLReading : CrossPollinatedReading

canonicalCrossPollinatedReadings : List CrossPollinatedReading
canonicalCrossPollinatedReadings =
  microphoneWaveTubeReading
  ∷ pixelTransportManifoldReading
  ∷ stationaryPathResidualReading
  ∷ multiscaleCausticBranchReading
  ∷ temporalPathIdentityReading
  ∷ observerConditionedMDLReading
  ∷ []

crossPollinatedReadingStatement : CrossPollinatedReading → String
crossPollinatedReadingStatement microphoneWaveTubeReading =
  "A microphone-conditioned acoustic carrier may track a bounded tube of contributions relevant to the selected microphone."
crossPollinatedReadingStatement pixelTransportManifoldReading =
  "A pixel-conditioned light carrier may track transport contributors that decode the selected radiance query."
crossPollinatedReadingStatement stationaryPathResidualReading =
  "Stationary paths may appear as sparse residual witnesses, but diffuse and multi-path terms remain admissible."
crossPollinatedReadingStatement multiscaleCausticBranchReading =
  "Caustic branches may be represented across projection/lift scales rather than as one universal point."
crossPollinatedReadingStatement temporalPathIdentityReading =
  "A transport carrier may preserve path or mode identity across frames when the chosen evolution supports it."
crossPollinatedReadingStatement observerConditionedMDLReading =
  "Description length may rank observer-relevant carriers without becoming physical action or proving optimality."

crossPollinatedReadingGap : CrossPollinatedReading → String
crossPollinatedReadingGap microphoneWaveTubeReading =
  "No theorem yet constructs the minimal microphone-relevant tube or proves wave-equation fidelity."
crossPollinatedReadingGap pixelTransportManifoldReading =
  "No theorem yet supplies unbiased arbitrary-scene rendering or replacement of RTX transport."
crossPollinatedReadingGap stationaryPathResidualReading =
  "No theorem yet proves stationary-phase dominance for every scene, frequency, or observer."
crossPollinatedReadingGap multiscaleCausticBranchReading =
  "No theorem yet proves stable branch tracking through occlusion, birth, merger, or topology change."
crossPollinatedReadingGap temporalPathIdentityReading =
  "No theorem yet proves long-horizon identity, contraction, or bounded accumulated error."
crossPollinatedReadingGap observerConditionedMDLReading =
  "No entropy model, Kraft proof, rate-distortion theorem, or matched-quality speed benchmark is supplied here."

------------------------------------------------------------------------
-- Candidate-only receipt.

observerMultiscaleTransportOwner : String
observerMultiscaleTransportOwner =
  "DASHI.Physics.ObserverConditionedMultiscaleTransport"

observerMultiscaleTransportRow : CandidateOnly.CandidateOnlyRow
observerMultiscaleTransportRow =
  CandidateOnly.candidateOnlyRow
    "observer-conditioned multiscale transport"
    observerMultiscaleTransportOwner
    "observer equivalence + residual MDL + kernel/lift + temporal wave bridge"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "Join observer projection, multiscale residual reconstruction, kernel naturality, and cross-frame transport state."
    "Physical fidelity, quotient minimality, path completeness, stability, and computational speedup remain open."
    true
    false
    false
    false
    false
    false
    false
    false

observerMultiscaleTransportReceipt :
  CandidateOnly.CandidateOnlyReceipt observerMultiscaleTransportRow
observerMultiscaleTransportReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
