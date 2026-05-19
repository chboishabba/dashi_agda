module DASHI.Physics.DashiDynamicsShiftInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s; _+_)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.List.Base using (_∷_; [])

open import DASHI.Physics.DashiDynamics as DD
open import DASHI.Physics.Closure.PhysicsClosureEmpiricalInstance as PCEI
open import DASHI.Physics.Closure.PhotonuclearEmpiricalConstantsRegistry as PECR
open import DASHI.Physics.Closure.PhotonuclearEmpiricalMeasurementSurface as PEMS
open import DASHI.Physics.Closure.PhotonuclearEmpiricalEvidenceSummary as PEES
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureConsumer as SOSPC
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Minimal concrete DashiDynamics package over an existing repo-native
-- carrier.
--
-- This instance is deliberately small:
--   * state carrier = the current shift pressure-point carrier
--   * path/reduction = equality on that carrier
--   * action/density/amplitude = pressure-ranked scalars on the same carrier
--   * empirical side = one packaged photonuclear validation surface
--   * control side = the packaged held/control pressure consumer
--
-- It is an interface inhabitant only, not a derivation claim.

photonuclearMeasuredObservablesNat :
  PEMS.PhotonuclearMeasuredObservables Nat
photonuclearMeasuredObservablesNat =
  record
    { defectIntensity = suc zero
    ; promotedObservable = suc (suc zero)
    ; densityProxy = suc zero
    ; saturationProxy = zero
    }

photonuclearSampleNat :
  PEMS.PhotonuclearMeasurementSample Nat
photonuclearSampleNat =
  record
    { sampleLabel = "canonical-photonuclear-sample"
    ; photonEnergy = suc (suc (suc zero))
    ; observables = photonuclearMeasuredObservablesNat
    }

photonuclearProvenanceNat :
  PEMS.PhotonuclearProvenanceHook
photonuclearProvenanceNat =
  record
    { sourceLabel = "repo-canonical-photonuclear-lane"
    ; sourceKind = "packaged-sample"
    ; sourceRef = "Docs/PhotonuclearEmpiricalRegistry.md"
    ; note = "Minimal packaged sample for DashiDynamics interface instantiation."
    }

photonuclearMeasurementRecordNat :
  PEMS.PhotonuclearMeasurementRecord Nat
photonuclearMeasurementRecordNat =
  record
    { measurementLabel = "canonical-photonuclear-measurement"
    ; sample = photonuclearSampleNat
    ; provenance = photonuclearProvenanceNat
    }

photonuclearMeasurementSurfaceNat :
  PEMS.PhotonuclearEmpiricalMeasurementSurface Nat
photonuclearMeasurementSurfaceNat =
  PEMS.mkPhotonuclearEmpiricalMeasurementSurface
    PCEI.physicsClosureEmpirical
    photonuclearMeasuredObservablesNat
    (photonuclearSampleNat ∷ [])
    (photonuclearMeasurementRecordNat ∷ [])
    (photonuclearProvenanceNat ∷ [])
    PEMS.canonicalPhotonuclearClaimBoundary

photonuclearEvidenceSummaryNat :
  PEES.PhotonuclearEvidenceSummary Nat
photonuclearEvidenceSummaryNat =
  PEES.mkPhotonuclearEvidenceSummary
    "canonical-dashi-dynamics-empirical-evidence"
    PECR.photonuclearConstantsRegistry
    photonuclearMeasurementSurfaceNat

photonuclearValidationSummaryNat :
  PEVS.PhotonuclearEmpiricalValidationSummary Nat
photonuclearValidationSummaryNat =
  PEVS.mkPhotonuclearEmpiricalValidationSummary
    "canonical-dashi-dynamics-empirical-validation"
    photonuclearEvidenceSummaryNat

shiftPointPath :
  SPTI.ShiftPressurePoint →
  SPTI.ShiftPressurePoint →
  Set
shiftPointPath a b = a ≡ b

shiftPointReduction :
  SPTI.ShiftPressurePoint →
  SPTI.ShiftPressurePoint →
  Set
shiftPointReduction a b = a ≡ b

shiftPressureRank :
  SPTI.ShiftPressurePoint →
  Nat
shiftPressureRank SPTI.shiftStartPoint = zero
shiftPressureRank SPTI.shiftNextPoint = suc zero
shiftPressureRank SPTI.shiftHeldExitPoint = suc (suc zero)

shiftPressureAdvance :
  SPTI.ShiftPressurePoint →
  SPTI.ShiftPressurePoint
shiftPressureAdvance SPTI.shiftStartPoint = SPTI.shiftNextPoint
shiftPressureAdvance SPTI.shiftNextPoint = SPTI.shiftHeldExitPoint
shiftPressureAdvance SPTI.shiftHeldExitPoint = SPTI.shiftHeldExitPoint

shiftDensityBase : Nat
shiftDensityBase =
  PEMS.PhotonuclearMeasuredObservables.densityProxy
    photonuclearMeasuredObservablesNat

shiftPointAction :
  ∀ {a b : SPTI.ShiftPressurePoint} →
  shiftPointPath a b →
  Nat
shiftPointAction {a} refl = shiftPressureRank a

shiftPointDensity :
  SPTI.ShiftPressurePoint →
  Nat
shiftPointDensity s = shiftDensityBase + shiftPressureRank s

shiftPointAmplitude :
  ∀ {a b : SPTI.ShiftPressurePoint} →
  shiftPointPath a b →
  Nat
shiftPointAmplitude {a} refl = shiftPressureRank a

shiftHeldPotential :
  SPTI.ShiftPressurePoint →
  Nat
shiftHeldPotential SPTI.shiftStartPoint = suc (suc zero)
shiftHeldPotential SPTI.shiftNextPoint = suc zero
shiftHeldPotential SPTI.shiftHeldExitPoint = zero

iterate :
  {A : Set} →
  Nat →
  (A → A) →
  A →
  A
iterate zero f x = x
iterate (suc n) f x = iterate n f (f x)

data ShiftNonHeld :
  SPTI.ShiftPressurePoint →
  Set where
  atStart :
    ShiftNonHeld SPTI.shiftStartPoint
  atNext :
    ShiftNonHeld SPTI.shiftNextPoint

ShiftSelfActionBound : Set
ShiftSelfActionBound =
  (s : SPTI.ShiftPressurePoint) →
  shiftPointAction {a = s} {b = s} refl ≤ shiftPointDensity s

data ShiftAdmissibleTarget :
  SPTI.ShiftPressurePoint →
  SPTI.ShiftPressurePoint →
  Set where
  start-next :
    ShiftAdmissibleTarget
      SPTI.shiftStartPoint
      SPTI.shiftNextPoint
  start-held :
    ShiftAdmissibleTarget
      SPTI.shiftStartPoint
      SPTI.shiftHeldExitPoint
  next-held :
    ShiftAdmissibleTarget
      SPTI.shiftNextPoint
      SPTI.shiftHeldExitPoint
  held-held :
    ShiftAdmissibleTarget
      SPTI.shiftHeldExitPoint
      SPTI.shiftHeldExitPoint

shiftAdvanceAdmissible :
  (s : SPTI.ShiftPressurePoint) →
  ShiftAdmissibleTarget s (shiftPressureAdvance s)
shiftAdvanceAdmissible SPTI.shiftStartPoint = start-next
shiftAdvanceAdmissible SPTI.shiftNextPoint = next-held
shiftAdvanceAdmissible SPTI.shiftHeldExitPoint = held-held

shiftTransitionAction :
  (s t : SPTI.ShiftPressurePoint) →
  ShiftAdmissibleTarget s t →
  Nat
shiftTransitionAction .SPTI.shiftStartPoint .SPTI.shiftNextPoint start-next =
  suc zero
shiftTransitionAction .SPTI.shiftStartPoint .SPTI.shiftHeldExitPoint start-held =
  suc (suc zero)
shiftTransitionAction .SPTI.shiftNextPoint .SPTI.shiftHeldExitPoint next-held =
  suc zero
shiftTransitionAction .SPTI.shiftHeldExitPoint .SPTI.shiftHeldExitPoint held-held =
  zero

ShiftLeastActionLaw : Set
ShiftLeastActionLaw =
  (s t : SPTI.ShiftPressurePoint) →
  (target : ShiftAdmissibleTarget s t) →
  shiftTransitionAction s (shiftPressureAdvance s) (shiftAdvanceAdmissible s)
    ≤
  shiftTransitionAction s t target

ShiftActionLaw : Set
ShiftActionLaw = Σ ShiftSelfActionBound (λ _ → ShiftLeastActionLaw)

ShiftDensityLaw : Set
ShiftDensityLaw =
  (s : SPTI.ShiftPressurePoint) →
  shiftPointDensity s ≤ shiftPointDensity (shiftPressureAdvance s)

ShiftAmplitudeLaw : Set
ShiftAmplitudeLaw =
  (s : SPTI.ShiftPressurePoint) →
  shiftPressureRank s ≤ shiftPressureRank (shiftPressureAdvance s)

ShiftHeldFixedPointLaw : Set
ShiftHeldFixedPointLaw =
  shiftPressureAdvance SPTI.shiftHeldExitPoint ≡ SPTI.shiftHeldExitPoint

ShiftPotentialDescentLaw : Set
ShiftPotentialDescentLaw =
  (s : SPTI.ShiftPressurePoint) →
  shiftHeldPotential (shiftPressureAdvance s) ≤ shiftHeldPotential s

ShiftStrictPotentialDescentLaw : Set
ShiftStrictPotentialDescentLaw =
  (s : SPTI.ShiftPressurePoint) →
  ShiftNonHeld s →
  shiftHeldPotential (shiftPressureAdvance s) < shiftHeldPotential s

ShiftReductionLaw : Set
ShiftReductionLaw =
  Σ ShiftHeldFixedPointLaw
    (λ _ →
      Σ ShiftPotentialDescentLaw
        (λ _ → ShiftStrictPotentialDescentLaw))

ShiftConvergenceLaw : Set
ShiftConvergenceLaw =
  (s : SPTI.ShiftPressurePoint) →
  shiftPressureAdvance (shiftPressureAdvance s) ≡ SPTI.shiftHeldExitPoint

ShiftConvergesToHeld : Set
ShiftConvergesToHeld =
  (s : SPTI.ShiftPressurePoint) →
  Σ Nat
    (λ n →
      iterate n shiftPressureAdvance s
        ≡
      SPTI.shiftHeldExitPoint)

ShiftConvergesToHeldWithin2 : Set
ShiftConvergesToHeldWithin2 =
  (s : SPTI.ShiftPressurePoint) →
  Σ Nat
    (λ n →
      Σ (n ≤ suc (suc zero))
        (λ _ →
          iterate n shiftPressureAdvance s
            ≡
          SPTI.shiftHeldExitPoint))

shiftPointActionBound : ShiftSelfActionBound
shiftPointActionBound SPTI.shiftStartPoint = z≤n
shiftPointActionBound SPTI.shiftNextPoint = s≤s z≤n
shiftPointActionBound SPTI.shiftHeldExitPoint = s≤s (s≤s z≤n)

shiftLeastActionWitness : ShiftLeastActionLaw
shiftLeastActionWitness SPTI.shiftStartPoint SPTI.shiftNextPoint start-next =
  NatP.≤-refl
shiftLeastActionWitness SPTI.shiftStartPoint SPTI.shiftHeldExitPoint start-held =
  s≤s z≤n
shiftLeastActionWitness SPTI.shiftNextPoint SPTI.shiftHeldExitPoint next-held =
  NatP.≤-refl
shiftLeastActionWitness SPTI.shiftHeldExitPoint SPTI.shiftHeldExitPoint held-held =
  NatP.≤-refl

shiftPointDensityMonotone : ShiftDensityLaw
shiftPointDensityMonotone SPTI.shiftStartPoint = s≤s z≤n
shiftPointDensityMonotone SPTI.shiftNextPoint = s≤s (s≤s z≤n)
shiftPointDensityMonotone SPTI.shiftHeldExitPoint = NatP.≤-refl

shiftPressureRankMonotone : ShiftAmplitudeLaw
shiftPressureRankMonotone SPTI.shiftStartPoint = z≤n
shiftPressureRankMonotone SPTI.shiftNextPoint = s≤s z≤n
shiftPressureRankMonotone SPTI.shiftHeldExitPoint = NatP.≤-refl

shiftHeldFixedPointWitness : ShiftHeldFixedPointLaw
shiftHeldFixedPointWitness = refl

shiftPotentialDescentWitness : ShiftPotentialDescentLaw
shiftPotentialDescentWitness SPTI.shiftStartPoint = s≤s z≤n
shiftPotentialDescentWitness SPTI.shiftNextPoint = z≤n
shiftPotentialDescentWitness SPTI.shiftHeldExitPoint = NatP.≤-refl

shiftStrictPotentialDescentWitness : ShiftStrictPotentialDescentLaw
shiftStrictPotentialDescentWitness SPTI.shiftStartPoint atStart = s≤s (s≤s z≤n)
shiftStrictPotentialDescentWitness SPTI.shiftNextPoint atNext = s≤s z≤n

shiftPointReductionWitness : ShiftReductionLaw
shiftPointReductionWitness =
  shiftHeldFixedPointWitness
  , (shiftPotentialDescentWitness , shiftStrictPotentialDescentWitness)

shiftConvergenceLawWitness : ShiftConvergenceLaw
shiftConvergenceLawWitness SPTI.shiftStartPoint = refl
shiftConvergenceLawWitness SPTI.shiftNextPoint = refl
shiftConvergenceLawWitness SPTI.shiftHeldExitPoint = refl

shiftConvergesToHeld : ShiftConvergesToHeld
shiftConvergesToHeld SPTI.shiftStartPoint =
  suc (suc zero) , refl
shiftConvergesToHeld SPTI.shiftNextPoint =
  suc zero , refl
shiftConvergesToHeld SPTI.shiftHeldExitPoint =
  zero , refl

shiftConvergesToHeldWithin2 : ShiftConvergesToHeldWithin2
shiftConvergesToHeldWithin2 SPTI.shiftStartPoint =
  suc (suc zero) , (NatP.≤-refl , refl)
shiftConvergesToHeldWithin2 SPTI.shiftNextPoint =
  suc zero , (s≤s z≤n , refl)
shiftConvergesToHeldWithin2 SPTI.shiftHeldExitPoint =
  zero , (z≤n , refl)

shiftActionLawWitness : ShiftActionLaw
shiftActionLawWitness = shiftPointActionBound , shiftLeastActionWitness

shiftDashiDynamics :
  DD.DashiDynamics Nat
shiftDashiDynamics =
  record
    { State = SPTI.ShiftPressurePoint
    ; Path = shiftPointPath
    ; Observable = SPTI.ShiftPressurePoint
    ; Scalar = Nat
    ; Action = shiftPointAction
    ; Density = shiftPointDensity
    ; Amplitude = shiftPointAmplitude
    ; Reduction = shiftPointReduction
    ; ActionLaw = ShiftActionLaw
    ; DensityLaw = ShiftDensityLaw
    ; ReductionLaw = ShiftReductionLaw
    ; ConvergenceLaw = ShiftConvergenceLaw
    ; empiricalValidation = photonuclearValidationSummaryNat
    ; pressureConsumer = SOSPC.shiftObservableSignaturePressureConsumer
    ; interfaceLabel = "shift-dashi-dynamics"
    ; nonClaimBoundary =
        "Interface packaging only"
        ∷ "Action/density/amplitude are pressure-ranked proxies on the packaged carrier"
        ∷ "Density is empirical densityProxy plus shift pressure rank"
        ∷ "Action law includes a bounded least-action witness over admissible pressure steps"
        ∷ "Reduction law includes a held-point fixed point, potential descent, and strict descent off the held point"
        ∷ "Convergence law is the exact two-step absorption of every shift point to the held point"
        ∷ "Pressure advance is a bounded three-point endomap, not a Schrödinger derivation"
        ∷ "No MeasurementSurface -> DashiStateSchema projection is implied"
        ∷ "No new physics derivation claim is made"
        ∷ []
    }

shiftHeldStatus :
  DD.heldControlPressureStatus shiftDashiDynamics ≡ SPTI.shiftPressureStatus SPTI.shiftHeldExitPoint
shiftHeldStatus = refl

shiftEmpiricalStatuses :
  DD.empiricalValidationStatuses shiftDashiDynamics
  ≡
  PEVS.PhotonuclearEmpiricalValidationSummary.statuses photonuclearValidationSummaryNat
shiftEmpiricalStatuses = refl
