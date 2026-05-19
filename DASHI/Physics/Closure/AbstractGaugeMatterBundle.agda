module DASHI.Physics.Closure.AbstractGaugeMatterBundle where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
import DASHI.Physics.Closure.RGObservableInvariance as RGOI

record AbstractGaugeMatterBundle : Setω where
  field
    Carrier : Set
    GaugeFiber : Set
    MatterField : Set
    Observable : Set
    ContinuumField : Set

    evolve : Carrier → Carrier
    coarse : Carrier → Carrier
    offset : Carrier → Carrier

    admissible : Carrier → Bool
    coneWitness : Carrier → Set
    mdlLevel : Carrier → Nat

    gaugeAction : GaugeFiber → Carrier → Carrier
    matterOf : Carrier → MatterField
    observableOf : Carrier → Observable
    continuumLift : Carrier → ContinuumField
    pickGauge : Carrier → GGC.Gauge

open AbstractGaugeMatterBundle public

record NaturalDynamicsWitness
  (B : AbstractGaugeMatterBundle) : Setω where
  field
    admissible-evolve :
      ∀ x →
      admissible B x ≡ true →
      admissible B (evolve B x) ≡ true

    admissible-coarse :
      ∀ x →
      admissible B x ≡ true →
      admissible B (coarse B x) ≡ true

    admissible-offset :
      ∀ x →
      admissible B x ≡ true →
      admissible B (offset B x) ≡ true

    mdl-descent :
      ∀ x →
      mdlLevel B (evolve B x) ≡ mdlLevel B x

    coarse-offset-commute :
      ∀ x →
      coarse B (offset B x) ≡ offset B (coarse B x)

    cone-preserved-evolve :
      ∀ x →
      coneWitness B x →
      coneWitness B (evolve B x)

    cone-preserved-coarse :
      ∀ x →
      coneWitness B x →
      coneWitness B (coarse B x)

    cone-preserved-offset :
      ∀ x →
      coneWitness B x →
      coneWitness B (offset B x)

open NaturalDynamicsWitness public

record ConservedObservableWitness
  (B : AbstractGaugeMatterBundle) : Setω where
  field
    Charge : Set
    chargeOf : Carrier B → Charge

    charge-evolve :
      ∀ x →
      admissible B x ≡ true →
      chargeOf x ≡ chargeOf (evolve B x)

    charge-coarse :
      ∀ x →
      admissible B x ≡ true →
      chargeOf x ≡ chargeOf (coarse B x)

    observable-gauge-invariant :
      ∀ g x →
      observableOf B (gaugeAction B g x) ≡ observableOf B x

open ConservedObservableWitness public

record ContinuumWitness
  (B : AbstractGaugeMatterBundle) : Setω where
  field
    LimitCarrier : Set
    LimitObservable : Set
    scaleToLimit : ContinuumField B → LimitCarrier
    limitObservable : LimitCarrier → LimitObservable
    observableProjection : Observable B → LimitObservable
    limitCone : LimitCarrier → Set
    limitMdl : LimitCarrier → Nat
    scaleFromCarrier : Carrier B → LimitCarrier

    continuum-compatible :
      ∀ x →
      limitObservable (scaleToLimit (continuumLift B x))
        ≡
      observableProjection (observableOf B x)

    continuum-cone-compatible :
      ∀ x →
      coneWitness B x →
      limitCone (scaleToLimit (continuumLift B x))

    continuum-mdl-compatible :
      ∀ x →
      limitMdl (scaleToLimit (continuumLift B x)) ≡ mdlLevel B x

    scale-lift-compatible :
      ∀ x →
      scaleFromCarrier x ≡ scaleToLimit (continuumLift B x)

    scale-preserve-evolve :
      ∀ x →
      scaleFromCarrier (evolve B x) ≡ scaleFromCarrier x

    scale-preserve-coarse :
      ∀ x →
      scaleFromCarrier (coarse B x) ≡ scaleFromCarrier x

    scale-preserve-offset :
      ∀ x →
      scaleFromCarrier (offset B x) ≡ scaleFromCarrier x

open ContinuumWitness public

record SignatureLockWitness
  (B : AbstractGaugeMatterBundle) : Setω where
  field
    SignatureClass : Set
    signatureOf : Carrier B → SignatureClass
    lockedSignature : SignatureClass

    signature-evolve :
      ∀ x →
      admissible B x ≡ true →
      signatureOf x ≡ signatureOf (evolve B x)

    signature-coarse :
      ∀ x →
      admissible B x ≡ true →
      signatureOf x ≡ signatureOf (coarse B x)

    signature-locked :
      ∀ x →
      admissible B x ≡ true →
      signatureOf x ≡ lockedSignature

open SignatureLockWitness public

record ObservableTransportWitness
  (B : AbstractGaugeMatterBundle) : Setω where
  field
    TargetCarrier : Set
    observeTarget : TargetCarrier → Observable B
    transport : Carrier B → TargetCarrier

    transport-sound :
      ∀ x →
      admissible B x ≡ true →
      observableOf B x ≡ observeTarget (transport x)

open ObservableTransportWitness public

record TransportedProjectionDeltaWitness
  (B : AbstractGaugeMatterBundle) : Setω where
  field
    transportW : ObservableTransportWitness B
    admissibleT : TargetCarrier transportW → Set
    projectAT : TargetCarrier transportW → TargetCarrier transportW
    projectBT : TargetCarrier transportW → TargetCarrier transportW
    coneT : TargetCarrier transportW → Set

    cone-projectAT :
      ∀ x →
      admissibleT x →
      coneT x →
      coneT (projectAT x)

    cone-projectBT :
      ∀ x →
      admissibleT x →
      coneT x →
      coneT (projectBT x)

    universalityT :
      ∀ x →
      admissibleT x →
      observeTarget transportW (projectAT x)
        ≡
      observeTarget transportW (projectBT x)

open TransportedProjectionDeltaWitness public

record GaugeMatterRecoveryTheorem
  (B : AbstractGaugeMatterBundle) : Setω where
  field
    natural : NaturalDynamicsWitness B
    conserved : ConservedObservableWitness B
    continuum : ContinuumWitness B
    signature : SignatureLockWitness B
    transport : ObservableTransportWitness B
    transportedProjectionDelta : TransportedProjectionDeltaWitness B
    transportedProjectionDeltaAlt : TransportedProjectionDeltaWitness B

    gauge-recovered :
      ∀ x →
      admissible B x ≡ true →
      pickGauge B x ≡ GGC.SU3×SU2×U1

    observable-recovery :
      ∀ x →
      admissible B x ≡ true →
      observableOf B (coarse B (evolve B x))
        ≡ observableOf B (offset B (coarse B x))

open GaugeMatterRecoveryTheorem public

toObservableRGOffsetUniversality :
  (B : AbstractGaugeMatterBundle) →
  GaugeMatterRecoveryTheorem B →
  RGOI.ObservableRGOffsetUniversality
    (Carrier B)
    (Observable B)
    _≡_
toObservableRGOffsetUniversality B thm =
  record
    { admissibleO = λ x → admissible B x ≡ true
    ; evolveA = evolve B
    ; coarseA = coarse B
    ; evolveB = coarse B
    ; coarseB = offset B
    ; observeO = observableOf B
    ; offset = λ x → x
    ; universalityOffset = GaugeMatterRecoveryTheorem.observable-recovery thm
    }

toProjectionDeltaCompatibility :
  (B : AbstractGaugeMatterBundle) →
  GaugeMatterRecoveryTheorem B →
  RGOI.ProjectionDeltaCompatibility
    (Carrier B)
    (Observable B)
    _≡_
toProjectionDeltaCompatibility B thm =
  record
    { admissibleΔ = λ x → admissible B x ≡ true
    ; projectA = λ x → coarse B (evolve B x)
    ; projectB = λ x → offset B (coarse B x)
    ; observeΔ = observableOf B
    ; coneΔ = coneWitness B
    ; cone-projectA =
        λ x ax cx →
          NaturalDynamicsWitness.cone-preserved-coarse
            (GaugeMatterRecoveryTheorem.natural thm)
            (evolve B x)
            (NaturalDynamicsWitness.cone-preserved-evolve
              (GaugeMatterRecoveryTheorem.natural thm)
              x
              cx)
    ; cone-projectB =
        λ x ax cx →
          NaturalDynamicsWitness.cone-preserved-offset
            (GaugeMatterRecoveryTheorem.natural thm)
            (coarse B x)
            (NaturalDynamicsWitness.cone-preserved-coarse
              (GaugeMatterRecoveryTheorem.natural thm)
              x
              cx)
    ; universalityΔ = GaugeMatterRecoveryTheorem.observable-recovery thm
    }

toTransportedProjectionDeltaCompatibility :
  (B : AbstractGaugeMatterBundle) →
  (w : TransportedProjectionDeltaWitness B) →
  RGOI.ProjectionDeltaCompatibility
    (TargetCarrier (transportW w))
    (Observable B)
    _≡_
toTransportedProjectionDeltaCompatibility B w =
  record
    { admissibleΔ = admissibleT w
    ; projectA = projectAT w
    ; projectB = projectBT w
    ; observeΔ = observeTarget (transportW w)
    ; coneΔ = coneT w
    ; cone-projectA = cone-projectAT w
    ; cone-projectB = cone-projectBT w
    ; universalityΔ = universalityT w
    }

toRecoveryTransportedProjectionDeltaCompatibility :
  (B : AbstractGaugeMatterBundle) →
  (thm : GaugeMatterRecoveryTheorem B) →
  RGOI.ProjectionDeltaCompatibility
    (TargetCarrier
      (TransportedProjectionDeltaWitness.transportW
        (GaugeMatterRecoveryTheorem.transportedProjectionDelta thm)))
    (Observable B)
    _≡_
toRecoveryTransportedProjectionDeltaCompatibility B thm =
  toTransportedProjectionDeltaCompatibility
    B
    (GaugeMatterRecoveryTheorem.transportedProjectionDelta thm)

toRecoveryTransportedProjectionDeltaCompatibilityAlt :
  (B : AbstractGaugeMatterBundle) →
  (thm : GaugeMatterRecoveryTheorem B) →
  RGOI.ProjectionDeltaCompatibility
    (TargetCarrier
      (TransportedProjectionDeltaWitness.transportW
        (GaugeMatterRecoveryTheorem.transportedProjectionDeltaAlt thm)))
    (Observable B)
    _≡_
toRecoveryTransportedProjectionDeltaCompatibilityAlt B thm =
  toTransportedProjectionDeltaCompatibility
    B
    (GaugeMatterRecoveryTheorem.transportedProjectionDeltaAlt thm)

fromCanonicalConstraintGaugePackage :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  (GaugeFiber MatterField Observable ContinuumField : Set) →
  (evolve coarse offset : CCGP.Carrier P → CCGP.Carrier P) →
  (coneWitness : CCGP.Carrier P → Set) →
  (mdlLevel : CCGP.Carrier P → Nat) →
  (gaugeAction : GaugeFiber → CCGP.Carrier P → CCGP.Carrier P) →
  (matterOf : CCGP.Carrier P → MatterField) →
  (observableOf : CCGP.Carrier P → Observable) →
  (continuumLift : CCGP.Carrier P → ContinuumField) →
  AbstractGaugeMatterBundle
fromCanonicalConstraintGaugePackage
  P GaugeFiber MatterField Observable ContinuumField
  evolve coarse offset coneWitness mdlLevel gaugeAction matterOf
  observableOf continuumLift =
  record
    { Carrier = CCGP.Carrier P
    ; GaugeFiber = GaugeFiber
    ; MatterField = MatterField
    ; Observable = Observable
    ; ContinuumField = ContinuumField
    ; evolve = evolve
    ; coarse = coarse
    ; offset = offset
    ; admissible = CCGP.admissible P
    ; coneWitness = coneWitness
    ; mdlLevel = mdlLevel
    ; gaugeAction = gaugeAction
    ; matterOf = matterOf
    ; observableOf = observableOf
    ; continuumLift = continuumLift
    ; pickGauge = CCGP.pickGauge P
    }
