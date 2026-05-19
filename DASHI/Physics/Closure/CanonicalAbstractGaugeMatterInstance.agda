module DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Product using (_×_; _,_)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Algebra.Trit using (pos; zer)
open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ConeTimeIsotropy as CTI using (Signature)
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Geometry.Signature31Lock as S31L
open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftExecutionInvariantCore as SEIC
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.PressureHamiltonJacobiShiftInstance as PHJSI
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import Ontology.Hecke.Scan as HS
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

  CanonicalGaugeFiber : Set
  CanonicalGaugeFiber = GGC.Gauge

  CanonicalRGObservable : Set
  CanonicalRGObservable = RGOI.RGObservable SRGOI.ShiftBasin SRGOI.ShiftMotif

  CanonicalMatterField : Set
  CanonicalMatterField = GGC.Gauge × CanonicalRGObservable

  CanonicalObservable : Set
  CanonicalObservable = GGC.Gauge × CanonicalRGObservable

  CanonicalContinuumField : Set
  CanonicalContinuumField = GGC.Gauge × CanonicalRGObservable

  CanonicalEigenShadow : Set
  CanonicalEigenShadow = Nat × Nat

  CanonicalContinuumObservable : Set
  CanonicalContinuumObservable =
    GGC.Gauge × SRGOI.ShiftBasin × Nat × SRGOI.ShiftMotif × CanonicalEigenShadow

canonicalSignature : HS.Sig15
canonicalSignature = SEIC.canonicalShiftSignature

canonicalEigenProfile : PHEM.EigenProfile
canonicalEigenProfile = SEIC.canonicalShiftEigenProfile

canonicalRGObservable : CanonicalRGObservable
canonicalRGObservable =
  RGOI.RGObservableSurface.observe
    SRGOI.shiftRGSurface
    SLEI.canonicalShiftStateWitness

identityCarrier :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage →
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage
identityCarrier x = x

canonicalGaugeAction :
  CanonicalGaugeFiber →
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage →
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage
canonicalGaugeAction _ x = x

CanonicalShiftCarrier : Set
CanonicalShiftCarrier =
  EC.Contract.State (SLEI.shiftContract {suc zero} {suc (suc (suc zero))})

canonicalShiftRep₀ : CanonicalShiftCarrier
canonicalShiftRep₀ = pos ∷ zer ∷ zer ∷ zer ∷ []

canonicalShiftRep₁ : CanonicalShiftCarrier
canonicalShiftRep₁ = zer ∷ pos ∷ zer ∷ zer ∷ []

canonicalShiftRep₂ : CanonicalShiftCarrier
canonicalShiftRep₂ = zer ∷ zer ∷ pos ∷ zer ∷ []

canonicalTransportState :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → CanonicalShiftCarrier
canonicalTransportState CI.CR = canonicalShiftRep₀
canonicalTransportState CI.CP = canonicalShiftRep₁
canonicalTransportState CI.CC = canonicalShiftRep₂

canonicalRGObservableOf :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → CanonicalRGObservable
canonicalRGObservableOf x =
  RGOI.RGObservableSurface.observe
    SRGOI.shiftRGSurface
    (canonicalTransportState x)

canonicalConeWitness :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → Set
canonicalConeWitness _ = ⊤

canonicalMdlLevel :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → Nat
canonicalMdlLevel x =
  RGOI.RGObservable.mdlLevel (canonicalRGObservableOf x)

canonicalBasinLevel :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → SRGOI.ShiftBasin
canonicalBasinLevel x =
  RGOI.RGObservable.basinLabel (canonicalRGObservableOf x)

canonicalSignatureLevel :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → HS.Sig15
canonicalSignatureLevel x =
  RGOI.RGObservable.heckeSignature (canonicalRGObservableOf x)

canonicalEigenLevel :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → PHEM.EigenProfile
canonicalEigenLevel x =
  RGOI.RGObservable.eigenSummary (canonicalRGObservableOf x)

canonicalMotifLevel :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → SRGOI.ShiftMotif
canonicalMotifLevel x =
  RGOI.RGObservable.motifClass (canonicalRGObservableOf x)

canonicalEigenShadowLevel :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → CanonicalEigenShadow
canonicalEigenShadowLevel x =
  ( PHEM.EigenProfile.earth (canonicalEigenLevel x)
  , PHEM.EigenProfile.hub (canonicalEigenLevel x)
  )

canonicalMatterOf :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → CanonicalMatterField
canonicalMatterOf x =
  (CCGP.pickGauge PGCT.canonicalConstraintGaugePackage x , canonicalRGObservableOf x)

canonicalObservableOf :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → CanonicalObservable
canonicalObservableOf x =
  (CCGP.pickGauge PGCT.canonicalConstraintGaugePackage x , canonicalRGObservableOf x)

canonicalContinuumLift :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → CanonicalContinuumField
canonicalContinuumLift x =
  (CCGP.pickGauge PGCT.canonicalConstraintGaugePackage x , canonicalRGObservableOf x)

canonicalClosureDynamics :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage →
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage
canonicalClosureDynamics x =
  CCGP._[_,]_ PGCT.canonicalConstraintGaugePackage CI.CR x

canonicalMotifPreserved :
  ∀ x →
  canonicalMotifLevel x ≡ canonicalMotifLevel (canonicalClosureDynamics x)
canonicalMotifPreserved CI.CR = refl
canonicalMotifPreserved CI.CP = refl
canonicalMotifPreserved CI.CC = refl

canonicalEigenShadowPreserved :
  ∀ x →
  canonicalEigenShadowLevel x ≡ canonicalEigenShadowLevel (canonicalClosureDynamics x)
canonicalEigenShadowPreserved CI.CR = refl
canonicalEigenShadowPreserved CI.CP = refl
canonicalEigenShadowPreserved CI.CC = refl

canonicalEigenLevel-CP-obstructed :
  canonicalEigenLevel CI.CP ≢ canonicalEigenLevel (canonicalClosureDynamics CI.CP)
canonicalEigenLevel-CP-obstructed ()

CanonicalConservedCharge : Set
CanonicalConservedCharge =
  GGC.Gauge × SRGOI.ShiftBasin × Nat × SRGOI.ShiftMotif × CanonicalEigenShadow

CanonicalCoarseConservedCharge : Set
CanonicalCoarseConservedCharge =
  GGC.Gauge × SRGOI.ShiftBasin × SRGOI.ShiftMotif

canonicalConservedChargeOf :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → CanonicalConservedCharge
canonicalConservedChargeOf x =
  ( CCGP.pickGauge PGCT.canonicalConstraintGaugePackage x
  , canonicalBasinLevel x
  , canonicalMdlLevel x
  , canonicalMotifLevel x
  , canonicalEigenShadowLevel x
  )

canonicalCoarseConservedChargeOf :
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage → CanonicalCoarseConservedCharge
canonicalCoarseConservedChargeOf x =
  ( CCGP.pickGauge PGCT.canonicalConstraintGaugePackage x
  , canonicalBasinLevel x
  , canonicalMotifLevel x
  )

canonicalConservedChargePreserved :
  ∀ x →
  canonicalConservedChargeOf x ≡ canonicalConservedChargeOf (canonicalClosureDynamics x)
canonicalConservedChargePreserved CI.CR = refl
canonicalConservedChargePreserved CI.CP
  rewrite canonicalMotifPreserved CI.CP
  = refl
canonicalConservedChargePreserved CI.CC
  rewrite canonicalMotifPreserved CI.CC
  = refl

projectTransportedCoarseCharge :
  CanonicalObservable → CanonicalCoarseConservedCharge
projectTransportedCoarseCharge (g , o) =
  ( g
  , RGOI.RGObservable.basinLabel o
  , RGOI.RGObservable.motifClass o
  )

projectTransportedShiftCoarseCharge :
  CanonicalShiftCarrier → CanonicalCoarseConservedCharge
projectTransportedShiftCoarseCharge x =
  projectTransportedCoarseCharge
    (GGC.SU3×SU2×U1 , RGOI.RGObservableSurface.observe SRGOI.shiftRGSurface x)

canonicalClosureCoarseCharge-to-stepSchedule :
  ∀ x →
  canonicalCoarseConservedChargeOf (canonicalClosureDynamics x)
    ≡
  projectTransportedShiftCoarseCharge
    (SRGOI.shiftCoarse
      (EC.Contract.step
        (SLEI.shiftContract {suc zero} {suc (suc (suc zero))})
        (canonicalTransportState x)))
canonicalClosureCoarseCharge-to-stepSchedule CI.CR = refl
canonicalClosureCoarseCharge-to-stepSchedule CI.CP = refl
canonicalClosureCoarseCharge-to-stepSchedule CI.CC = refl

canonicalClosureCoarseCharge-to-schedule :
  ∀ x →
  SRGOI.shiftRGAdmissible (canonicalTransportState x) →
  canonicalCoarseConservedChargeOf (canonicalClosureDynamics x)
    ≡
  projectTransportedShiftCoarseCharge
    (SRGOI.shiftCoarseAlt (canonicalTransportState x))
canonicalClosureCoarseCharge-to-schedule x ax =
  trans
    (canonicalClosureCoarseCharge-to-stepSchedule x)
    (cong
      projectTransportedShiftCoarseCharge
      (sym (SRGOI.shiftCoarseAlt≡shiftCoarse (canonicalTransportState x))))

canonicalCoarseConservedChargePreservedLocal :
  ∀ y →
  canonicalCoarseConservedChargeOf y
    ≡
  canonicalCoarseConservedChargeOf (canonicalClosureDynamics y)
canonicalCoarseConservedChargePreservedLocal CI.CR = refl
canonicalCoarseConservedChargePreservedLocal CI.CP = refl
canonicalCoarseConservedChargePreservedLocal CI.CC = refl

canonicalSourceCoarseCharge-to-schedule :
  ∀ x →
  SRGOI.shiftRGAdmissible (canonicalTransportState x) →
  canonicalCoarseConservedChargeOf x
    ≡
  projectTransportedShiftCoarseCharge
    (SRGOI.shiftCoarseAlt (canonicalTransportState x))
canonicalSourceCoarseCharge-to-schedule x ax =
  trans
    (canonicalCoarseConservedChargePreservedLocal x)
    (canonicalClosureCoarseCharge-to-schedule x ax)

canonicalCoarseConservedChargePreserved :
  ∀ x →
  SRGOI.shiftRGAdmissible (canonicalTransportState x) →
  canonicalCoarseConservedChargeOf x
    ≡
  canonicalCoarseConservedChargeOf (canonicalClosureDynamics x)
canonicalCoarseConservedChargePreserved x ax =
  trans
    (canonicalSourceCoarseCharge-to-schedule x ax)
    (sym (canonicalClosureCoarseCharge-to-schedule x ax))

canonicalAbstractGaugeMatterBundle : AGMB.AbstractGaugeMatterBundle
canonicalAbstractGaugeMatterBundle =
  AGMB.fromCanonicalConstraintGaugePackage
    PGCT.canonicalConstraintGaugePackage
    CanonicalGaugeFiber
    CanonicalMatterField
    CanonicalObservable
    CanonicalContinuumField
    canonicalClosureDynamics
    canonicalClosureDynamics
    canonicalClosureDynamics
    canonicalConeWitness
    canonicalMdlLevel
    canonicalGaugeAction
    canonicalMatterOf
    canonicalObservableOf
    canonicalContinuumLift

canonicalNaturalDynamicsWitness :
  AGMB.NaturalDynamicsWitness canonicalAbstractGaugeMatterBundle
canonicalNaturalDynamicsWitness =
  record
    { admissible-evolve = λ _ ax → ax
    ; admissible-coarse = λ _ ax → ax
    ; admissible-offset = λ _ ax → ax
    ; mdl-descent = λ
        { CI.CR → refl
        ; CI.CP → refl
        ; CI.CC → refl
        }
    ; coarse-offset-commute = λ _ → refl
    ; cone-preserved-evolve = λ _ cx → cx
    ; cone-preserved-coarse = λ _ cx → cx
    ; cone-preserved-offset = λ _ cx → cx
    }

canonicalConservedObservableWitness :
  AGMB.ConservedObservableWitness canonicalAbstractGaugeMatterBundle
canonicalConservedObservableWitness =
  record
    { Charge = CanonicalCoarseConservedCharge
    ; chargeOf = canonicalCoarseConservedChargeOf
    ; charge-evolve = λ x _ → canonicalCoarseConservedChargePreservedLocal x
    ; charge-coarse = λ x _ → canonicalCoarseConservedChargePreservedLocal x
    ; observable-gauge-invariant = λ _ _ → refl
    }

record CanonicalTransportBackedNaturalCoarseTheorem : Setω where
  field
    natural :
      AGMB.NaturalDynamicsWitness canonicalAbstractGaugeMatterBundle
    conserved :
      AGMB.ConservedObservableWitness canonicalAbstractGaugeMatterBundle
    source-coarse-to-schedule :
      ∀ x →
      SRGOI.shiftRGAdmissible (canonicalTransportState x) →
      canonicalCoarseConservedChargeOf x
        ≡
      projectTransportedShiftCoarseCharge
        (SRGOI.shiftCoarseAlt (canonicalTransportState x))
    evolve-coarse-to-schedule :
      ∀ x →
      SRGOI.shiftRGAdmissible (canonicalTransportState x) →
      canonicalCoarseConservedChargeOf (canonicalClosureDynamics x)
        ≡
      projectTransportedShiftCoarseCharge
        (SRGOI.shiftCoarseAlt (canonicalTransportState x))
    shift-local-action :
      DDSI.ShiftLeastActionLaw
    shift-hamilton-jacobi :
      PHJSI.ShiftHJPresentation

canonicalTransportBackedNaturalCoarseTheorem :
  CanonicalTransportBackedNaturalCoarseTheorem
canonicalTransportBackedNaturalCoarseTheorem =
  record
    { natural = canonicalNaturalDynamicsWitness
    ; conserved = canonicalConservedObservableWitness
    ; source-coarse-to-schedule = canonicalSourceCoarseCharge-to-schedule
    ; evolve-coarse-to-schedule = canonicalClosureCoarseCharge-to-schedule
    ; shift-local-action = DDSI.shiftLeastActionWitness
    ; shift-hamilton-jacobi = PHJSI.shiftHamiltonJacobiWitness
    }

canonicalContinuumWitness :
  AGMB.ContinuumWitness canonicalAbstractGaugeMatterBundle
canonicalContinuumWitness =
  record
    { LimitCarrier = CanonicalContinuumObservable
    ; LimitObservable = CanonicalContinuumObservable
    ; scaleToLimit =
        λ { (g , o) →
            ( g
            , RGOI.RGObservable.basinLabel o
            , RGOI.RGObservable.mdlLevel o
            , RGOI.RGObservable.motifClass o
            , ( PHEM.EigenProfile.earth (RGOI.RGObservable.eigenSummary o)
              , PHEM.EigenProfile.hub (RGOI.RGObservable.eigenSummary o)
              )
            )
          }
    ; limitObservable = λ x → x
    ; observableProjection =
        λ { (g , o) →
            ( g
            , RGOI.RGObservable.basinLabel o
            , RGOI.RGObservable.mdlLevel o
            , RGOI.RGObservable.motifClass o
            , ( PHEM.EigenProfile.earth (RGOI.RGObservable.eigenSummary o)
              , PHEM.EigenProfile.hub (RGOI.RGObservable.eigenSummary o)
              )
            )
          }
    ; limitCone = λ _ → ⊤
    ; limitMdl = λ { (_ , _ , mdl , _ , _) → mdl }
    ; scaleFromCarrier = canonicalConservedChargeOf
    ; continuum-compatible = λ _ → refl
    ; continuum-cone-compatible = λ _ _ → tt
    ; continuum-mdl-compatible = λ _ → refl
    ; scale-lift-compatible = λ _ → refl
    ; scale-preserve-evolve = λ x → sym (canonicalConservedChargePreserved x)
    ; scale-preserve-coarse = λ x → sym (canonicalConservedChargePreserved x)
    ; scale-preserve-offset = λ x → sym (canonicalConservedChargePreserved x)
    }

canonicalTransportObservable :
  CanonicalShiftCarrier → CanonicalObservable
canonicalTransportObservable x =
  (GGC.SU3×SU2×U1 , RGOI.RGObservableSurface.observe SRGOI.shiftRGSurface x)

canonicalTransportObservable-sound :
  ∀ x →
  canonicalTransportObservable (canonicalTransportState x)
    ≡
  (GGC.SU3×SU2×U1 , canonicalRGObservableOf x)
canonicalTransportObservable-sound _ = refl

canonicalObservableTransportWitness :
  AGMB.ObservableTransportWitness canonicalAbstractGaugeMatterBundle
canonicalObservableTransportWitness =
  record
    { TargetCarrier = CanonicalShiftCarrier
    ; observeTarget = canonicalTransportObservable
    ; transport = canonicalTransportState
    ; transport-sound =
        λ x ax →
          cong (λ g → (g , canonicalRGObservableOf x))
            (CCGP.uniqueGaugeOnAdmissible
              PGCT.canonicalConstraintGaugePackage
              x
              ax)
    }

canonicalSignatureLockAxioms : S31L.SignatureLockAxioms
canonicalSignatureLockAxioms =
  record
    { dim4 = tt
    ; oneTime = tt
    ; threeSpace = tt
    ; coneArrow = tt
    ; isotropy = tt
    }

canonicalSignatureLockWitness :
  AGMB.SignatureLockWitness canonicalAbstractGaugeMatterBundle
canonicalSignatureLockWitness =
  record
    { SignatureClass = Signature
    ; signatureOf = λ _ → S31L.signatureLock canonicalSignatureLockAxioms
    ; lockedSignature = S31L.signatureLock canonicalSignatureLockAxioms
    ; signature-evolve = λ _ _ → refl
    ; signature-coarse = λ _ _ → refl
    ; signature-locked = λ _ _ → refl
    }

canonicalBundleProjectionDeltaCompatibilityRG :
  RGOI.ProjectionDeltaCompatibility
    (AGMB.Carrier canonicalAbstractGaugeMatterBundle)
    CanonicalRGObservable
    (RGOI.RGCoarseWitnessPackage.Observable≈ SRGOI.shiftRGWitnessPackage)
canonicalBundleProjectionDeltaCompatibilityRG =
  record
    { admissibleΔ = λ x → AGMB.admissible canonicalAbstractGaugeMatterBundle x ≡ true
    ; projectA =
        λ x →
          AGMB.coarse canonicalAbstractGaugeMatterBundle
            (AGMB.evolve canonicalAbstractGaugeMatterBundle x)
    ; projectB =
        λ x →
          AGMB.offset canonicalAbstractGaugeMatterBundle
            (AGMB.coarse canonicalAbstractGaugeMatterBundle x)
    ; observeΔ = canonicalRGObservableOf
    ; coneΔ = AGMB.coneWitness canonicalAbstractGaugeMatterBundle
    ; cone-projectA =
        λ x _ cx →
          AGMB.NaturalDynamicsWitness.cone-preserved-coarse
            canonicalNaturalDynamicsWitness
            (AGMB.evolve canonicalAbstractGaugeMatterBundle x)
            (AGMB.NaturalDynamicsWitness.cone-preserved-evolve
              canonicalNaturalDynamicsWitness
              x
              cx)
    ; cone-projectB =
        λ x _ cx →
          AGMB.NaturalDynamicsWitness.cone-preserved-offset
            canonicalNaturalDynamicsWitness
            (AGMB.coarse canonicalAbstractGaugeMatterBundle x)
            (AGMB.NaturalDynamicsWitness.cone-preserved-coarse
              canonicalNaturalDynamicsWitness
              x
              cx)
    ; universalityΔ =
        λ x _ →
          SRGOI.shiftObservableQuotient
            _
            _
            refl
            refl
            refl
            refl
            refl
    }

canonicalTransportedProjectionDeltaWitness :
  AGMB.TransportedProjectionDeltaWitness canonicalAbstractGaugeMatterBundle
canonicalTransportedProjectionDeltaWitness =
  record
    { transportW = canonicalObservableTransportWitness
    ; admissibleT = SRGOI.shiftRGAdmissible
    ; projectAT =
        λ x →
          SRGOI.shiftCoarse
            (EC.Contract.step
              (SLEI.shiftContract {suc zero} {suc (suc (suc zero))})
              x)
    ; projectBT = SRGOI.shiftCoarseAlt
    ; coneT = SRGOI.ShiftConeCompatible
    ; cone-projectAT = SRGOI.shiftConePreservedLeft
    ; cone-projectBT = λ x _ cx → SRGOI.shiftConeTransportCoarseAlt x cx
    ; universalityT =
        λ x _ →
          cong canonicalTransportObservable
            (sym (SRGOI.shiftCoarseAlt≡shiftCoarse x))
    }

canonicalTransportedProjectionDeltaCompatibility :
  RGOI.ProjectionDeltaCompatibility
    CanonicalShiftCarrier
    CanonicalObservable
    _≡_
canonicalTransportedProjectionDeltaCompatibility =
  AGMB.toTransportedProjectionDeltaCompatibility
    canonicalAbstractGaugeMatterBundle
    canonicalTransportedProjectionDeltaWitness

canonicalTransportedProjectionDeltaWitnessAlt :
  AGMB.TransportedProjectionDeltaWitness canonicalAbstractGaugeMatterBundle
canonicalTransportedProjectionDeltaWitnessAlt =
  record
    { transportW = canonicalObservableTransportWitness
    ; admissibleT = SRGOI.shiftRGAdmissible
    ; projectAT =
        λ x →
          SRGOI.shiftCoarseAlt
            (EC.Contract.step
              (SLEI.shiftContract {suc zero} {suc (suc (suc zero))})
              x)
    ; projectBT =
        λ x →
          EC.Contract.step
            (SLEI.shiftContract {suc zero} {suc (suc (suc zero))})
            (SRGOI.shiftCoarseAlt x)
    ; coneT = SRGOI.ShiftConeCompatible
    ; cone-projectAT = SRGOI.shiftConePreservedLeftAlt
    ; cone-projectBT =
        λ x _ cx →
          SRGOI.shiftConeTransportStep
            (SRGOI.shiftCoarseAlt x)
            (SRGOI.shiftConeTransportCoarseAlt x cx)
    ; universalityT =
        λ x _ →
          cong canonicalTransportObservable
            (SRGOI.shiftCoarseAltStep-commute x)
    }

canonicalTransportedProjectionDeltaCompatibilityAlt :
  RGOI.ProjectionDeltaCompatibility
    CanonicalShiftCarrier
    CanonicalObservable
    _≡_
canonicalTransportedProjectionDeltaCompatibilityAlt =
  AGMB.toTransportedProjectionDeltaCompatibility
    canonicalAbstractGaugeMatterBundle
    canonicalTransportedProjectionDeltaWitnessAlt

canonicalGaugeMatterRecoveryTheorem :
  AGMB.GaugeMatterRecoveryTheorem canonicalAbstractGaugeMatterBundle
canonicalGaugeMatterRecoveryTheorem =
  record
    { natural = canonicalNaturalDynamicsWitness
    ; conserved = canonicalConservedObservableWitness
    ; continuum = canonicalContinuumWitness
    ; signature = canonicalSignatureLockWitness
    ; transport = canonicalObservableTransportWitness
    ; transportedProjectionDelta =
        canonicalTransportedProjectionDeltaWitness
    ; transportedProjectionDeltaAlt =
        canonicalTransportedProjectionDeltaWitnessAlt
    ; gauge-recovered =
        CCGP.uniqueGaugeOnAdmissible
          PGCT.canonicalConstraintGaugePackage
    ; observable-recovery = λ _ _ → refl
    }

canonicalBundleOffsetUniversality :
  RGOI.ObservableRGOffsetUniversality
    (AGMB.Carrier canonicalAbstractGaugeMatterBundle)
    (AGMB.Observable canonicalAbstractGaugeMatterBundle)
    _≡_
canonicalBundleOffsetUniversality =
  AGMB.toObservableRGOffsetUniversality
    canonicalAbstractGaugeMatterBundle
    canonicalGaugeMatterRecoveryTheorem

canonicalBundleProjectionDeltaCompatibility :
  RGOI.ProjectionDeltaCompatibility
    (AGMB.Carrier canonicalAbstractGaugeMatterBundle)
    (AGMB.Observable canonicalAbstractGaugeMatterBundle)
    _≡_
canonicalBundleProjectionDeltaCompatibility =
  AGMB.toProjectionDeltaCompatibility
    canonicalAbstractGaugeMatterBundle
    canonicalGaugeMatterRecoveryTheorem

canonicalRecoveryTransportedProjectionDeltaCompatibility :
  RGOI.ProjectionDeltaCompatibility
    CanonicalShiftCarrier
    CanonicalObservable
    _≡_
canonicalRecoveryTransportedProjectionDeltaCompatibility =
  AGMB.toRecoveryTransportedProjectionDeltaCompatibility
    canonicalAbstractGaugeMatterBundle
    canonicalGaugeMatterRecoveryTheorem

canonicalRecoveryTransportedProjectionDeltaCompatibilityAlt :
  RGOI.ProjectionDeltaCompatibility
    CanonicalShiftCarrier
    CanonicalObservable
    _≡_
canonicalRecoveryTransportedProjectionDeltaCompatibilityAlt =
  AGMB.toRecoveryTransportedProjectionDeltaCompatibilityAlt
    canonicalAbstractGaugeMatterBundle
    canonicalGaugeMatterRecoveryTheorem
