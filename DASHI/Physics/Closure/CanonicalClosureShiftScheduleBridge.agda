module DASHI.Physics.Closure.CanonicalClosureShiftScheduleBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CA
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Execution.Contract as EC

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

  ShiftC = SLEI.shiftContract {1} {3}

  CanonicalCarrier : Set
  CanonicalCarrier = CCGP.Carrier PGCT.canonicalConstraintGaugePackage

-- Minimal concrete bridge already available:
-- on transported closure states, the two shift-side schedule branches have
-- equal transported observables whenever shift-side admissibility is provided.
closureTransportedScheduleSurface :
  ∀ x →
  SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
  CA.canonicalTransportObservable
    (SRGOI.shiftCoarse
      (EC.Contract.step ShiftC (CA.canonicalTransportState x)))
    ≡
  CA.canonicalTransportObservable
    (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x))
closureTransportedScheduleSurface x ax =
  AGMB.TransportedProjectionDeltaWitness.universalityT
    CA.canonicalTransportedProjectionDeltaWitness
    (CA.canonicalTransportState x)
    ax
  where
  open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB

-- Strong bridge shape that would identify closure dynamics with a
-- schedule-side raw-eigen channel after transport.
record RawEigenClosureShiftScheduleBridge : Set where
  field
    closure-to-schedule :
      ∀ x →
      CA.canonicalRGObservableOf (CA.canonicalClosureDynamics x)
        ≡
      RGOI.RGObservableSurface.observe
        SRGOI.shiftRGSurface
        (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x))

    schedule-to-source-eigen :
      ∀ x →
      RGOI.RGObservable.eigenSummary
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x)))
        ≡
      CA.canonicalEigenLevel x

projectedScheduleCharge :
  EC.Contract.State ShiftC → CA.CanonicalConservedCharge
projectedScheduleCharge x =
  ( GGC.SU3×SU2×U1
  , RGOI.RGObservable.basinLabel o
  , RGOI.RGObservable.mdlLevel o
  , RGOI.RGObservable.motifClass o
  , ( PHEM.EigenProfile.earth (RGOI.RGObservable.eigenSummary o)
    , PHEM.EigenProfile.hub (RGOI.RGObservable.eigenSummary o)
    )
  )
  where
  open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM

  o : RGOI.RGObservable SRGOI.ShiftBasin SRGOI.ShiftMotif
  o = RGOI.RGObservableSurface.observe SRGOI.shiftRGSurface x

CanonicalProjectedScheduleObservable : Set
CanonicalProjectedScheduleObservable =
  GGC.Gauge × SRGOI.ShiftBasin × SRGOI.ShiftMotif × (Nat × Nat)

CanonicalMotifScheduleObservable : Set
CanonicalMotifScheduleObservable =
  GGC.Gauge × SRGOI.ShiftBasin × SRGOI.ShiftMotif

closureProjectedObservable :
  CanonicalCarrier → CanonicalProjectedScheduleObservable
closureProjectedObservable x =
  ( CCGP.pickGauge PGCT.canonicalConstraintGaugePackage x
  , CA.canonicalBasinLevel x
  , CA.canonicalMotifLevel x
  , CA.canonicalEigenShadowLevel x
  )

projectObservableCharge :
  (GGC.Gauge × RGOI.RGObservable SRGOI.ShiftBasin SRGOI.ShiftMotif) →
  CA.CanonicalConservedCharge
projectObservableCharge (g , o) =
  ( g
  , RGOI.RGObservable.basinLabel o
  , RGOI.RGObservable.mdlLevel o
  , RGOI.RGObservable.motifClass o
  , ( PHEM.EigenProfile.earth (RGOI.RGObservable.eigenSummary o)
    , PHEM.EigenProfile.hub (RGOI.RGObservable.eigenSummary o)
    )
  )
  where
  open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM

projectObservableNoMdl :
  (GGC.Gauge × RGOI.RGObservable SRGOI.ShiftBasin SRGOI.ShiftMotif) →
  CanonicalProjectedScheduleObservable
projectObservableNoMdl (g , o) =
  ( g
  , RGOI.RGObservable.basinLabel o
  , RGOI.RGObservable.motifClass o
  , ( PHEM.EigenProfile.earth (RGOI.RGObservable.eigenSummary o)
    , PHEM.EigenProfile.hub (RGOI.RGObservable.eigenSummary o)
    )
  )
  where
  open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM

closureMotifObservable :
  CanonicalCarrier → CanonicalMotifScheduleObservable
closureMotifObservable x =
  ( CCGP.pickGauge PGCT.canonicalConstraintGaugePackage x
  , CA.canonicalBasinLevel x
  , CA.canonicalMotifLevel x
  )

projectObservableMotif :
  (GGC.Gauge × RGOI.RGObservable SRGOI.ShiftBasin SRGOI.ShiftMotif) →
  CanonicalMotifScheduleObservable
projectObservableMotif (g , o) =
  ( g
  , RGOI.RGObservable.basinLabel o
  , RGOI.RGObservable.motifClass o
  )

closureProjectedToScheduleLeft-CP-obstructed :
  closureProjectedObservable (CA.canonicalClosureDynamics CI.CP)
    ≢
  projectObservableNoMdl
    (CA.canonicalTransportObservable
      (SRGOI.shiftCoarse
        (EC.Contract.step ShiftC (CA.canonicalTransportState CI.CP))))
closureProjectedToScheduleLeft-CP-obstructed ()

closureMotifToScheduleLeft :
  ∀ x →
  closureMotifObservable (CA.canonicalClosureDynamics x)
    ≡
  projectObservableMotif
    (CA.canonicalTransportObservable
      (SRGOI.shiftCoarse
        (EC.Contract.step ShiftC (CA.canonicalTransportState x))))
closureMotifToScheduleLeft CI.CR = refl
closureMotifToScheduleLeft CI.CP = refl
closureMotifToScheduleLeft CI.CC = refl

closureConservedChargeToScheduleLeft-CP-obstructed :
  CA.canonicalConservedChargeOf (CA.canonicalClosureDynamics CI.CP)
    ≢
  projectedScheduleCharge
    (SRGOI.shiftCoarse
      (EC.Contract.step ShiftC (CA.canonicalTransportState CI.CP)))
closureConservedChargeToScheduleLeft-CP-obstructed ()

closureMotifToSchedule :
  ∀ x →
  SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
  closureMotifObservable (CA.canonicalClosureDynamics x)
    ≡
  projectObservableMotif
    (CA.canonicalTransportObservable
      (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x)))
closureMotifToSchedule x ax =
  trans
    (closureMotifToScheduleLeft x)
    (cong projectObservableMotif (closureTransportedScheduleSurface x ax))

closureMotifObservablePreserved :
  ∀ x →
  closureMotifObservable x
    ≡
  closureMotifObservable (CA.canonicalClosureDynamics x)
closureMotifObservablePreserved CI.CR = refl
closureMotifObservablePreserved CI.CP = refl
closureMotifObservablePreserved CI.CC = refl

sourceMotifToSchedule :
  ∀ x →
  SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
  closureMotifObservable x
    ≡
  projectObservableMotif
    (CA.canonicalTransportObservable
      (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x)))
sourceMotifToSchedule x ax =
  trans
    (closureMotifObservablePreserved x)
    (closureMotifToSchedule x ax)

-- Exact blocker on the canonical CP branch:
-- any bridge that includes both fields above collapses to raw-eigen
-- conservation on CP, contradicting the explicit obstruction theorem.
rawEigenClosureShiftBridge-CP-obstructed :
  RawEigenClosureShiftScheduleBridge → ⊥
rawEigenClosureShiftBridge-CP-obstructed br =
  CA.canonicalEigenLevel-CP-obstructed
    (sym
      (trans
        (cong
          RGOI.RGObservable.eigenSummary
          (RawEigenClosureShiftScheduleBridge.closure-to-schedule br CI.CP))
        (RawEigenClosureShiftScheduleBridge.schedule-to-source-eigen br CI.CP)))
