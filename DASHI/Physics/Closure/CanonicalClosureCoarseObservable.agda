module DASHI.Physics.Closure.CanonicalClosureCoarseObservable where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CA
open import DASHI.Physics.Closure.CanonicalClosureShiftScheduleBridge as CCSB
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Canonical maximal currently bridged coarse observable package.

CanonicalCarrier : Set
CanonicalCarrier =
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage

MaximalCoarseObservable : Set
MaximalCoarseObservable =
  CCSB.CanonicalMotifScheduleObservable

π-max : CanonicalCarrier → MaximalCoarseObservable
π-max = CCSB.closureMotifObservable

------------------------------------------------------------------------
-- Factorization through the already-landed motif-level bridge.

private
  ShiftC = SLEI.shiftContract {1} {3}

projectFromSchedule :
  EC.Contract.State ShiftC → MaximalCoarseObservable
projectFromSchedule x =
  CCSB.projectObservableMotif (CA.canonicalTransportObservable x)

π-max-closure-to-schedule :
  ∀ x →
  SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
  π-max (CA.canonicalClosureDynamics x)
    ≡
  projectFromSchedule (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x))
π-max-closure-to-schedule = CCSB.closureMotifToSchedule

π-max-source-to-schedule :
  ∀ x →
  SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
  π-max x
    ≡
  projectFromSchedule (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x))
π-max-source-to-schedule = CCSB.sourceMotifToSchedule

------------------------------------------------------------------------
-- Same coarse package as a projection of the larger conserved-charge payload.

projectFromConservedCharge :
  CA.CanonicalConservedCharge → MaximalCoarseObservable
projectFromConservedCharge (g , b , _ , m , _) = (g , b , m)

π-max-factors-through-conserved-charge :
  ∀ x →
  π-max x
    ≡
  projectFromConservedCharge (CA.canonicalConservedChargeOf x)
π-max-factors-through-conserved-charge _ = refl

------------------------------------------------------------------------
-- Obstruction-facing surface: stronger widened bridge shapes remain blocked
-- on CP under the current canonical closure law.

rawEigen-CP-obstructed :
  CA.canonicalEigenLevel CI.CP
    ≡
  CA.canonicalEigenLevel (CA.canonicalClosureDynamics CI.CP)
    → ⊥
rawEigen-CP-obstructed = CA.canonicalEigenLevel-CP-obstructed

record WidenedProjectedBridgeNoMdl : Set where
  field
    closure-projected-left :
      ∀ x →
      CCSB.closureProjectedObservable (CA.canonicalClosureDynamics x)
        ≡
      CCSB.projectObservableNoMdl
        (CA.canonicalTransportObservable
          (SRGOI.shiftCoarse
            (EC.Contract.step ShiftC (CA.canonicalTransportState x))))

noWidenedProjectedBridgeNoMdl : WidenedProjectedBridgeNoMdl → ⊥
noWidenedProjectedBridgeNoMdl br =
  CCSB.closureProjectedToScheduleLeft-CP-obstructed
    (WidenedProjectedBridgeNoMdl.closure-projected-left br CI.CP)

record WidenedConservedChargeScheduleBridge : Set where
  field
    closure-conserved-left :
      ∀ x →
      CA.canonicalConservedChargeOf (CA.canonicalClosureDynamics x)
        ≡
      CCSB.projectedScheduleCharge
        (SRGOI.shiftCoarse
          (EC.Contract.step ShiftC (CA.canonicalTransportState x)))

noWidenedConservedChargeScheduleBridge :
  WidenedConservedChargeScheduleBridge → ⊥
noWidenedConservedChargeScheduleBridge br =
  CCSB.closureConservedChargeToScheduleLeft-CP-obstructed
    (WidenedConservedChargeScheduleBridge.closure-conserved-left br CI.CP)
