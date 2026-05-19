module DASHI.Physics.Closure.ShiftContractCoarseObservable where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_; _×_)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (ShiftBasin; ShiftMotif; canonicalShiftHeckeState)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
  using
    ( observeOnGeo
    ; shiftContractObservableBundle
    ; shiftContractObservableTransportWitness
    )

------------------------------------------------------------------------
-- Noncanonical lift of the coarse observable package onto full
-- ShiftContractState, aligned with the observable-transport replay surface.

MaximalCoarseObservable : Set
MaximalCoarseObservable = GGC.Gauge × ShiftBasin × ShiftMotif

projectObservableMotif :
  GGC.Gauge × RGOI.RGObservable ShiftBasin ShiftMotif →
  MaximalCoarseObservable
projectObservableMotif (g , o) =
  ( g
  , RGOI.RGObservable.basinLabel o
  , RGOI.RGObservable.motifClass o
  )

π-max : ShiftContractState → MaximalCoarseObservable
π-max x =
  projectObservableMotif
    (GGC.SU3×SU2×U1 , observeOnGeo (canonicalShiftHeckeState x))

projectFromTransportTarget :
  SLEI.ShiftGeoV → MaximalCoarseObservable
projectFromTransportTarget x =
  projectObservableMotif (GGC.SU3×SU2×U1 , observeOnGeo x)

π-max-factors-through-transport :
  ∀ x →
  π-max x
    ≡
  projectFromTransportTarget
    (AGMB.ObservableTransportWitness.transport
      shiftContractObservableTransportWitness
      x)
π-max-factors-through-transport _ = refl

π-max-factors-through-bundle-observable :
  ∀ x →
  π-max x
    ≡
  projectObservableMotif
    (AGMB.observableOf shiftContractObservableBundle x)
π-max-factors-through-bundle-observable _ = refl
