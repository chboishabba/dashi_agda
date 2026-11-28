module DASHI.Physics.Motors.SmithFilsingerRetardedFaceCycleWeldExact where

-- Conditional Nat work grid. A flight channel is itself a volume cell;
-- its two interfaces are distinct receipts even when their totals agree.
-- Classical finite-volume conservation, existing DASHI owners reused.
-- No measured field, material or natural source is supplied by this module.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.SmithFilsingerFiniteVolumeFaceIncidenceExact as Face
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_)

record FlightWindow : Set where
  constructor flightWindow
  field
    launchWork arrivalWork initialFlight finalFlight : Nat
    transportBalance : launchWork + initialFlight ≡ arrivalWork + finalFlight

flightAsCell : FlightWindow → Face.LocalVolumeCell
flightAsCell f = Face.localVolumeCell 0 l 0 i 0 a 0 0 z
  (FlightWindow.transportBalance f)
  where
    open FlightWindow f renaming
      (launchWork to l; arrivalWork to a; initialFlight to i; finalFlight to z)

flightRestoredWork : (f : FlightWindow) →
  FlightWindow.initialFlight f ≡ FlightWindow.finalFlight f →
  FlightWindow.launchWork f ≡ FlightWindow.arrivalWork f
flightRestoredWork f restored =
  Cycle.+-cancelRight _ _ (FlightWindow.finalFlight f)
    (Cycle.trans
      (Cycle.cong (λ v → FlightWindow.launchWork f + v) (Bound.sym restored))
      (FlightWindow.transportBalance f))

-- Independent admitted cap plus controller work; no hidden flight depletion
-- when ALL cells (including each flight cell) restore their storage.
meshAsRepeatable :
  (m : Face.OrientedFaceMesh) →
  Face.totalInitial (Face.OrientedFaceMesh.cells m) ≡
    Face.totalFinal (Face.OrientedFaceMesh.cells m) →
  Cycle.RepeatableSourceCycle
meshAsRepeatable m restored =
  Cycle.repeatableSourceCycle ei d i z l (eo + q)
    (Cycle.trans
      (solve 3 (λ a b c → (a :+ b) :+ c := a :+ (b :+ c))
        refl ei d i)
      (Cycle.trans (Face.finiteVolumeExteriorEnergyBalance m)
        (solve 4
          (λ a b c e → a :+ (b :+ (c :+ e)) := b :+ ((a :+ c) :+ e))
          refl eo l q z)))
    restored
  where
    cs = Face.OrientedFaceMesh.cells m
    ei = Face.totalExtIn cs
    d = Face.totalDrive cs
    i = Face.totalInitial cs
    z = Face.totalFinal cs
    l = Face.totalLoad cs
    eo = Face.totalExtOut cs
    q = Face.totalLoss cs

