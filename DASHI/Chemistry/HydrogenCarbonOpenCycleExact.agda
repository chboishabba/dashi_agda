module DASHI.Chemistry.HydrogenCarbonOpenCycleExact where

-- Attribution: stoichiometric carbon atom conservation is classical chemistry;
-- the finite open-path accounting schema reuses DASHI's existing open-system
-- and finite-path conservation patterns. User-directed, ChatGPT-drafted
-- construction (2026-11-09), not evidence of a physical reactor or an
-- independently verified carbon capture process.
--
-- Carbon is measured as *amount of carbon atoms*, not energy or methane mass.
-- Carbon can recirculate if externally paid energy is supplied; losses demand
-- makeup carbon for any steady inventory.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
import DASHI.Physics.Units.SI as SI

record CarbonStep (before after : Nat) : Set where
  field
    makeupCarbon : Nat
    emittedCarbon : Nat
    balance : before + makeupCarbon ≡ after + emittedCarbon

open CarbonStep public

-- The path is a dependent chain of genuine selected carbon-ledger steps;
-- no numerical capture or synthesis efficiency is postulated.
data CarbonPath : Nat → Nat → Set where
  empty : (stock : Nat) → CarbonPath stock stock
  thenStep : ∀ {start middle finish} →
    CarbonStep start middle →
    CarbonPath middle finish →
    CarbonPath start finish

totalMakeup :
  ∀ {before after} → CarbonPath before after → Nat
totalMakeup (empty _) = 0
totalMakeup (thenStep s rest) = makeupCarbon s + totalMakeup rest

totalEmitted :
  ∀ {before after} → CarbonPath before after → Nat
totalEmitted (empty _) = 0
totalEmitted (thenStep s rest) = emittedCarbon s + totalEmitted rest

-- Pure polynomial reassociation needed for an ordered finite path.
carbonAssoc :
  (a b c : Nat) → a + (b + c) ≡ (a + b) + c
carbonAssoc a b c =
  solve 3
    (λ a b c → a :+ (b :+ c) := (a :+ b) :+ c)
    refl a b c

carbonSwap :
  (a b c : Nat) → (a + b) + c ≡ (a + c) + b
carbonSwap a b c =
  solve 3
    (λ a b c → (a :+ b) :+ c := (a :+ c) :+ b)
    refl a b c

carbonFinish :
  (a b c : Nat) → (a + b) + c ≡ a + (c + b)
carbonFinish a b c =
  solve 3
    (λ a b c → (a :+ b) :+ c := a :+ (c :+ b))
    refl a b c

carbonPathBalance :
  ∀ {before after} (p : CarbonPath before after) →
  before + totalMakeup p ≡ after + totalEmitted p
carbonPathBalance (empty stock) = refl
carbonPathBalance {before} {after}
  (thenStep {middle = middle} s rest) =
  trans
    (carbonAssoc before (makeupCarbon s) (totalMakeup rest))
    (trans
      (cong (λ n → n + totalMakeup rest) (balance s))
      (trans
        (carbonSwap middle (emittedCarbon s) (totalMakeup rest))
        (trans
          (cong (λ n → n + emittedCarbon s)
            (carbonPathBalance rest))
          (carbonFinish after (totalEmitted rest) (emittedCarbon s)))))

-- Required stable inventory is a source condition, not a consequence of
-- repeated capture. If the total before=after, the recovered carbon does
-- not replenish emitted material without external makeup.
record CyclicCarbonRun (inventory : Nat) : Set where
  field
    path : CarbonPath inventory inventory
    measuredCarbonFeeds : Set
    measuredCarbonExhaust : Set
    productIdentityAndStorageAssay : Set

open CyclicCarbonRun public

cyclicCarbonMakeupEqualsEmissions :
  ∀ {inventory} (run : CyclicCarbonRun inventory) →
  inventory + totalMakeup (path run)
    ≡ inventory + totalEmitted (path run)
cyclicCarbonMakeupEqualsEmissions run = carbonPathBalance (path run)

record ReactorEnergyAndCarbonReceipt : Set₁ where
  field
    carbonInput : SI.Measurement SI.Amount SI.unitScale
    carbonOutput : SI.Measurement SI.Amount SI.unitScale
    inputElectricity : SI.Measurement SI.Energy SI.unitScale
    recoveredHeat : SI.Measurement SI.Energy SI.unitScale
    auxiliaryConsumption : SI.Measurement SI.Energy SI.unitScale
    productHHVEnergy : SI.Measurement SI.Energy SI.unitScale
    carbonMassBalancePaid : Set
    waterAndOxygenBalancePaid : Set
    hydrogenAllocationPaid : Set
    reactorOperatingEnvelopePaid : Set
    chromatographicProductIdentityPaid : Set
    heatRecoveryAndStorageBoundaryPaid : Set
    independentTimeAlignedMeasurement : Set
