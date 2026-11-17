module DASHI.Physics.Motors.SmithFilsingerSpatialSourceCapWeldExact where

-- High-alpha Agda consumer: ALL-N spatial internal-source port
-- cancellation from existing SpatialPortChainExact, joined to the
-- SAME selected Filsinger source, controller, load and admitted cap.
-- No finite N, phase, geometry, Maxwell PDE or environmental source
-- is fabricated from a numeric source boundary.
--
-- The all-N spatial conservation owner is imported, not duplicated.
-- Its physical field/current/source boundary remains an authority gate.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_)

import DASHI.Physics.Motors.SmithFilsingerSpatialPortChainExact as Spatial
import DASHI.Physics.Motors.SmithFilsingerTimedSpatialPortChainExact as Timed
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- Only exterior natural port remains after all internal chain ports
-- cancel. The outgoing natural port must be subtracted, not mistaken
-- for external environmental input.
reorderSpatialInput :
  (outgoing naturalNet driver stored : Nat) →
  (outgoing + naturalNet) + (driver + stored)
    ≡ (naturalNet + driver) + (outgoing + stored)
reorderSpatialInput o n d s =
  solve 4
    (λ o n d s →
      ((o :+ n) :+ (d :+ s))
      := ((n :+ d) :+ (o :+ s)))
    refl o n d s

reorderSpatialOutput :
  (outgoing useful loss stored : Nat) →
  outgoing + (useful + (loss + stored))
    ≡ (useful + loss) + (outgoing + stored)
reorderSpatialOutput o u l s =
  solve 4
    (λ o u l s →
      (o :+ (u :+ (l :+ s)))
      := ((u :+ l) :+ (o :+ s)))
    refl o u l s

-- Derive the NET source/work law from the original all-N chain
-- conservation theorem, the actual signed first/last boundary and
-- WHOLE-CHAIN storage restoration. No second aggregate ledger axiom.
spatialChainNetSourceWork :
  ∀ {first last}
  (chain : Spatial.SpatialChain first last)
  (naturalNet : Nat) →
  first ≡ last + naturalNet →
  Spatial.sumInitialStorage chain ≡ Spatial.sumFinalStorage chain →
  naturalNet + Spatial.sumDrive chain
    ≡ Spatial.sumUsefulLoad chain + Spatial.sumDissipation chain
spatialChainNetSourceWork {first} {last}
  chain naturalNet netBoundary storageRestored =
  Cycle.+-cancelRight _ _ (last + Spatial.sumFinalStorage chain)
    (Cycle.trans
      (Bound.sym
        (reorderSpatialInput last naturalNet
          (Spatial.sumDrive chain) (Spatial.sumFinalStorage chain)))
      (Cycle.trans
        (Cycle.cong
          (λ x → x +
            (Spatial.sumDrive chain + Spatial.sumFinalStorage chain))
          (Bound.sym netBoundary))
        (Cycle.trans
          (Cycle.cong
            (λ z → first + (Spatial.sumDrive chain + z))
            (Bound.sym storageRestored))
          (Cycle.trans
            (Spatial.spatialChainWorkBalance chain)
            (reorderSpatialOutput last
              (Spatial.sumUsefulLoad chain)
              (Spatial.sumDissipation chain)
              (Spatial.sumFinalStorage chain))))))

spatialChainLoadBelowNetSourceAndController :
  ∀ {first last}
  (chain : Spatial.SpatialChain first last)
  (naturalNet : Nat) →
  first ≡ last + naturalNet →
  Spatial.sumInitialStorage chain ≡ Spatial.sumFinalStorage chain →
  Bound._≤_ (Spatial.sumUsefulLoad chain)
    (naturalNet + Spatial.sumDrive chain)
spatialChainLoadBelowNetSourceAndController chain n netLaw restored =
  Bound.transportUpper
    (Bound.sym (spatialChainNetSourceWork chain n netLaw restored))
    (Bound.≤-append
      (Spatial.sumUsefulLoad chain) (Spatial.sumDissipation chain))

-- It is a separate physical premise that an exterior chain's net
-- source is the independently identified NATURAL source of one
-- selected historic original and the controller/load belong to it.
-- The chain's first/last scalars cannot by themselves prove solar work.
selectedOriginalAllSpatialCellsBelowNaturalCap :
  ∀ {first last}
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f)
  (chain : Spatial.SpatialChain first last)
  (naturalNet : Nat) →
  first ≡ last + naturalNet →
  naturalNet ≡ Cycle.RepeatableSourceCycle.naturalSourceWork
    (Cycle.AdmittedSourceCapCycle.repeatable
      (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)) →
  Spatial.sumDrive chain ≡ Cycle.RepeatableSourceCycle.controllerWork
    (Cycle.AdmittedSourceCapCycle.repeatable
      (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)) →
  Spatial.sumUsefulLoad chain ≡
    Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f) →
  Spatial.sumInitialStorage chain ≡ Spatial.sumFinalStorage chain →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f))
    (Cycle.AdmittedSourceCapCycle.independentlyAdmittedNaturalCap
      (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)
      + Cycle.RepeatableSourceCycle.controllerWork
        (Cycle.AdmittedSourceCapCycle.repeatable
          (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)))
selectedOriginalAllSpatialCellsBelowNaturalCap
  b f s chain n firstNet sameNatural sameController sameLoad restored =
  substLower (Bound.sym sameLoad)
    (Bound.transportUpper
      (Cycle.cong (λ x → cap + x) sameController)
      (Cycle.≤-trans
        (spatialChainLoadBelowNetSourceAndController
          chain n firstNet restored)
        (Cycle.+-monotoneRight
          (Spatial.sumDrive chain)
          (Bound.transportUpper capReceipt
            (Bound.≤-append n unused)))))
  where
    substLower : {a b c : Nat} →
      a ≡ b → Bound._≤_ b c → Bound._≤_ a c
    substLower refl proof = proof

    capCycle : Cycle.AdmittedSourceCapCycle
    capCycle = Weld.SignedSourceCycleWeld.cycleWithSourceCap s

    cap : Nat
    cap = Cycle.AdmittedSourceCapCycle.independentlyAdmittedNaturalCap capCycle

    unused : Nat
    unused = Cycle.AdmittedSourceCapCycle.unspentNaturalBudget capCycle

    capReceipt : n + unused ≡ cap
    capReceipt =
      Cycle.trans
        (Cycle.cong (λ x → x + unused) sameNatural)
        (Cycle.AdmittedSourceCapCycle.capReceipt capCycle)

-- Cross-owner causality weld: the timed all-N spatial source/receiver
-- chain erases to the CANONICAL all-N energy chain without changing the
-- admitted natural work or finite-slew controller work. Retarded flight
-- also certifies that the final event is not before the launch event.
-- Neither theorem is a continuous Maxwell light-cone statement.
allTimedSelectedOriginalCellsBelowNaturalCap :
  ∀ {first last start finish}
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f)
  (path : Timed.TimedSpatialChain first last start finish)
  (naturalNet : Nat) →
  first ≡ last + naturalNet →
  naturalNet ≡ Cycle.RepeatableSourceCycle.naturalSourceWork
    (Cycle.AdmittedSourceCapCycle.repeatable
      (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)) →
  Spatial.sumDrive (Timed.eraseTiming path)
    ≡ Cycle.RepeatableSourceCycle.controllerWork
        (Cycle.AdmittedSourceCapCycle.repeatable
          (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)) →
  Spatial.sumUsefulLoad (Timed.eraseTiming path)
    ≡ Port.MidpointTwoPortWorkWindow.usefulWork
        (Weld.FormalFieldToPort.portWindow f) →
  Spatial.sumInitialStorage (Timed.eraseTiming path)
    ≡ Spatial.sumFinalStorage (Timed.eraseTiming path) →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f))
    (Cycle.AdmittedSourceCapCycle.independentlyAdmittedNaturalCap
      (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)
     + Cycle.RepeatableSourceCycle.controllerWork
        (Cycle.AdmittedSourceCapCycle.repeatable
          (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)))
allTimedSelectedOriginalCellsBelowNaturalCap
  b f s path n sourceBoundary sourceOwner driverOwner loadOwner restored =
  selectedOriginalAllSpatialCellsBelowNaturalCap
    b f s (Timed.eraseTiming path) n
    sourceBoundary sourceOwner driverOwner loadOwner restored

allTimedSelectedOriginalArrivalIsCausal :
  ∀ {first last start finish}
  (path : Timed.TimedSpatialChain first last start finish) →
  Bound._≤_ start finish
allTimedSelectedOriginalArrivalIsCausal =
  Timed.allTimedPathsArriveAfterLaunch
