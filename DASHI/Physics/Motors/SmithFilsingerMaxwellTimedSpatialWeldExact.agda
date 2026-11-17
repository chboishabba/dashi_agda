module DASHI.Physics.Motors.SmithFilsingerMaxwellTimedSpatialWeldExact where

-- Full mathematical COMPOSITE MAX-CUT, no numerical simulation:
--   canonical KSW 668 three-vector Ampere/Faraday pointwise Poynting
--       -> independently certified physical spacetime/port integration
--       -> canonical Filsinger finite causal + all-N spatial work chain
--       -> selected ORIGINAL signed source cap, with full storage return.
--
-- The integration witness is REQUIRED for EVERY spatial cell. It is not
-- constructed from a field label, time tag, audio frequency, or a dummy
-- Set. Original Maxwell source current and physical source work are OPEN.
--
-- Attribution: user-origin Smith/Filsinger source/sink and environmental
-- access hypothesis; KSW original vector-jet and timed spatial DAG owners.

open import Agda.Primitive using (Level; _⊔_; lzero; lsuc)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as Vector
import DASHI.Physics.Motors.SmithFilsingerTimedSpatialPortChainExact as Timed
import DASHI.Physics.Motors.SmithFilsingerSpatialPortChainExact as Spatial
import DASHI.Physics.Motors.SmithFilsingerSpatialSourceCapWeldExact as Cap
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- Every physically integrated electromagnetic link has a genuine
-- ORIGINAL full-vector jet and its independent causal/spatial port map.
-- The source b, field f and signed source cycle s are the SAME through
-- every link by dependent typing, not merely equal file labels.
data MaxwellTimedPath
  {r : Level} {F : C3.RealField r}
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f) :
  Nat → Nat → Nat → Nat →
  Set (lsuc (r ⊔ lsuc (lsuc lzero)))
  where
    atBoundary : (boundary time : Nat) →
      MaxwellTimedPath b f s boundary boundary time time

    throughField :
      ∀ {first shared last start middle finish} →
      (jet : Vector.FullVectorMaxwellJet F) →
      (physicalPoyntingToCausalCell :
        Vector.fullVectorSignedBudget jet ≡ C3.zero F →
        Timed.CausalSpatialCell first shared start middle) →
      MaxwellTimedPath b f s shared last middle finish →
      MaxwellTimedPath b f s first last start finish

-- This is the exact computationally normalising PROOF compilers' fold,
-- not a physical Maxwell solver. Every cell's physical integration must
-- have been separately established to construct a nonempty path.
eraseMaxwellToTimedSpatial :
  ∀ {r} {F : C3.RealField r}
    {b : Weld.SelectedBoundary}
    {f : Weld.FormalFieldToPort b}
    {s : Weld.SignedSourceCycleWeld b f}
    {first last start finish} →
  MaxwellTimedPath b f s first last start finish →
  Timed.TimedSpatialChain first last start finish
eraseMaxwellToTimedSpatial (atBoundary boundary time) =
  Timed.emptyTimed boundary time
eraseMaxwellToTimedSpatial (throughField jet integrated rest) =
  Timed.thenTimed
    (integrated (Vector.fullVectorMaxwellPoyntingIdentity jet))
    (eraseMaxwellToTimedSpatial rest)

-- Original all-N timed conservation and no-early-arrival are reused.
-- They now apply to ANY path assembled from individually admitted
-- *three-component Maxwell pointwise* field-to-port certificates.
allIntegratedMaxwellCellsConserveWork :
  ∀ {r} {F : C3.RealField r}
    {b : Weld.SelectedBoundary}
    {f : Weld.FormalFieldToPort b}
    {s : Weld.SignedSourceCycleWeld b f}
    {first last start finish} →
  (path : MaxwellTimedPath b f s first last start finish) →
  first + (Spatial.sumDrive
    (Timed.eraseTiming (eraseMaxwellToTimedSpatial path))
    + Spatial.sumInitialStorage
      (Timed.eraseTiming (eraseMaxwellToTimedSpatial path)))
  ≡ last + (Spatial.sumUsefulLoad
    (Timed.eraseTiming (eraseMaxwellToTimedSpatial path))
    + (Spatial.sumDissipation
      (Timed.eraseTiming (eraseMaxwellToTimedSpatial path))
    + Spatial.sumFinalStorage
      (Timed.eraseTiming (eraseMaxwellToTimedSpatial path))))
allIntegratedMaxwellCellsConserveWork path =
  Timed.timedSpatialEnergyConservation (eraseMaxwellToTimedSpatial path)

allIntegratedMaxwellCellsRespectFlight :
  ∀ {r} {F : C3.RealField r}
    {b : Weld.SelectedBoundary}
    {f : Weld.FormalFieldToPort b}
    {s : Weld.SignedSourceCycleWeld b f}
    {first last start finish} →
  (path : MaxwellTimedPath b f s first last start finish) →
  Bound._≤_ start finish
allIntegratedMaxwellCellsRespectFlight path =
  Timed.allTimedPathsArriveAfterLaunch (eraseMaxwellToTimedSpatial path)

-- Strong F10 x F13 x F15 endpoint: ALL spatial cells are backed by
-- the original 3D vector-jet mathematical identity, each one separately
-- integrated to a causal energy work cell. Without extra sign choices,
-- the same ORIGINAL natural NET source cap bounds the actual load when
-- all cell stores return and source/driver/load identities are admitted.
allIntegratedMaxwellCellsBelowSelectedNaturalCap :
  ∀ {r} {F : C3.RealField r}
    {first last start finish} →
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f)
  (path : MaxwellTimedPath b f s first last start finish)
  (naturalNet : Nat) →
  first ≡ last + naturalNet →
  naturalNet ≡ Cycle.RepeatableSourceCycle.naturalSourceWork
    (Cycle.AdmittedSourceCapCycle.repeatable
      (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)) →
  Spatial.sumDrive (Timed.eraseTiming (eraseMaxwellToTimedSpatial path))
    ≡ Cycle.RepeatableSourceCycle.controllerWork
      (Cycle.AdmittedSourceCapCycle.repeatable
        (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)) →
  Spatial.sumUsefulLoad (Timed.eraseTiming (eraseMaxwellToTimedSpatial path))
    ≡ Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f) →
  Spatial.sumInitialStorage
    (Timed.eraseTiming (eraseMaxwellToTimedSpatial path))
    ≡ Spatial.sumFinalStorage
      (Timed.eraseTiming (eraseMaxwellToTimedSpatial path)) →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f))
    (Cycle.AdmittedSourceCapCycle.independentlyAdmittedNaturalCap
       (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)
     + Cycle.RepeatableSourceCycle.controllerWork
        (Cycle.AdmittedSourceCapCycle.repeatable
          (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)))
allIntegratedMaxwellCellsBelowSelectedNaturalCap
  b f s path net netLaw sameNatural sameController sameLoad restored =
  Cap.allTimedSelectedOriginalCellsBelowNaturalCap
    b f s (eraseMaxwellToTimedSpatial path) net
    netLaw sameNatural sameController sameLoad restored
