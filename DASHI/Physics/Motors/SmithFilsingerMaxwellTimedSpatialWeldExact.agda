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
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Time
import DASHI.Physics.Motors.SmithFilsingerSpatialPortChainExact as Spatial
import DASHI.Physics.Motors.SmithFilsingerSpatialSourceCapWeldExact as Cap
import DASHI.Physics.Motors.SmithFilsingerOpenBoundaryPoyntingGaussExact as Gauss
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- A measured/sourced pointwise-to-interval theorem is a work law
-- on the SAME two directed exterior terminals. It is not a preconstructed
-- CausalSpatialCell: the latter is DERIVED from this physical law below.
-- Field-to-boundary integration, orientation and trace are separate
-- premises. A bare three-vector curl jet cannot supply the integral.
record IntegratedFieldCell
  {r : Level} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (first shared start middle : Nat) : Set (lsuc r) where
  field
    controllerWork initiallyStored usefulLoad lossAndRadiation
      finallyStored : Nat
    flight : Time.RetardedFlight
    startsAt : Time.RetardedFlight.launch flight ≡ start
    finishesAt : Time.RetardedFlight.arrival flight ≡ middle

    -- This particular field must be integrated over the actual selected
    -- time/space boundary. The implication itself is a physical premise.
    -- Its CONCLUSION is a numeric work equality, not a ready-made cell.
    integratedLocalPoynting :
      Vector.fullVectorSignedBudget jet ≡ C3.zero F →
      first + (controllerWork + initiallyStored)
        ≡ shared + (usefulLoad + (lossAndRadiation + finallyStored))

-- Concrete Agda construction from a Maxwell pointwise theorem and the
-- independent physically integrated local equality. The proof of local
-- SpatialCell.work is not accepted wholesale as an arbitrary cell.
buildCausalCellFromMaxwell :
  ∀ {r} {F : C3.RealField r}
    {first shared start middle} →
  (jet : Vector.FullVectorMaxwellJet F) →
  (receipt : IntegratedFieldCell jet first shared start middle) →
  Timed.CausalSpatialCell first shared start middle
buildCausalCellFromMaxwell jet receipt =
  Timed.causalSpatialCell
    (Spatial.spatialCell
      (IntegratedFieldCell.controllerWork receipt)
      (IntegratedFieldCell.initiallyStored receipt)
      (IntegratedFieldCell.usefulLoad receipt)
      (IntegratedFieldCell.lossAndRadiation receipt)
      (IntegratedFieldCell.finallyStored receipt)
      (IntegratedFieldCell.integratedLocalPoynting receipt
        (Vector.fullVectorMaxwellPoyntingIdentity jet)))
    (IntegratedFieldCell.flight receipt)
    (IntegratedFieldCell.startsAt receipt)
    (IntegratedFieldCell.finishesAt receipt)

-- Stronger open-Gauss cell: the KSW pointwise vector theorem is
-- FIRST integrated to signed rational exterior face flux using the exact
-- finite YM-Ward telescoping theorem. Only the final calibrated signed
-- rational-flux -> finite Nat work equality remains physical.
-- This does not silently use a periodic zero-exterior-flux boundary.
record IntegratedOpenGaussCell
  {r : Level} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (first shared start middle : Nat) : Set (lsuc r) where
  field
    faceTrace : Gauss.OriginalMaxwellOpenFaceTrace jet
    controllerWork initiallyStored usefulLoad lossAndRadiation
      finallyStored : Nat
    flight : Time.RetardedFlight
    startsAt : Time.RetardedFlight.launch flight ≡ start
    finishesAt : Time.RetardedFlight.arrival flight ≡ middle

    -- One remaining calibrated conversion obligation. It explicitly
    -- witnesses that the signed rational exterior flux corresponds to
    -- the same original input/output finite-grid port work and units.
    originalRationalFluxToNatWork :
      Gauss.OriginalMaxwellOpenFaceTrace.integratedSpatialPoyntingDivergence
        faceTrace
      ≡ Gauss.OriginalMaxwellOpenFaceTrace.originalSignedExteriorPortFlux
          faceTrace →
      first + (controllerWork + initiallyStored)
        ≡ shared + (usefulLoad + (lossAndRadiation + finallyStored))

-- Derive a real CausalSpatialCell from KSW vector Poynting, exact
-- nonperiodic 3-axis Gauss, physical field/face integral, and calibrated
-- original terminal equality. The latter is NOT filled by a dummy proof.
buildCausalCellFromOpenGauss :
  ∀ {r} {F : C3.RealField r}
    {first shared start middle} →
  (jet : Vector.FullVectorMaxwellJet F) →
  (receipt : IntegratedOpenGaussCell jet first shared start middle) →
  Timed.CausalSpatialCell first shared start middle
buildCausalCellFromOpenGauss jet receipt =
  Timed.causalSpatialCell
    (Spatial.spatialCell
      (IntegratedOpenGaussCell.controllerWork receipt)
      (IntegratedOpenGaussCell.initiallyStored receipt)
      (IntegratedOpenGaussCell.usefulLoad receipt)
      (IntegratedOpenGaussCell.lossAndRadiation receipt)
      (IntegratedOpenGaussCell.finallyStored receipt)
      (IntegratedOpenGaussCell.originalRationalFluxToNatWork receipt
        (Gauss.originalFullVectorJetOpenBoundaryFlux jet
          (IntegratedOpenGaussCell.faceTrace receipt))))
    (IntegratedOpenGaussCell.flight receipt)
    (IntegratedOpenGaussCell.startsAt receipt)
    (IntegratedOpenGaussCell.finishesAt receipt)

-- Every link carries an actual FULL VECTOR Maxwell jet and a separate
-- physically integrated field-to-port work receipt; one original
-- selected source b/f/s is preserved across the entire dependent path.
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
      IntegratedFieldCell jet first shared start middle →
      MaxwellTimedPath b f s shared last middle finish →
      MaxwellTimedPath b f s first last start finish

    throughOpenGauss :
      ∀ {first shared last start middle finish} →
      (jet : Vector.FullVectorMaxwellJet F) →
      IntegratedOpenGaussCell jet first shared start middle →
      MaxwellTimedPath b f s shared last middle finish →
      MaxwellTimedPath b f s first last start finish

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
eraseMaxwellToTimedSpatial (throughField jet receipt rest) =
  Timed.thenTimed
    (buildCausalCellFromMaxwell jet receipt)
    (eraseMaxwellToTimedSpatial rest)
eraseMaxwellToTimedSpatial (throughOpenGauss jet receipt rest) =
  Timed.thenTimed
    (buildCausalCellFromOpenGauss jet receipt)
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
