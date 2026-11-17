module DASHI.Physics.Motors.SmithFilsingerOriginalMaxwellRestoredMeterFundingExact where

-- F10/F15 original-object funding weld: retain the existing, independently
-- source-admitted restored-cycle theorem and the selected ORIGINAL Maxwell
-- meter window. Do not assume a second energy balance, or promote the
-- algebra to a measured source or a verified original-apparatus result.

open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Rational.Base as ℚ

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as Vector
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Source
import DASHI.Physics.Motors.SmithFilsingerSelectedSpaceTimePortWeldExact as Original
import DASHI.Physics.Motors.SmithFilsingerOriginalMaxwellMeterIntervalWeldExact as MeterWeld
import DASHI.Physics.Motors.SmithFilsingerSpaceTimePoyntingTelescopeExact as SpaceTime
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle

-- Source.SignedSourceCycleWeld b f and MeterWeld ... jet b f refer to the
-- SAME original boundary and field-port pair, not two compatible-looking
-- sources. The restored Nat-source ledger is mapped to exact rational
-- calibrated work by the ALREADY admitted additive calibration map.
--
-- This equality is a consequence of Cycle.workPaidAfterStorageReturns,
-- Original.loadIsSameOriginal, the original port's same-cycle load and
-- loss correspondences, and calibratedAdd. It is NOT an independent
-- conservation hypothesis.
restoredSourceFundsSameOriginalMaxwellReceiver :
  ∀ {r} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (b : Source.SelectedBoundary)
  (f : Source.FormalFieldToPort b)
  (a : MeterWeld.OriginalMaxwellMeterIntervalWeld jet b f)
  (w : Source.SignedSourceCycleWeld b f) →
  let port = MeterWeld.originalPort a
      physical = Original.SelectedOriginalSpaceTimePort.physicalTrace port
      calibrated = Original.SelectedOriginalSpaceTimePort.calibratedWork port
      c = Cycle.AdmittedSourceCapCycle.repeatable
            (Source.SignedSourceCycleWeld.cycleWithSourceCap w)
  in
  (SpaceTime.SameOriginalSpaceTimeMaxwellAdmission.actualUsefulReceiverWork
     physical
   ℚ.+ calibrated
     (Port.MidpointTwoPortWorkWindow.internalLoss
       (Source.FormalFieldToPort.portWindow f)))
  ≡
  (calibrated (Cycle.RepeatableSourceCycle.naturalSourceWork c)
   ℚ.+ calibrated (Cycle.RepeatableSourceCycle.controllerWork c))
restoredSourceFundsSameOriginalMaxwellReceiver jet b f a w
  rewrite Original.SelectedOriginalSpaceTimePort.loadIsSameOriginal
            (MeterWeld.originalPort a)
        | Source.SignedSourceCycleWeld.sameOriginalUsefulLoad w
        | Source.SignedSourceCycleWeld.sameOriginalInternalLoss w =
  trans
    (sym (Original.SelectedOriginalSpaceTimePort.calibratedAdd
      (MeterWeld.originalPort a)
      (Cycle.RepeatableSourceCycle.usefulLoadWork c)
      (Cycle.RepeatableSourceCycle.allHeatAndOutgoing c)))
    (trans
      (cong
        (Original.SelectedOriginalSpaceTimePort.calibratedWork
          (MeterWeld.originalPort a))
        (sym (Cycle.workPaidAfterStorageReturns c)))
      (Original.SelectedOriginalSpaceTimePort.calibratedAdd
        (MeterWeld.originalPort a)
        (Cycle.RepeatableSourceCycle.naturalSourceWork c)
        (Cycle.RepeatableSourceCycle.controllerWork c)))
  where
    c : Cycle.RepeatableSourceCycle
    c = Cycle.AdmittedSourceCapCycle.repeatable
          (Source.SignedSourceCycleWeld.cycleWithSourceCap w)

