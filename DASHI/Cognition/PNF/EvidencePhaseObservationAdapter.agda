module DASHI.Cognition.PNF.EvidencePhaseObservationAdapter where

import DASHI.Core.FinePhaseObservation as Phase
import DASHI.Cognition.PNF.EvidenceHorizon369 as Horizon
import DASHI.Cognition.PNF.TypePressure as Pressure

------------------------------------------------------------------------
-- H3/H6/H9 evidence coordinates already retain exact signed integer evidence.
-- This adapter makes their coarse direction literally an instance of the
-- canonical fine->coarse phase-observation core.
------------------------------------------------------------------------

evidenceCoordinatePhaseObservation :
  ∀ {Candidate family}
    (coordinate : Horizon.EvidenceCoordinate Candidate family) →
  Phase.ObservedPhase
    Phase.integerSignedPhaseSystem
    (Horizon.fineSignedEvidence coordinate)
evidenceCoordinatePhaseObservation coordinate =
  Phase.observeIntegerPhase (Horizon.fineSignedEvidence coordinate)

typePressurePhaseObservation :
  ∀ {subject candidateType}
    (pressure : Pressure.NumericPredicateRolePressure subject candidateType) →
  Phase.ObservedPhase
    Phase.integerSignedPhaseSystem
    (Pressure.signedRolePressure pressure)
typePressurePhaseObservation pressure =
  Phase.observeIntegerPhase (Pressure.signedRolePressure pressure)
