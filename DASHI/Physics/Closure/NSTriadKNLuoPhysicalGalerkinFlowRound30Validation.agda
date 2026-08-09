module DASHI.Physics.Closure.NSTriadKNLuoPhysicalGalerkinFlowRound30Validation where

------------------------------------------------------------------------
-- Round Thirty validation root.
--
-- Imported cumulatively by the Round-29 root on this child branch so the
-- existing pull-request workflow typechecks the new tranche as well.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinVectorFieldRound30Exact as Field
import DASHI.Physics.Closure.NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact as Coordinates
import DASHI.Physics.Closure.NSTriadKNPicardLindelofTransportRound30Exact as Picard
import DASHI.Physics.Closure.NSTriadKNLiteralNonlinearEnergyCancellationRound30Exact as Cancellation
import DASHI.Physics.Closure.NSTriadKNPhysicalFiniteEnergyIdentityRound30Exact as Energy
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalGalerkinFlowRound30Exact as Global

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

physicalFieldCodomainRegression :
  Field.fullGalerkinVectorFieldMapsReconstructedState ≡ true
physicalFieldCodomainRegression =
  Field.fullGalerkinVectorFieldMapsReconstructedStateIsTrue

coordinateTransportRegression :
  Coordinates.finitePhysicalCoordinateEquivalenceClosed ≡ true
coordinateTransportRegression =
  Coordinates.finitePhysicalCoordinateEquivalenceClosedIsTrue

picardTransportRegression :
  Picard.picardLindelofTransportClosed ≡ true
picardTransportRegression = Picard.picardLindelofTransportClosedIsTrue

nonlinearFoldRegression :
  Cancellation.literalNonlinearFiniteFoldClosed ≡ true
nonlinearFoldRegression = Cancellation.literalNonlinearFiniteFoldClosedIsTrue

energyIdentityRegression :
  Energy.physicalFiniteDifferentialEnergyIdentityClosed ≡ true
energyIdentityRegression =
  Energy.physicalFiniteDifferentialEnergyIdentityClosedIsTrue

globalFlowReducerRegression :
  Global.literalPhysicalGlobalFlowReducerClosed ≡ true
globalFlowReducerRegression =
  Global.literalPhysicalGlobalFlowReducerClosedIsTrue
