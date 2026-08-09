module DASHI.Physics.Closure.NSTriadKNLuoPhysicalGalerkinFlowRound30Validation where

------------------------------------------------------------------------
-- Round Thirty validation root.
--
-- This root exercises the concrete Leray/output-fibre/viscous-quadratic
-- construction before the coordinate-flow, energy, shell and Cotlar reducers.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as Leray
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as Nonlinear
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact as ConcreteField
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinVectorFieldRound30Exact as Field
import DASHI.Physics.Closure.NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact as Coordinates
import DASHI.Physics.Closure.NSTriadKNPicardLindelofTransportRound30Exact as Picard
import DASHI.Physics.Closure.NSTriadKNLiteralNonlinearEnergyCancellationRound30Exact as Cancellation
import DASHI.Physics.Closure.NSTriadKNPhysicalFiniteEnergyIdentityRound30Exact as Energy
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalGalerkinFlowRound30Exact as Global
import DASHI.Physics.Closure.NSTriadKNPhysicalTimeDependentShellBalanceRound30Exact as Shell
import DASHI.Physics.Closure.NSTriadKNCutoffUniformCotlarSteinRound30Exact as Cotlar

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

lerayOutputRegression :
  Leray.lerayOutputTransversalityClosed ≡ true
lerayOutputRegression = Leray.lerayOutputTransversalityClosedIsTrue

lerayIdempotenceRegression :
  Leray.lerayIdempotenceClosed ≡ true
lerayIdempotenceRegression = Leray.lerayIdempotenceClosedIsTrue

projectedNonlinearityRegression :
  Nonlinear.projectedNonlinearityTransverseClosed ≡ true
projectedNonlinearityRegression =
  Nonlinear.projectedNonlinearityTransverseClosedIsTrue

literalCoefficientRegression :
  Coefficient.literalViscousQuadraticCoefficientClosed ≡ true
literalCoefficientRegression =
  Coefficient.literalViscousQuadraticCoefficientClosedIsTrue

concreteFieldRegression :
  ConcreteField.concretePhysicalGalerkinVectorFieldClosed ≡ true
concreteFieldRegression =
  ConcreteField.concretePhysicalGalerkinVectorFieldClosedIsTrue

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

physicalShellReducerRegression :
  Shell.physicalTimeDependentShellReducerClosed ≡ true
physicalShellReducerRegression =
  Shell.physicalTimeDependentShellReducerClosedIsTrue

operatorCotlarReducerRegression :
  Cotlar.operatorValuedCotlarSteinReducerClosed ≡ true
operatorCotlarReducerRegression =
  Cotlar.operatorValuedCotlarSteinReducerClosedIsTrue
