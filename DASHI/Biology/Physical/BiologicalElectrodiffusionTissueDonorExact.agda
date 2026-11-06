module DASHI.Biology.Physical.BiologicalElectrodiffusionTissueDonorExact where

------------------------------------------------------------------------
-- Native physical donor for the 27-site biological future quotient.
-- The existing PNP owner supplies typed SI ionic flux and Poisson charge
-- constraints. A separately sourced observation map selects tissue signals.
-- Neither selected site dynamics nor a source-calibrated parameter set is
-- invented by this module.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP
import DASHI.Biology.Physical.SIBioelectricNetworkAdapterExact as BioSI
import DASHI.Biology.Cell.BioelectricNetwork as Network
import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Biology.Physical.PlanarianControlCalibrationExact as Planarian
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube

record BiophysicalTissueSourceSocket : Set₁ where
  field
    electroDiffusion : PNP.ElectrodiffusionApplicationReceipt
    chemicalNetwork : Chemistry.ReactionNetwork
    bioelectricCarrier : Network.BioelectricNetwork
    originalSource : String
    selectedAssay : String
    originalBoundaryConditions : String
    -- Explicit physical-to-observer map: no claim it is supplied by
    -- the source review or by a canonical all-zero SI network.
    sampledTissue :
      PNP.CoupledState (PNP.fluxLaw electroDiffusion) → Bio.TissueField

open BiophysicalTissueSourceSocket public

-- Existing PNP flux law is reused without identifying a synthetic
-- Boolean junction with a measured ionic current.
sourceIonicFluxSplits :
  (socket : BiophysicalTissueSourceSocket)
  (state : PNP.CoupledState (PNP.fluxLaw (electroDiffusion socket))) →
  PNP.totalFlux (PNP.fluxLaw (electroDiffusion socket)) state
    ≡ PNP.combineFlux (PNP.fluxLaw (electroDiffusion socket))
        (PNP.diffusiveFlux (PNP.fluxLaw (electroDiffusion socket)) state)
        (PNP.electricMigrationFlux
          (PNP.fluxLaw (electroDiffusion socket)) state)
sourceIonicFluxSplits socket state =
  PNP.totalFluxDecomposition (PNP.fluxLaw (electroDiffusion socket)) state

sourcePoissonChargeAgrees :
  (socket : BiophysicalTissueSourceSocket)
  (state : PNP.CoupledState (PNP.fluxLaw (electroDiffusion socket))) →
  PNP.ionicChargeDensity
    (PNP.poissonCoupling (electroDiffusion socket)) state
  ≡ PNP.EM.chargeDensity
      (PNP.electromagneticField (electroDiffusion socket))
      (PNP.fieldState
        (PNP.fluxLaw (electroDiffusion socket)) state)
sourcePoissonChargeAgrees socket state =
  PNP.ionicAndFieldChargeDensityAgree
    (PNP.poissonCoupling (electroDiffusion socket)) state

-- Readout belongs to the original three-axis cube, not 27 labels
-- without adjacency. The map is a required source-specific input.
sampledAt :
  (socket : BiophysicalTissueSourceSocket)
  (state : PNP.CoupledState (PNP.fluxLaw (electroDiffusion socket))) →
  Cube.Ternary27Point → Bio.BiologicalState
sampledAt socket state = sampledTissue socket state

sourcePNPReference : String
sourcePNPReference = PNP.sourceDOI

canonicalSIExampleIsNotMeasuredTissue : Network.BioelectricNetwork
canonicalSIExampleIsNotMeasuredTissue = BioSI.canonicalSIBioelectricNetwork

publishedPlanarianParameterSearch : Planarian.CountObservation
publishedPlanarianParameterSearch = Planarian.hybridModelParameterSweep
