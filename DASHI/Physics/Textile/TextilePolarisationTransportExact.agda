module DASHI.Physics.Textile.TextilePolarisationTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import Data.Fin as Fin

import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- NIST Optical Polarization Metrology describes a light ray by a four-element
-- Stokes vector and reflection/transmission by a 4 x 4 Mueller matrix.
-- This module reuses that metrology-level representation as a textile optical
-- response fibre.  It is not a full Maxwell, coherence, or Jones-amplitude
-- solver.
------------------------------------------------------------------------

nistPolarisationMetrologyTitle : String
nistPolarisationMetrologyTitle = "NIST Optical Polarization Metrology"

StokesIndex : Set
StokesIndex = Fin.Fin 4

record StokesVector (Scalar : Set) : Set where
  constructor stokes-vector
  field
    component : StokesIndex → Scalar

open StokesVector public

record MuellerMatrix (Scalar : Set) : Set where
  constructor mueller-matrix
  field
    coefficient : StokesIndex → StokesIndex → Scalar

open MuellerMatrix public

record StokesMuellerAlgebra (Scalar : Set) : Set₁ where
  constructor stokes-mueller-algebra
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    sum4 : (StokesIndex → Scalar) → Scalar

open StokesMuellerAlgebra public

applyMueller :
  {Scalar : Set} →
  StokesMuellerAlgebra Scalar →
  MuellerMatrix Scalar →
  StokesVector Scalar →
  StokesVector Scalar
applyMueller algebra matrix input =
  stokes-vector
    (λ outputIndex →
      sum4 algebra
        (λ inputIndex →
          multiply algebra
            (coefficient matrix outputIndex inputIndex)
            (component input inputIndex)))

record TextilePolarisationReceipt
    {OpticalState Illumination OpticalObserver Radiance Scalar : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (algebra : StokesMuellerAlgebra Scalar) : Set₁ where
  constructor textile-polarisation-receipt
  field
    state : OpticalState
    observer : OpticalObserver

    incidentStokes : StokesVector Scalar
    textileMuellerResponse : MuellerMatrix Scalar
    outgoingStokes : StokesVector Scalar

    outgoingFollowsMuellerResponse :
      outgoingStokes
      ≡ applyMueller algebra textileMuellerResponse incidentStokes

    retainedRadianceObservation :
      Optical.TextileRadianceObservation model state observer

open TextilePolarisationReceipt public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data IntensityOnlyDeterminesPolarisedTextileAppearance : Set where

intensityOnlyDoesNotDeterminePolarisedTextileAppearance :
  IntensityOnlyDeterminesPolarisedTextileAppearance → ⊥
intensityOnlyDoesNotDeterminePolarisedTextileAppearance ()

data MuellerReceiptIsFullCoherentMaxwellSolution : Set where

muellerReceiptIsNotFullCoherentMaxwellSolution :
  MuellerReceiptIsFullCoherentMaxwellSolution → ⊥
muellerReceiptIsNotFullCoherentMaxwellSolution ()

data MaterialLabelDeterminesTextileMuellerMatrix : Set where

materialLabelDoesNotDetermineTextileMuellerMatrix :
  MaterialLabelDeterminesTextileMuellerMatrix → ⊥
materialLabelDoesNotDetermineTextileMuellerMatrix ()
