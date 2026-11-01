module DASHI.Physics.Closure.NSTriadKNLuoInageDirectionalAbsorptionComparisonExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Shin-ichi Inage.
-- Title: "Conditional Regularity of the Three-Dimensional Navier-Stokes
-- Equations via High-High Triadic Absorption".
-- Preprint DOI: 10.20944/preprints202603.1591.v1.
-- Status: non-peer-reviewed preprint.
--
-- Author: Shin-ichi Inage.
-- Title: "Structural Reduction Framework and Residence-Time Compression of
-- Coherent Same-Scale Triadic Interactions in the 3D Navier-Stokes Equations".
-- DOI: 10.3390/math14091410.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- PURPOSE
-- Make the logical comparison requested by the source audit into checked
-- mathematics rather than prose:
--
--   directional/geometric interaction bound
--        -> pointwise viscous absorption
--        -> duration-weighted integrated absorption.
--
-- The first arrow needs a genuine producer estimate comparing the geometric
-- contribution with eta times viscosity.  The second arrow is proved by the
-- existing residence-time summation theorem.  Therefore pointwise F3-style
-- directional depletion, pointwise Inage absorption and integrated Inage
-- absorption remain distinct theorem strengths.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNLuoIntegratedHighHighResidenceExact as Residence

record StrictAbsorptionParameters : Set where
  constructor strict-absorption-parameters
  field
    residenceParameters : Residence.ResidenceParameters
    etaBelowOne : Residence.eta residenceParameters < 1ℚ

open StrictAbsorptionParameters public

record DirectionalAbsorptionCell
    (parameters : StrictAbsorptionParameters) : Set where
  constructor directional-absorption-cell
  field
    duration transfer viscous residual geometricContribution : ℚ

    durationNonnegative : 0ℚ ≤ duration
    transferNonnegative : 0ℚ ≤ transfer
    viscousNonnegative : 0ℚ ≤ viscous
    residualNonnegative : 0ℚ ≤ residual
    geometricContributionNonnegative :
      0ℚ ≤ geometricContribution

    directionalInteractionBound :
      transfer ≤ geometricContribution + residual

    geometricViscousAbsorption :
      geometricContribution
      ≤ Residence.eta (residenceParameters parameters) * viscous

open DirectionalAbsorptionCell public

PointwiseDirectionalBound :
  (parameters : StrictAbsorptionParameters) →
  DirectionalAbsorptionCell parameters → Set
PointwiseDirectionalBound parameters cell =
  transfer cell ≤ geometricContribution cell + residual cell

PointwiseHHAbsorption :
  (parameters : StrictAbsorptionParameters) →
  DirectionalAbsorptionCell parameters → Set
PointwiseHHAbsorption parameters cell =
  transfer cell
  ≤ Residence.eta (residenceParameters parameters) * viscous cell
    + residual cell

directionalBoundImpliesPointwiseAbsorption :
  (parameters : StrictAbsorptionParameters) →
  (cell : DirectionalAbsorptionCell parameters) →
  PointwiseHHAbsorption parameters cell
directionalBoundImpliesPointwiseAbsorption parameters cell =
  ℚₚ.≤-trans
    (directionalInteractionBound cell)
    (ℚₚ.+-mono-≤
      (geometricViscousAbsorption cell)
      ℚₚ.≤-refl)

asResidenceCell :
  (parameters : StrictAbsorptionParameters) →
  DirectionalAbsorptionCell parameters →
  Residence.ResidenceCell (residenceParameters parameters)
asResidenceCell parameters cell =
  Residence.residence-cell
    (duration cell)
    (transfer cell)
    0ℚ
    (viscous cell)
    (residual cell)
    0ℚ
    (durationNonnegative cell)
    (transferNonnegative cell)
    ℚₚ.≤-refl
    (viscousNonnegative cell)
    (residualNonnegative cell)
    ℚₚ.≤-refl
    (directionalBoundImpliesPointwiseAbsorption parameters cell)
    ℚₚ.≤-refl

asResidenceCells :
  (parameters : StrictAbsorptionParameters) →
  List (DirectionalAbsorptionCell parameters) →
  List (Residence.ResidenceCell (residenceParameters parameters))
asResidenceCells parameters [] = []
asResidenceCells parameters (cell ∷ cells) =
  asResidenceCell parameters cell
  ∷ asResidenceCells parameters cells

IntegratedHHAbsorption :
  (parameters : StrictAbsorptionParameters) →
  List (DirectionalAbsorptionCell parameters) → Set
IntegratedHHAbsorption parameters cells =
  Residence.integratedGoodTransfer
    (residenceParameters parameters)
    (asResidenceCells parameters cells)
  ≤
  Residence.eta (residenceParameters parameters)
    * Residence.integratedViscosity
        (residenceParameters parameters)
        (asResidenceCells parameters cells)
  + Residence.integratedResidual
      (residenceParameters parameters)
      (asResidenceCells parameters cells)

pointwiseAbsorptionImpliesIntegratedAbsorption :
  (parameters : StrictAbsorptionParameters) →
  (cells : List (DirectionalAbsorptionCell parameters)) →
  IntegratedHHAbsorption parameters cells
pointwiseAbsorptionImpliesIntegratedAbsorption parameters cells =
  Residence.integratedGoodAbsorption
    (residenceParameters parameters)
    (asResidenceCells parameters cells)

record DirectionalToIntegratedAbsorption
    (parameters : StrictAbsorptionParameters) : Set where
  constructor directional-to-integrated-absorption
  field
    cells : List (DirectionalAbsorptionCell parameters)

open DirectionalToIntegratedAbsorption public

comparisonPointwiseAbsorption :
  (parameters : StrictAbsorptionParameters) →
  (comparison : DirectionalToIntegratedAbsorption parameters) →
  (cell : DirectionalAbsorptionCell parameters) →
  PointwiseHHAbsorption parameters cell
comparisonPointwiseAbsorption parameters comparison =
  directionalBoundImpliesPointwiseAbsorption parameters

comparisonIntegratedAbsorption :
  (parameters : StrictAbsorptionParameters) →
  (comparison : DirectionalToIntegratedAbsorption parameters) →
  IntegratedHHAbsorption parameters (cells comparison)
comparisonIntegratedAbsorption parameters comparison =
  pointwiseAbsorptionImpliesIntegratedAbsorption
    parameters (cells comparison)
