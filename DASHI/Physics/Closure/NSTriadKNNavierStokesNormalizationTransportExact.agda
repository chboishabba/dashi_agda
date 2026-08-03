module DASHI.Physics.Closure.NSTriadKNNavierStokesNormalizationTransportExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Edgar Buckingham.
-- Title: "On Physically Similar Systems; Illustrations of the Use of
-- Dimensional Equations".
-- Physical Review 4 (1914), 345--376.
-- DOI: 10.1103/PhysRev.4.345.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- PURPOSE
-- Own the general physical-to-normalized Navier--Stokes transport separately
-- from Luo's special unit-viscosity source.  Exact dimensional identities are
-- machine checked here; concrete continuum equation, energy and terminal-window
-- transports remain proof-relevant fields to be inhabited by the official
-- solution construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Units.MechanicalDimensionExact as Dimension
import DASHI.Physics.Limits.PhysicsLimitCommutingSquare as Limits
open import DASHI.Physics.YangMills.CompactLieProofLevel

record NavierStokesTermDimensionReceipt : Set where
  field
    timeDerivativeHasAccelerationDimension :
      Dimension.velocityDimension ⊗ᴰ Dimension.frequencyDimension
      ≡ Dimension.accelerationDimension

    advectionHasAccelerationDimension :
      Dimension.velocityDimension ⊗ᴰ Dimension.velocityGradientDimension
      ≡ Dimension.accelerationDimension

    pressureGradientMatchesDensityAcceleration :
      Dimension.pressureDimension ⊗ᴰ Dimension.inverseLengthDimension
      ≡ Dimension.massDensityDimension ⊗ᴰ Dimension.accelerationDimension

    viscosityTimesLaplacianHasAccelerationDimension :
      Dimension.kinematicViscosityDimension
        ⊗ᴰ Dimension.laplacianVelocityDimension
      ≡ Dimension.accelerationDimension

    integratedSpecificDissipationMatchesSpecificEnergy :
      Dimension.specificDissipationRateDimension ⊗ᴰ Dimension.timeDimension
      ≡ Dimension.speedSquaredDimension

open NavierStokesTermDimensionReceipt public

canonicalNavierStokesTermDimensionReceipt :
  NavierStokesTermDimensionReceipt
canonicalNavierStokesTermDimensionReceipt = record
  { timeDerivativeHasAccelerationDimension =
      Dimension.velocityTimeDerivativeIsAcceleration
  ; advectionHasAccelerationDimension =
      Dimension.advectionIsAcceleration
  ; pressureGradientMatchesDensityAcceleration =
      Dimension.pressureGradientMatchesDensityAcceleration
  ; viscosityTimesLaplacianHasAccelerationDimension =
      Dimension.viscousLaplacianIsAcceleration
  ; integratedSpecificDissipationMatchesSpecificEnergy =
      Dimension.specificDissipationIntegratedInTimeIsSpecificEnergy
  }

record GeneralNavierStokesNormalization
    (PhysicalEquation NormalizedEquation : Set)
    (PhysicalEnergyIdentity NormalizedEnergyIdentity : Set)
    (PhysicalTerminalWindow NormalizedTerminalWindow : Set) : Set₁ where
  field
    equationNormalization : PhysicalEquation → NormalizedEquation

    physicalEnergyIdentity :
      PhysicalEquation → PhysicalEnergyIdentity
    normalizedEnergyIdentity :
      NormalizedEquation → NormalizedEnergyIdentity
    energyNormalization :
      PhysicalEnergyIdentity → NormalizedEnergyIdentity

    energyIdentityCommutes :
      (equation : PhysicalEquation) →
      normalizedEnergyIdentity (equationNormalization equation)
      ≡ energyNormalization (physicalEnergyIdentity equation)

    physicalTerminalWindow :
      PhysicalEquation → PhysicalTerminalWindow
    normalizedTerminalWindow :
      NormalizedEquation → NormalizedTerminalWindow
    terminalWindowNormalization :
      PhysicalTerminalWindow → NormalizedTerminalWindow

    terminalWindowCommutes :
      (equation : PhysicalEquation) →
      normalizedTerminalWindow (equationNormalization equation)
      ≡ terminalWindowNormalization (physicalTerminalWindow equation)

    InverseReynoldsCoefficient : Set
    inverseReynoldsCoefficientSelected : InverseReynoldsCoefficient

    normalizedEquationRetainsInverseReynolds :
      NormalizedEquation → InverseReynoldsCoefficient → Set

    normalizedEquationCoefficientMeaning :
      (equation : PhysicalEquation) →
      normalizedEquationRetainsInverseReynolds
        (equationNormalization equation)
        inverseReynoldsCoefficientSelected

open GeneralNavierStokesNormalization public

energyIdentitySquare :
  ∀ {PhysicalEquation NormalizedEquation}
    {PhysicalEnergyIdentity NormalizedEnergyIdentity}
    {PhysicalTerminalWindow NormalizedTerminalWindow} →
  (normalization : GeneralNavierStokesNormalization
    PhysicalEquation NormalizedEquation
    PhysicalEnergyIdentity NormalizedEnergyIdentity
    PhysicalTerminalWindow NormalizedTerminalWindow) →
  Limits.CommutingSquare
    PhysicalEquation NormalizedEquation
    PhysicalEnergyIdentity NormalizedEnergyIdentity
energyIdentitySquare normalization = record
  { top = equationNormalization normalization
  ; left = physicalEnergyIdentity normalization
  ; right = normalizedEnergyIdentity normalization
  ; bottom = energyNormalization normalization
  }

energyIdentityExactCommutation :
  ∀ {PhysicalEquation NormalizedEquation}
    {PhysicalEnergyIdentity NormalizedEnergyIdentity}
    {PhysicalTerminalWindow NormalizedTerminalWindow} →
  (normalization : GeneralNavierStokesNormalization
    PhysicalEquation NormalizedEquation
    PhysicalEnergyIdentity NormalizedEnergyIdentity
    PhysicalTerminalWindow NormalizedTerminalWindow) →
  Limits.ExactCommutation (energyIdentitySquare normalization)
energyIdentityExactCommutation normalization = record
  { pathsAgree = energyIdentityCommutes normalization }

terminalWindowSquare :
  ∀ {PhysicalEquation NormalizedEquation}
    {PhysicalEnergyIdentity NormalizedEnergyIdentity}
    {PhysicalTerminalWindow NormalizedTerminalWindow} →
  (normalization : GeneralNavierStokesNormalization
    PhysicalEquation NormalizedEquation
    PhysicalEnergyIdentity NormalizedEnergyIdentity
    PhysicalTerminalWindow NormalizedTerminalWindow) →
  Limits.CommutingSquare
    PhysicalEquation NormalizedEquation
    PhysicalTerminalWindow NormalizedTerminalWindow
terminalWindowSquare normalization = record
  { top = equationNormalization normalization
  ; left = physicalTerminalWindow normalization
  ; right = normalizedTerminalWindow normalization
  ; bottom = terminalWindowNormalization normalization
  }

terminalWindowExactCommutation :
  ∀ {PhysicalEquation NormalizedEquation}
    {PhysicalEnergyIdentity NormalizedEnergyIdentity}
    {PhysicalTerminalWindow NormalizedTerminalWindow} →
  (normalization : GeneralNavierStokesNormalization
    PhysicalEquation NormalizedEquation
    PhysicalEnergyIdentity NormalizedEnergyIdentity
    PhysicalTerminalWindow NormalizedTerminalWindow) →
  Limits.ExactCommutation (terminalWindowSquare normalization)
terminalWindowExactCommutation normalization = record
  { pathsAgree = terminalWindowCommutes normalization }

navierStokesTermDimensionLevel : ProofLevel
navierStokesTermDimensionLevel = machineChecked

generalEquationTransportLevel : ProofLevel
generalEquationTransportLevel = conditional

energyIdentityTransportLevel : ProofLevel
energyIdentityTransportLevel = conditional

terminalWindowTransportLevel : ProofLevel
terminalWindowTransportLevel = conditional
