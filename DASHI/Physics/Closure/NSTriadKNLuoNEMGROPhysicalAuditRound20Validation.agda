module DASHI.Physics.Closure.NSTriadKNLuoNEMGROPhysicalAuditRound20Validation where

------------------------------------------------------------------------
-- Cumulative validation root.
--
-- Imports Round Nineteen and checks the concrete NEMGRO audit tranche:
--
-- * exact gradient-strain sign and antisymmetric cancellation;
-- * affine projected-Korn counterexample;
-- * divergence-free cutoff-curl plateau core;
-- * amplitude-scaling obstruction;
-- * correct 3D L4 interpolation and sixth-power remainder;
-- * coupling-parameter sign obstruction;
-- * spectral-projector inverse-gap crossing;
-- * exact periodic Biot--Savart nonzero-mode strain symbol;
-- * squared directional triple-product factor;
-- * finite directional high-high shell summation.
--
-- No principal-value periodic kernel, continuum Calderon--Zygmund estimate,
-- PDE-produced bad-time residence compression, strict universal viscosity
-- margin, or unconditional Navier--Stokes regularity result is asserted.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLuoUnconditionalAbsorptionRound19Validation
import DASHI.Physics.Closure.NSTriadKNLuoPositiveStrainGradientSignExact
import DASHI.Physics.Closure.NSTriadKNLuoLocalizedProjectedKornAffineCounterexampleExact
import DASHI.Physics.Closure.NSTriadKNLuoCompactSupportPositiveStrainCoreExact
import DASHI.Physics.Closure.NSTriadKNLuoAmplitudeScalingStaticRigidityNoGoExact
import DASHI.Physics.Closure.NSTriadKNLuoThreeDimensionalGradientL4InterpolationExact
import DASHI.Physics.Closure.NSTriadKNLuoCouplingParameterSignNoGoExact
import DASHI.Physics.Closure.NSTriadKNLuoSpectralProjectorGapDependenceExact
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartMultiplierExact
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalKernelTripleProductExact
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDirectionalHHBridgeExact
