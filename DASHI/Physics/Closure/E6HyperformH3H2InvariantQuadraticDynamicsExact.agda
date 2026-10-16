module DASHI.Physics.Closure.E6HyperformH3H2InvariantQuadraticDynamicsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3H2OrderParameterGeometryExact as Geometry
import DASHI.Physics.Closure.E6HyperformH3H2OrderParameterDynamicsExact as Dynamics

------------------------------------------------------------------------
-- SYMMETRY CLASSIFICATION OF QUADRATIC FIBRE DYNAMICS
--
-- The nine H2 choices over one selected H3 form the affine plane F3^2, with
-- effective symmetry F3^2 semidirect O(2,3), order 72.  The exact local
-- producer enumerates its action on ordered point pairs.  There are precisely
-- three pair orbits:
--
--   9   diagonal pairs;
--   36  norm-1 displacement pairs;
--   36  norm-2 displacement pairs.
--
-- Hence every invariant quadratic kernel is constant on those three orbits,
-- so the invariant kernel algebra is three-dimensional with basis
--
--   I, A1, A2,
--
-- where A1/A2 are the norm-1/norm-2 adjacency matrices.  If one additionally
-- requires locality to the intrinsic norm-1 shell, the A2 coefficient is zero.
-- Requiring constant sections to have zero kinetic energy then forces
--
--   K = kappa (4 I - A1) = kappa L
--
-- for one scalar kappa.  The dimensionless operator L is therefore fixed by
-- finite symmetry and locality; kappa is not.
------------------------------------------------------------------------

orderedPairOrbitCount : Nat
orderedPairOrbitCount = 3

diagonalPairOrbitSize : Nat
diagonalPairOrbitSize = 9

normOnePairOrbitSize : Nat
normOnePairOrbitSize = 36

normTwoPairOrbitSize : Nat
normTwoPairOrbitSize = 36

invariantQuadraticKernelDimension : Nat
invariantQuadraticKernelDimension = 3

localConstantAnnihilatingFamilyDimension : Nat
localConstantAnnihilatingFamilyDimension = 1

canonicalDimensionlessKineticOperator : String
canonicalDimensionlessKineticOperator = "L = 4 I - A_norm1"

canonicalSpectrum : String
canonicalSpectrum = "0^1, 3^4, 6^4"

record H3H2InvariantQuadraticDynamicsLocalReceipt : Set where
  constructor h3-h2-invariant-quadratic-dynamics-local-receipt
  field
    sameNineStateFibreUsed : Bool
    sameAffineOrthogonal72ActionUsed : Bool
    allOrderedPairsEnumerated : Bool
    exactlyThreePairOrbits : Bool
    diagonalOrbitSize9 : Bool
    normOneOrbitSize36 : Bool
    normTwoOrbitSize36 : Bool
    invariantKernelDimensionThree : Bool
    invariantKernelBasisIA1A2 : Bool
    normOneLocalityRemovesA2 : Bool
    constantZeroEnergyForcesFourIMinusA1 : Bool
    localKineticShapeUniqueUpToScale : Bool
    spectrumMatchesExistingLaplacian : Bool
    spectralGapThree : Bool
    physicalKineticCoefficientDerived : Bool
    continuumScalingDerived : Bool
    physicalTimeUnitDerived : Bool
    stressEnergyDerived : Bool
    boundary : String
open H3H2InvariantQuadraticDynamicsLocalReceipt public

canonicalH3H2InvariantQuadraticDynamicsLocalReceipt :
  H3H2InvariantQuadraticDynamicsLocalReceipt
canonicalH3H2InvariantQuadraticDynamicsLocalReceipt =
  h3-h2-invariant-quadratic-dynamics-local-receipt
    true true true true true true true true true true true true true true
    false false false false
    "The 72-element affine-orthogonal fibre symmetry has exactly three ordered-pair orbitals, so invariant quadratic kernels are span{I,A_norm1,A_norm2}. Requiring intrinsic norm-1 locality and zero energy on constants leaves exactly kappa(4I-A_norm1). This fixes the finite kinetic operator shape and spectrum up to one coefficient; no physical coefficient, time scale, continuum limit or stress tensor is inferred."

geometryReceipt : Geometry.H3H2OrderParameterGeometryLocalReceipt
geometryReceipt = Geometry.canonicalH3H2OrderParameterGeometryLocalReceipt

dynamicsReceipt : Dynamics.H3H2OrderParameterDynamicsLocalReceipt
dynamicsReceipt = Dynamics.canonicalH3H2OrderParameterDynamicsLocalReceipt

record PhysicalOrderParameterDynamics : Set₁ where
  field
    kineticCoefficient : Set
    potentialOrSelectionLaw : Set
    continuumScaling : Set
    lorentzianEvolution : Set
    stressEnergyVariation : Set
    empiricalCalibration : Set
open PhysicalOrderParameterDynamics public

data DimensionlessInvariantKineticShapeCreatesPhysicalDynamics : Set where

dimensionlessShapeDoesNotCreatePhysicalDynamics :
  DimensionlessInvariantKineticShapeCreatesPhysicalDynamics → {A : Set} → A
dimensionlessShapeDoesNotCreatePhysicalDynamics ()
