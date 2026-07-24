module DASHI.Biology.MolecularMechanicsForcesDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using
  ( Float
  ; primFloatPlus
  ; primFloatMinus
  ; primFloatTimes
  ; primFloatDiv
  ; primFloatNegate
  ; primFloatSqrt
  )
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Biology.MolecularMechanicsPotentialBridge as Abstract
open import DASHI.Biology.ConcreteProteinMolecularMechanics

------------------------------------------------------------------------
-- Vector and finite-force-field algebra.

negVec3 : Vec3 → Vec3
negVec3 v = scaleVec3 (primFloatNegate 1.0) v

sumVec3 : List Vec3 → Vec3
sumVec3 [] = zeroVec3
sumVec3 (v ∷ vs) = v +v sumVec3 vs

mapVec3 : {A : Set} → (A → Vec3) → List A → List Vec3
mapVec3 f [] = []
mapVec3 f (x ∷ xs) = f x ∷ mapVec3 f xs

unitFromTo : Vec3 → Vec3 → Vec3
unitFromTo a b = scaleVec3 (1.0 /f distance a b) (b -v a)

------------------------------------------------------------------------
-- Explicit radial derivatives for bond, Coulomb, and Lennard-Jones terms.

bondRadialMagnitude : Bond → Float
bondRadialMagnitude b =
  primFloatNegate
    (2.0 *f bondStiffness b *f
     (distance (position (bondLeft b)) (position (bondRight b))
      -f equilibriumBondLength b))

bondForceOnLeft : Bond → Vec3
bondForceOnLeft b =
  scaleVec3 (bondRadialMagnitude b)
    (unitFromTo (position (bondLeft b)) (position (bondRight b)))

bondForceOnRight : Bond → Vec3
bondForceOnRight b = negVec3 (bondForceOnLeft b)

coulombRadialMagnitude : NonbondedPair → Float
coulombRadialMagnitude p =
  (partialCharge (pairLeft p) *f partialCharge (pairRight p)) /f
  (dielectricFactor p *f square r)
  where
    r : Float
    r = distance (position (pairLeft p)) (position (pairRight p))

coulombForceOnLeft : NonbondedPair → Vec3
coulombForceOnLeft p =
  scaleVec3 (coulombRadialMagnitude p)
    (unitFromTo (position (pairLeft p)) (position (pairRight p)))

coulombForceOnRight : NonbondedPair → Vec3
coulombForceOnRight p = negVec3 (coulombForceOnLeft p)

lennardJonesRadialMagnitude : NonbondedPair → Float
lennardJonesRadialMagnitude p =
  24.0 *f lennardJonesEpsilon p /f r *f
  (2.0 *f twelfthPower ratio -f sixthPower ratio)
  where
    r : Float
    r = distance (position (pairLeft p)) (position (pairRight p))

    ratio : Float
    ratio = lennardJonesSigma p /f r

lennardJonesForceOnLeft : NonbondedPair → Vec3
lennardJonesForceOnLeft p =
  scaleVec3 (lennardJonesRadialMagnitude p)
    (unitFromTo (position (pairLeft p)) (position (pairRight p)))

lennardJonesForceOnRight : NonbondedPair → Vec3
lennardJonesForceOnRight p = negVec3 (lennardJonesForceOnLeft p)

------------------------------------------------------------------------
-- Angle and torsion Cartesian gradients require a chart with nondegenerate
-- cross products.  The implementation carries those executable kernels and
-- their claimed relationship to the scalar terms explicitly rather than
-- hiding them behind the total negative-gradient operation.

record InternalCoordinateForceKernel : Set₁ where
  field
    angleForceLeft : AngleInteraction → Vec3
    angleForceCentre : AngleInteraction → Vec3
    angleForceRight : AngleInteraction → Vec3

    torsionForceA : TorsionInteraction → Vec3
    torsionForceB : TorsionInteraction → Vec3
    torsionForceC : TorsionInteraction → Vec3
    torsionForceD : TorsionInteraction → Vec3

    angleChartNondegenerate : AngleInteraction → Bool
    torsionChartNondegenerate : TorsionInteraction → Bool

    angleNegativeGradientCertified : Bool
    torsionNegativeGradientCertified : Bool

open InternalCoordinateForceKernel public

------------------------------------------------------------------------
-- Termwise force decomposition.

record TermwiseForceEvaluation : Set₁ where
  field
    bondForces : ProteinConfiguration → ProteinForceField
    angleForces : ProteinConfiguration → ProteinForceField
    torsionForces : ProteinConfiguration → ProteinForceField
    coulombForces : ProteinConfiguration → ProteinForceField
    vanDerWaalsForces : ProteinConfiguration → ProteinForceField

open TermwiseForceEvaluation public

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

sumForceFields :
  ProteinForceField →
  ProteinForceField →
  ProteinForceField
sumForceFields = append

termwiseTotalForce :
  TermwiseForceEvaluation →
  ProteinConfiguration →
  ProteinForceField
termwiseTotalForce F c =
  sumForceFields (bondForces F c)
    (sumForceFields (angleForces F c)
      (sumForceFields (torsionForces F c)
        (sumForceFields (coulombForces F c)
          (vanDerWaalsForces F c))))

termwiseForceDecomposition :
  (F : TermwiseForceEvaluation) →
  (c : ProteinConfiguration) →
  termwiseTotalForce F c ≡
  sumForceFields (bondForces F c)
    (sumForceFields (angleForces F c)
      (sumForceFields (torsionForces F c)
        (sumForceFields (coulombForces F c)
          (vanDerWaalsForces F c))))
termwiseForceDecomposition F c = refl

termwiseNegativeGradientAction :
  TermwiseForceEvaluation →
  Abstract.NegativeGradientAction
    floatScalarAlgebra
    concreteProteinCarrier
termwiseNegativeGradientAction F =
  record
    { negativeGradient = λ potential c → termwiseTotalForce F c }

record ForceDerivativeCertificate
  (F : TermwiseForceEvaluation) : Set where
  field
    bondTermMatchesNegativeGradient : Bool
    angleTermMatchesNegativeGradient : Bool
    torsionTermMatchesNegativeGradient : Bool
    coulombTermMatchesNegativeGradient : Bool
    vanDerWaalsTermMatchesNegativeGradient : Bool
    totalGradientLinearOnAdmissibleDomain : Bool
    allPairSeparationsNonzero : Bool
    allAngleChartsNondegenerate : Bool
    allTorsionChartsNondegenerate : Bool

open ForceDerivativeCertificate public

------------------------------------------------------------------------
-- Newtonian and Langevin state evolution.

record DynamicAtom : Set where
  constructor dynamicAtom
  field
    dynamicIndex : Nat
    dynamicMass : Float
    dynamicPosition : Vec3
    dynamicVelocity : Vec3
    dynamicForce : Vec3
    frictionCoefficient : Float
    stochasticImpulse : Vec3

open DynamicAtom public

acceleration : DynamicAtom → Vec3
acceleration a = scaleVec3 (1.0 /f dynamicMass a) (dynamicForce a)

langevinAcceleration : DynamicAtom → Vec3
langevinAcceleration a =
  scaleVec3 (1.0 /f dynamicMass a)
    (dynamicForce a
     -v scaleVec3 (frictionCoefficient a) (dynamicVelocity a)
     +v stochasticImpulse a)

record VelocityVerletStep : Set₁ where
  field
    timestep : Float
    updateForces : List DynamicAtom → List DynamicAtom

open VelocityVerletStep public

half : Float
half = 0.5

positionHalfStep : Float → DynamicAtom → Vec3
positionHalfStep dt a =
  dynamicPosition a
  +v scaleVec3 dt (dynamicVelocity a)
  +v scaleVec3 (half *f square dt) (acceleration a)

velocityHalfStep : Float → DynamicAtom → Vec3
velocityHalfStep dt a =
  dynamicVelocity a
  +v scaleVec3 (half *f dt) (acceleration a)

record IntegratorValidationBoundary : Set where
  field
    positiveTimestep : Bool
    positiveMasses : Bool
    forceReevaluationAtNewPositions : Bool
    timestepBelowStabilityThreshold : Bool
    constraintSolverConverged : Bool
    neighbourListValid : Bool
    periodicMinimumImageValid : Bool
    longRangeElectrostaticsControlled : Bool
    thermostatTemperatureControlled : Bool

open IntegratorValidationBoundary public

record MolecularTrajectory : Set where
  constructor molecularTrajectory
  field
    frames : List ProteinConfiguration
    frameTimestep : Float
    temperature : Float

open MolecularTrajectory public

record TrajectoryObservables : Set₁ where
  field
    potentialEnergyTrace : MolecularTrajectory → List Float
    kineticEnergyTrace : MolecularTrajectory → List Float
    temperatureTrace : MolecularTrajectory → List Float
    radiusOfGyrationTrace : MolecularTrajectory → List Float
    rmsdTrace : MolecularTrajectory → List Float
    contactCountTrace : MolecularTrajectory → List Nat

open TrajectoryObservables public
