module DASHI.Biology.MolecularMechanicsCartesianProduction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using
  ( Float
  ; primFloatPlus
  ; primFloatMinus
  ; primFloatTimes
  ; primFloatDiv
  ; primFloatNegate
  ; primFloatSin
  ; primFloatLess
  )
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Biology.ConcreteProteinMolecularMechanics
open import DASHI.Biology.MolecularMechanicsForcesDynamics

------------------------------------------------------------------------
-- Cartesian vector geometry.

cross : Vec3 → Vec3 → Vec3
cross (vec3 ax ay az) (vec3 bx by bz) =
  vec3 (ay *f bz -f az *f by)
       (az *f bx -f ax *f bz)
       (ax *f by -f ay *f bx)

normalise : Vec3 → Vec3
normalise v = scaleVec3 (1.0 /f norm v) v

nonzeroVec3 : Vec3 → Bool
nonzeroVec3 v = primFloatLess 0.0 (normSq v)

angleLeftBond : AngleInteraction → Vec3
angleLeftBond a = position (angleLeft a) -v position (angleCentre a)

angleRightBond : AngleInteraction → Vec3
angleRightBond a = position (angleRight a) -v position (angleCentre a)

angleSine : AngleInteraction → Float
angleSine a = primFloatSin (measuredAngle a)

angleChartAdmissible : AngleInteraction → Bool
angleChartAdmissible a with nonzeroVec3 (angleLeftBond a)
... | false = false
... | true with nonzeroVec3 (angleRightBond a)
...   | false = false
...   | true =
  primFloatLess 0.0
    (square (angleSine a))

angleEnergyDerivative : AngleInteraction → Float
angleEnergyDerivative a =
  2.0 *f angleStiffness a *f
  (measuredAngle a -f equilibriumAngle a)

-- For u = (r_i-r_j)/|r_i-r_j| and v = (r_k-r_j)/|r_k-r_j|,
--
--   F_i = (dU/dθ) (v - cosθ u) / (|r_i-r_j| sinθ)
--   F_k = (dU/dθ) (u - cosθ v) / (|r_k-r_j| sinθ)
--   F_j = -(F_i + F_k).
--
-- The domain excludes zero bond lengths and sin θ = 0.

angleCartesianForceLeft : AngleInteraction → Vec3
angleCartesianForceLeft a =
  scaleVec3
    (angleEnergyDerivative a /f
      (norm left *f angleSine a))
    (rightUnit -v scaleVec3 cosine leftUnit)
  where
    left : Vec3
    left = angleLeftBond a

    right : Vec3
    right = angleRightBond a

    leftUnit : Vec3
    leftUnit = normalise left

    rightUnit : Vec3
    rightUnit = normalise right

    cosine : Float
    cosine = dot leftUnit rightUnit

angleCartesianForceRight : AngleInteraction → Vec3
angleCartesianForceRight a =
  scaleVec3
    (angleEnergyDerivative a /f
      (norm right *f angleSine a))
    (leftUnit -v scaleVec3 cosine rightUnit)
  where
    left : Vec3
    left = angleLeftBond a

    right : Vec3
    right = angleRightBond a

    leftUnit : Vec3
    leftUnit = normalise left

    rightUnit : Vec3
    rightUnit = normalise right

    cosine : Float
    cosine = dot leftUnit rightUnit

angleCartesianForceCentre : AngleInteraction → Vec3
angleCartesianForceCentre a =
  negVec3
    (angleCartesianForceLeft a +v angleCartesianForceRight a)

angleForceConservation :
  (a : AngleInteraction) →
  angleCartesianForceLeft a +v
  (angleCartesianForceCentre a +v angleCartesianForceRight a)
  ≡
  angleCartesianForceLeft a +v
  (negVec3 (angleCartesianForceLeft a +v angleCartesianForceRight a)
   +v angleCartesianForceRight a)
angleForceConservation a = refl

------------------------------------------------------------------------
-- Full Cartesian torsion forces.
--
-- b1 = r_B-r_A, b2 = r_C-r_B, b3 = r_D-r_C
-- n1 = b1×b2, n2 = b2×b3.
-- The dihedral chart excludes |b2| = 0, |n1| = 0, and |n2| = 0.

bond1 : TorsionInteraction → Vec3
bond1 t = position (torsionB t) -v position (torsionA t)

bond2 : TorsionInteraction → Vec3
bond2 t = position (torsionC t) -v position (torsionB t)

bond3 : TorsionInteraction → Vec3
bond3 t = position (torsionD t) -v position (torsionC t)

torsionNormal1 : TorsionInteraction → Vec3
torsionNormal1 t = cross (bond1 t) (bond2 t)

torsionNormal2 : TorsionInteraction → Vec3
torsionNormal2 t = cross (bond2 t) (bond3 t)

torsionChartAdmissible : TorsionInteraction → Bool
torsionChartAdmissible t with nonzeroVec3 (bond2 t)
... | false = false
... | true with nonzeroVec3 (torsionNormal1 t)
...   | false = false
...   | true = nonzeroVec3 (torsionNormal2 t)

torsionEnergyDerivative : TorsionInteraction → Float
torsionEnergyDerivative t =
  primFloatNegate
    (torsionAmplitude t *f torsionMultiplicity t *f
     primFloatSin
       (torsionMultiplicity t *f measuredDihedral t -f
        torsionPhase t))

dihedralGradientA : TorsionInteraction → Vec3
dihedralGradientA t =
  scaleVec3
    (primFloatNegate
      (norm (bond2 t) /f normSq (torsionNormal1 t)))
    (torsionNormal1 t)

dihedralGradientD : TorsionInteraction → Vec3
dihedralGradientD t =
  scaleVec3
    (norm (bond2 t) /f normSq (torsionNormal2 t))
    (torsionNormal2 t)

dihedralGradientB : TorsionInteraction → Vec3
dihedralGradientB t =
  scaleVec3 (a -f 1.0) (dihedralGradientA t)
  -v scaleVec3 c (dihedralGradientD t)
  where
    denominator : Float
    denominator = normSq (bond2 t)

    a : Float
    a = dot (bond1 t) (bond2 t) /f denominator

    c : Float
    c = dot (bond3 t) (bond2 t) /f denominator

dihedralGradientC : TorsionInteraction → Vec3
dihedralGradientC t =
  scaleVec3 (c -f 1.0) (dihedralGradientD t)
  -v scaleVec3 a (dihedralGradientA t)
  where
    denominator : Float
    denominator = normSq (bond2 t)

    a : Float
    a = dot (bond1 t) (bond2 t) /f denominator

    c : Float
    c = dot (bond3 t) (bond2 t) /f denominator

torsionCartesianForceA : TorsionInteraction → Vec3
torsionCartesianForceA t =
  scaleVec3 (primFloatNegate (torsionEnergyDerivative t))
    (dihedralGradientA t)

torsionCartesianForceB : TorsionInteraction → Vec3
torsionCartesianForceB t =
  scaleVec3 (primFloatNegate (torsionEnergyDerivative t))
    (dihedralGradientB t)

torsionCartesianForceC : TorsionInteraction → Vec3
torsionCartesianForceC t =
  scaleVec3 (primFloatNegate (torsionEnergyDerivative t))
    (dihedralGradientC t)

torsionCartesianForceD : TorsionInteraction → Vec3
torsionCartesianForceD t =
  scaleVec3 (primFloatNegate (torsionEnergyDerivative t))
    (dihedralGradientD t)

------------------------------------------------------------------------
-- Force contributions and aggregation by atom index.

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc a) (suc b) = natEqual a b

addContribution : ForceOnAtom → ProteinForceField → ProteinForceField
addContribution f [] = f ∷ []
addContribution f (g ∷ gs) with natEqual (forceAtomIndex f) (forceAtomIndex g)
... | true =
  forceOnAtom
    (forceAtomIndex g)
    (forceVector f +v forceVector g)
  ∷ gs
... | false = g ∷ addContribution f gs

aggregateForceField : ProteinForceField → ProteinForceField
aggregateForceField [] = []
aggregateForceField (f ∷ fs) = addContribution f (aggregateForceField fs)

netForceFor : Nat → ProteinForceField → Vec3
netForceFor index [] = zeroVec3
netForceFor index (f ∷ fs) with natEqual index (forceAtomIndex f)
... | true = forceVector f +v netForceFor index fs
... | false = netForceFor index fs

aggregateTermwiseForce :
  TermwiseForceEvaluation →
  ProteinConfiguration →
  ProteinForceField
aggregateTermwiseForce F c =
  aggregateForceField (termwiseTotalForce F c)

angleForceContributions : AngleInteraction → ProteinForceField
angleForceContributions a =
  forceOnAtom (atomIndex (angleLeft a)) (angleCartesianForceLeft a)
  ∷ forceOnAtom (atomIndex (angleCentre a)) (angleCartesianForceCentre a)
  ∷ forceOnAtom (atomIndex (angleRight a)) (angleCartesianForceRight a)
  ∷ []

torsionForceContributions : TorsionInteraction → ProteinForceField
torsionForceContributions t =
  forceOnAtom (atomIndex (torsionA t)) (torsionCartesianForceA t)
  ∷ forceOnAtom (atomIndex (torsionB t)) (torsionCartesianForceB t)
  ∷ forceOnAtom (atomIndex (torsionC t)) (torsionCartesianForceC t)
  ∷ forceOnAtom (atomIndex (torsionD t)) (torsionCartesianForceD t)
  ∷ []

------------------------------------------------------------------------
-- Complete velocity Verlet.

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

predictVerletAtom : Float → DynamicAtom → DynamicAtom
predictVerletAtom dt a =
  dynamicAtom
    (dynamicIndex a)
    (dynamicMass a)
    (positionHalfStep dt a)
    (velocityHalfStep dt a)
    (dynamicForce a)
    (frictionCoefficient a)
    (stochasticImpulse a)

finishVerletAtom : Float → DynamicAtom → DynamicAtom
finishVerletAtom dt a =
  dynamicAtom
    (dynamicIndex a)
    (dynamicMass a)
    (dynamicPosition a)
    (dynamicVelocity a +v
      scaleVec3 (half *f dt) (acceleration a))
    (dynamicForce a)
    (frictionCoefficient a)
    (stochasticImpulse a)

completeVelocityVerlet :
  VelocityVerletStep →
  List DynamicAtom →
  List DynamicAtom
completeVelocityVerlet step state =
  mapList (finishVerletAtom (timestep step))
    (updateForces step
      (mapList (predictVerletAtom (timestep step)) state))

record CartesianProductionBoundary : Set where
  field
    allAnglesAdmissible : Bool
    allTorsionsAdmissible : Bool
    angleFormulaCertified : Bool
    torsionFormulaCertified : Bool
    forceAggregationIndexUnique : Bool
    forceReevaluationPreservesAtomOrder : Bool
    momentumConservationErrorBound : Float

open CartesianProductionBoundary public
