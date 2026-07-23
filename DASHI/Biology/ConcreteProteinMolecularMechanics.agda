module DASHI.Biology.ConcreteProteinMolecularMechanics where

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
  ; primFloatCos
  ; primFloatLess
  )
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.MolecularMechanicsPotentialBridge as Abstract

------------------------------------------------------------------------
-- Concrete approximate-real carrier.
--
-- Float is executable and therefore supports literal finite evaluation.  It
-- is not an exact real field: roundoff, overflow, NaN, and transcendental
-- approximation remain explicit numerical obligations.

floatScalarAlgebra : Abstract.ScalarAlgebra
floatScalarAlgebra =
  record
    { Scalar = Float
    ; zero = 0.0
    ; _+_ = primFloatPlus
    ; _-_ = primFloatMinus
    ; _*_ = primFloatTimes
    }

_+f_ : Float → Float → Float
_+f_ = primFloatPlus

_-f_ : Float → Float → Float
_-f_ = primFloatMinus

_*f_ : Float → Float → Float
_*f_ = primFloatTimes

_/f_ : Float → Float → Float
_/f_ = primFloatDiv

negf : Float → Float
negf = primFloatNegate

square : Float → Float
square x = x *f x

sixthPower : Float → Float
sixthPower x = square (square x) *f square x

twelfthPower : Float → Float
twelfthPower x = square (sixthPower x)

foldFloat : List Float → Float
foldFloat [] = 0.0
foldFloat (x ∷ xs) = x +f foldFloat xs

mapFloat : {A : Set} → (A → Float) → List A → List Float
mapFloat f [] = []
mapFloat f (x ∷ xs) = f x ∷ mapFloat f xs

sumBy : {A : Set} → (A → Float) → List A → Float
sumBy f xs = foldFloat (mapFloat f xs)

------------------------------------------------------------------------
-- Three-dimensional coordinate and force carriers.

record Vec3 : Set where
  constructor vec3
  field
    x : Float
    y : Float
    z : Float

open Vec3 public

zeroVec3 : Vec3
zeroVec3 = vec3 0.0 0.0 0.0

_+v_ : Vec3 → Vec3 → Vec3
vec3 ax ay az +v vec3 bx by bz =
  vec3 (ax +f bx) (ay +f by) (az +f bz)

_-v_ : Vec3 → Vec3 → Vec3
vec3 ax ay az -v vec3 bx by bz =
  vec3 (ax -f bx) (ay -f by) (az -f bz)

scaleVec3 : Float → Vec3 → Vec3
scaleVec3 a (vec3 vx vy vz) =
  vec3 (a *f vx) (a *f vy) (a *f vz)

dot : Vec3 → Vec3 → Float
dot (vec3 ax ay az) (vec3 bx by bz) =
  ax *f bx +f (ay *f by +f az *f bz)

normSq : Vec3 → Float
normSq v = dot v v

norm : Vec3 → Float
norm v = primFloatSqrt (normSq v)

distanceSq : Vec3 → Vec3 → Float
distanceSq a b = normSq (a -v b)

distance : Vec3 → Vec3 → Float
distance a b = primFloatSqrt (distanceSq a b)

------------------------------------------------------------------------
-- Protein-facing atom metadata.

data Element : Set where
  hydrogen carbon nitrogen oxygen sulfur phosphorus otherElement : Element

record Atom : Set where
  constructor atom
  field
    atomIndex : Nat
    element : Element
    partialCharge : Float
    mass : Float
    residueIdentity : String
    chainIdentity : String
    position : Vec3
    velocity : Vec3

open Atom public

record Bond : Set where
  constructor bond
  field
    bondLeft : Atom
    bondRight : Atom
    bondStiffness : Float
    equilibriumBondLength : Float

open Bond public

record AngleInteraction : Set where
  constructor angleInteraction
  field
    angleLeft : Atom
    angleCentre : Atom
    angleRight : Atom
    angleStiffness : Float
    equilibriumAngle : Float
    measuredAngle : Float

open AngleInteraction public

record TorsionInteraction : Set where
  constructor torsionInteraction
  field
    torsionA : Atom
    torsionB : Atom
    torsionC : Atom
    torsionD : Atom
    torsionAmplitude : Float
    torsionMultiplicity : Float
    torsionPhase : Float
    measuredDihedral : Float

open TorsionInteraction public

record NonbondedPair : Set where
  constructor nonbondedPair
  field
    pairLeft : Atom
    pairRight : Atom
    dielectricFactor : Float
    lennardJonesEpsilon : Float
    lennardJonesSigma : Float

open NonbondedPair public

record PeriodicBox : Set where
  constructor periodicBox
  field
    boxX : Float
    boxY : Float
    boxZ : Float

record SolventState : Set where
  constructor solventState
  field
    solventName : String
    ionicStrength : Float
    relativePermittivity : Float
    explicitSolvent : Bool

record ProteinConfiguration : Set where
  constructor proteinConfiguration
  field
    atoms : List Atom
    bonds : List Bond
    angles : List AngleInteraction
    torsions : List TorsionInteraction
    nonbondedPairs : List NonbondedPair
    periodicCell : PeriodicBox
    solvent : SolventState

open ProteinConfiguration public

length : {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = 1 + length xs

proteinAtomCount : ProteinConfiguration → Nat
proteinAtomCount c = length (atoms c)

record ForceOnAtom : Set where
  constructor forceOnAtom
  field
    forceAtomIndex : Nat
    forceVector : Vec3

open ForceOnAtom public

ProteinForceField : Set
ProteinForceField = List ForceOnAtom

concreteProteinCarrier : Abstract.MolecularCarrier floatScalarAlgebra
concreteProteinCarrier =
  record
    { Atom = Atom
    ; Configuration = ProteinConfiguration
    ; ForceField = ProteinForceField
    ; atomCount = proteinAtomCount
    }

------------------------------------------------------------------------
-- Literal finite potential terms.

bondEnergy : Bond → Float
bondEnergy b =
  bondStiffness b *f
  square (distance (position (bondLeft b)) (position (bondRight b))
          -f equilibriumBondLength b)

angleEnergy : AngleInteraction → Float
angleEnergy a =
  angleStiffness a *f
  square (measuredAngle a -f equilibriumAngle a)

torsionEnergy : TorsionInteraction → Float
torsionEnergy t =
  torsionAmplitude t *f
  (1.0 +f primFloatCos
    (torsionMultiplicity t *f measuredDihedral t -f torsionPhase t))

coulombEnergy : NonbondedPair → Float
coulombEnergy p =
  (partialCharge (pairLeft p) *f partialCharge (pairRight p)) /f
  (dielectricFactor p *f
   distance (position (pairLeft p)) (position (pairRight p)))

lennardJonesEnergy : NonbondedPair → Float
lennardJonesEnergy p =
  4.0 *f lennardJonesEpsilon p *f
  (twelfthPower ratio -f sixthPower ratio)
  where
    ratio : Float
    ratio = lennardJonesSigma p /f
      distance (position (pairLeft p)) (position (pairRight p))

concreteBondPotential : ProteinConfiguration → Float
concreteBondPotential c = sumBy bondEnergy (bonds c)

concreteAnglePotential : ProteinConfiguration → Float
concreteAnglePotential c = sumBy angleEnergy (angles c)

concreteTorsionPotential : ProteinConfiguration → Float
concreteTorsionPotential c = sumBy torsionEnergy (torsions c)

concreteCoulombPotential : ProteinConfiguration → Float
concreteCoulombPotential c = sumBy coulombEnergy (nonbondedPairs c)

concreteVanDerWaalsPotential : ProteinConfiguration → Float
concreteVanDerWaalsPotential c =
  sumBy lennardJonesEnergy (nonbondedPairs c)

concreteMolecularPotential :
  Abstract.MolecularPotential floatScalarAlgebra concreteProteinCarrier
concreteMolecularPotential =
  record
    { bondPotential = concreteBondPotential
    ; anglePotential = concreteAnglePotential
    ; torsionPotential = concreteTorsionPotential
    ; electrostaticPotentialEnergy = concreteCoulombPotential
    ; vanDerWaalsPotential = concreteVanDerWaalsPotential
    }

concreteTotalPotential : ProteinConfiguration → Float
concreteTotalPotential =
  Abstract.totalPotential concreteMolecularPotential

concretePotentialDecomposition :
  (c : ProteinConfiguration) →
  concreteTotalPotential c ≡
  concreteBondPotential c +f
  (concreteAnglePotential c +f
   (concreteTorsionPotential c +f
    (concreteCoulombPotential c +f
     concreteVanDerWaalsPotential c)))
concretePotentialDecomposition c = refl

------------------------------------------------------------------------
-- Executable comparisons and domain guards.

lowerEnergy : ProteinConfiguration → ProteinConfiguration → Bool
lowerEnergy a b = primFloatLess (concreteTotalPotential a)
                               (concreteTotalPotential b)

positiveFloat : Float → Bool
positiveFloat x = primFloatLess 0.0 x

nonzeroSeparation : NonbondedPair → Bool
nonzeroSeparation p =
  primFloatLess 0.0
    (distanceSq (position (pairLeft p)) (position (pairRight p)))

all : {A : Set} → (A → Bool) → List A → Bool
all p [] = true
all p (x ∷ xs) with p x
... | true = all p xs
... | false = false

collisionFree : ProteinConfiguration → Bool
collisionFree c = all nonzeroSeparation (nonbondedPairs c)

record FloatEvaluationBoundary : Set where
  field
    finiteInputs : Bool
    noNaNInputs : Bool
    noInfiniteInputs : Bool
    positiveMasses : Bool
    positiveBondStiffnesses : Bool
    positiveDielectricFactors : Bool
    collisionFreePairs : Bool
    roundoffErrorBound : Float
    transcendentalErrorBound : Float

open FloatEvaluationBoundary public
