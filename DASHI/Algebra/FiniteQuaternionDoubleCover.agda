module DASHI.Algebra.FiniteQuaternionDoubleCover where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Unified.GRQuantumProofTerms

------------------------------------------------------------------------
-- Exact finite double cover Q8 -> V4.
--
-- Q8 is the unit-quaternion subgroup {+/-1,+/-i,+/-j,+/-k}.  Quotienting by
-- the central sign gives the Klein four subgroup of 180-degree spatial
-- rotations.  This is a nontrivial fully checked two-to-one cover and a finite
-- model of the Spin(3) double-cover mechanism.  It is not the full continuous
-- Spin(3) -> SO(3) theorem.


data Sign : Set where
  positiveSign : Sign
  negativeSign : Sign

signMultiply : Sign → Sign → Sign
signMultiply positiveSign right = right
signMultiply negativeSign positiveSign = negativeSign
signMultiply negativeSign negativeSign = positiveSign


data QuaternionBasis : Set where
  basisOne basisI basisJ basisK : QuaternionBasis

record Q8 : Set where
  constructor quaternion
  field
    sign : Sign
    basis : QuaternionBasis
open Q8 public

record SignedBasis : Set where
  constructor signed-basis
  field
    productSign : Sign
    productBasis : QuaternionBasis
open SignedBasis public

basisMultiply : QuaternionBasis → QuaternionBasis → SignedBasis
basisMultiply basisOne right = signed-basis positiveSign right
basisMultiply basisI basisOne = signed-basis positiveSign basisI
basisMultiply basisI basisI = signed-basis negativeSign basisOne
basisMultiply basisI basisJ = signed-basis positiveSign basisK
basisMultiply basisI basisK = signed-basis negativeSign basisJ
basisMultiply basisJ basisOne = signed-basis positiveSign basisJ
basisMultiply basisJ basisI = signed-basis negativeSign basisK
basisMultiply basisJ basisJ = signed-basis negativeSign basisOne
basisMultiply basisJ basisK = signed-basis positiveSign basisI
basisMultiply basisK basisOne = signed-basis positiveSign basisK
basisMultiply basisK basisI = signed-basis positiveSign basisJ
basisMultiply basisK basisJ = signed-basis negativeSign basisI
basisMultiply basisK basisK = signed-basis negativeSign basisOne

q8Multiply : Q8 → Q8 → Q8
q8Multiply (quaternion leftSign leftBasis) (quaternion rightSign rightBasis)
  with basisMultiply leftBasis rightBasis
... | signed-basis basisSign resultBasis =
  quaternion
    (signMultiply (signMultiply leftSign rightSign) basisSign)
    resultBasis

plusOne : Q8
plusOne = quaternion positiveSign basisOne

minusOne : Q8
minusOne = quaternion negativeSign basisOne

plusI plusJ plusK minusI minusJ minusK : Q8
plusI = quaternion positiveSign basisI
plusJ = quaternion positiveSign basisJ
plusK = quaternion positiveSign basisK
minusI = quaternion negativeSign basisI
minusJ = quaternion negativeSign basisJ
minusK = quaternion negativeSign basisK

------------------------------------------------------------------------
-- Sign-forgetting rotation quotient.


data V4Rotation : Set where
  identityRotation halfTurnX halfTurnY halfTurnZ : V4Rotation

basisRotation : QuaternionBasis → V4Rotation
basisRotation basisOne = identityRotation
basisRotation basisI = halfTurnX
basisRotation basisJ = halfTurnY
basisRotation basisK = halfTurnZ

rho : Q8 → V4Rotation
rho (quaternion _ basisValue) = basisRotation basisValue

rotationMultiply : V4Rotation → V4Rotation → V4Rotation
rotationMultiply identityRotation right = right
rotationMultiply halfTurnX identityRotation = halfTurnX
rotationMultiply halfTurnX halfTurnX = identityRotation
rotationMultiply halfTurnX halfTurnY = halfTurnZ
rotationMultiply halfTurnX halfTurnZ = halfTurnY
rotationMultiply halfTurnY identityRotation = halfTurnY
rotationMultiply halfTurnY halfTurnX = halfTurnZ
rotationMultiply halfTurnY halfTurnY = identityRotation
rotationMultiply halfTurnY halfTurnZ = halfTurnX
rotationMultiply halfTurnZ identityRotation = halfTurnZ
rotationMultiply halfTurnZ halfTurnX = halfTurnY
rotationMultiply halfTurnZ halfTurnY = halfTurnX
rotationMultiply halfTurnZ halfTurnZ = identityRotation

rhoHomomorphism :
  (left right : Q8) →
  rho (q8Multiply left right)
  ≡ rotationMultiply (rho left) (rho right)
rhoHomomorphism (quaternion leftSign basisOne)
                (quaternion rightSign rightBasis) = refl
rhoHomomorphism (quaternion leftSign basisI)
                (quaternion rightSign basisOne) = refl
rhoHomomorphism (quaternion leftSign basisI)
                (quaternion rightSign basisI) = refl
rhoHomomorphism (quaternion leftSign basisI)
                (quaternion rightSign basisJ) = refl
rhoHomomorphism (quaternion leftSign basisI)
                (quaternion rightSign basisK) = refl
rhoHomomorphism (quaternion leftSign basisJ)
                (quaternion rightSign basisOne) = refl
rhoHomomorphism (quaternion leftSign basisJ)
                (quaternion rightSign basisI) = refl
rhoHomomorphism (quaternion leftSign basisJ)
                (quaternion rightSign basisJ) = refl
rhoHomomorphism (quaternion leftSign basisJ)
                (quaternion rightSign basisK) = refl
rhoHomomorphism (quaternion leftSign basisK)
                (quaternion rightSign basisOne) = refl
rhoHomomorphism (quaternion leftSign basisK)
                (quaternion rightSign basisI) = refl
rhoHomomorphism (quaternion leftSign basisK)
                (quaternion rightSign basisJ) = refl
rhoHomomorphism (quaternion leftSign basisK)
                (quaternion rightSign basisK) = refl

record RotationPreimage (rotation : V4Rotation) : Set where
  constructor rotation-preimage
  field
    element : Q8
    mapsToRotation : rho element ≡ rotation
open RotationPreimage public

rhoSurjective : (rotation : V4Rotation) → RotationPreimage rotation
rhoSurjective identityRotation = rotation-preimage plusOne refl
rhoSurjective halfTurnX = rotation-preimage plusI refl
rhoSurjective halfTurnY = rotation-preimage plusJ refl
rhoSurjective halfTurnZ = rotation-preimage plusK refl

------------------------------------------------------------------------
-- Exact kernel characterization.

kernelCharacterization :
  (element : Q8) →
  (rho element ≡ identityRotation)
  ↔ ((element ≡ plusOne) ⊎ (element ≡ minusOne))
kernelCharacterization (quaternion positiveSign basisOne) =
  iff (λ _ → inj₁ refl) (λ _ → refl)
kernelCharacterization (quaternion negativeSign basisOne) =
  iff (λ _ → inj₂ refl) (λ _ → refl)
kernelCharacterization (quaternion positiveSign basisI) =
  iff (λ ()) (λ { (inj₁ ()) ; (inj₂ ()) })
kernelCharacterization (quaternion negativeSign basisI) =
  iff (λ ()) (λ { (inj₁ ()) ; (inj₂ ()) })
kernelCharacterization (quaternion positiveSign basisJ) =
  iff (λ ()) (λ { (inj₁ ()) ; (inj₂ ()) })
kernelCharacterization (quaternion negativeSign basisJ) =
  iff (λ ()) (λ { (inj₁ ()) ; (inj₂ ()) })
kernelCharacterization (quaternion positiveSign basisK) =
  iff (λ ()) (λ { (inj₁ ()) ; (inj₂ ()) })
kernelCharacterization (quaternion negativeSign basisK) =
  iff (λ ()) (λ { (inj₁ ()) ; (inj₂ ()) })

------------------------------------------------------------------------
-- Two-element fibers.

plusMinusDistinct : plusOne ≢ minusOne
plusMinusDistinct ()

plusMinusIDistinct : plusI ≢ minusI
plusMinusIDistinct ()

plusMinusJDistinct : plusJ ≢ minusJ
plusMinusJDistinct ()

plusMinusKDistinct : plusK ≢ minusK
plusMinusKDistinct ()

identityFiberExhaustive :
  (candidate : Q8) →
  rho candidate ≡ identityRotation →
  (candidate ≡ plusOne) ⊎ (candidate ≡ minusOne)
identityFiberExhaustive (quaternion positiveSign basisOne) refl = inj₁ refl
identityFiberExhaustive (quaternion negativeSign basisOne) refl = inj₂ refl
identityFiberExhaustive (quaternion positiveSign basisI) ()
identityFiberExhaustive (quaternion negativeSign basisI) ()
identityFiberExhaustive (quaternion positiveSign basisJ) ()
identityFiberExhaustive (quaternion negativeSign basisJ) ()
identityFiberExhaustive (quaternion positiveSign basisK) ()
identityFiberExhaustive (quaternion negativeSign basisK) ()

xFiberExhaustive :
  (candidate : Q8) →
  rho candidate ≡ halfTurnX →
  (candidate ≡ plusI) ⊎ (candidate ≡ minusI)
xFiberExhaustive (quaternion positiveSign basisOne) ()
xFiberExhaustive (quaternion negativeSign basisOne) ()
xFiberExhaustive (quaternion positiveSign basisI) refl = inj₁ refl
xFiberExhaustive (quaternion negativeSign basisI) refl = inj₂ refl
xFiberExhaustive (quaternion positiveSign basisJ) ()
xFiberExhaustive (quaternion negativeSign basisJ) ()
xFiberExhaustive (quaternion positiveSign basisK) ()
xFiberExhaustive (quaternion negativeSign basisK) ()

yFiberExhaustive :
  (candidate : Q8) →
  rho candidate ≡ halfTurnY →
  (candidate ≡ plusJ) ⊎ (candidate ≡ minusJ)
yFiberExhaustive (quaternion positiveSign basisOne) ()
yFiberExhaustive (quaternion negativeSign basisOne) ()
yFiberExhaustive (quaternion positiveSign basisI) ()
yFiberExhaustive (quaternion negativeSign basisI) ()
yFiberExhaustive (quaternion positiveSign basisJ) refl = inj₁ refl
yFiberExhaustive (quaternion negativeSign basisJ) refl = inj₂ refl
yFiberExhaustive (quaternion positiveSign basisK) ()
yFiberExhaustive (quaternion negativeSign basisK) ()

zFiberExhaustive :
  (candidate : Q8) →
  rho candidate ≡ halfTurnZ →
  (candidate ≡ plusK) ⊎ (candidate ≡ minusK)
zFiberExhaustive (quaternion positiveSign basisOne) ()
zFiberExhaustive (quaternion negativeSign basisOne) ()
zFiberExhaustive (quaternion positiveSign basisI) ()
zFiberExhaustive (quaternion negativeSign basisI) ()
zFiberExhaustive (quaternion positiveSign basisJ) ()
zFiberExhaustive (quaternion negativeSign basisJ) ()
zFiberExhaustive (quaternion positiveSign basisK) refl = inj₁ refl
zFiberExhaustive (quaternion negativeSign basisK) refl = inj₂ refl

rhoFiberIsTwoElement :
  (rotation : V4Rotation) → TwoElementFiber rho rotation
rhoFiberIsTwoElement identityRotation =
  record
    { first = plusOne
    ; second = minusOne
    ; firstMaps = refl
    ; secondMaps = refl
    ; distinct = plusMinusDistinct
    ; exhaustive = identityFiberExhaustive
    }
rhoFiberIsTwoElement halfTurnX =
  record
    { first = plusI
    ; second = minusI
    ; firstMaps = refl
    ; secondMaps = refl
    ; distinct = plusMinusIDistinct
    ; exhaustive = xFiberExhaustive
    }
rhoFiberIsTwoElement halfTurnY =
  record
    { first = plusJ
    ; second = minusJ
    ; firstMaps = refl
    ; secondMaps = refl
    ; distinct = plusMinusJDistinct
    ; exhaustive = yFiberExhaustive
    }
rhoFiberIsTwoElement halfTurnZ =
  record
    { first = plusK
    ; second = minusK
    ; firstMaps = refl
    ; secondMaps = refl
    ; distinct = plusMinusKDistinct
    ; exhaustive = zFiberExhaustive
    }

finiteQuaternionSpinCover : SpinDoubleCoverProof
finiteQuaternionSpinCover =
  record
    { Spin = Q8
    ; SO = V4Rotation
    ; rho = rho
    ; spinIdentity = plusOne
    ; soIdentity = identityRotation
    ; plusOne = plusOne
    ; minusOne = minusOne
    ; SpinProduct = q8Multiply
    ; SOProduct = rotationMultiply
    ; rhoHomomorphism = rhoHomomorphism
    ; SurjectiveWitness = RotationPreimage
    ; rhoSurjective = rhoSurjective
    ; kernelCharacterization = kernelCharacterization
    ; fiberIsTwoElement = rhoFiberIsTwoElement
    }

finiteQuaternionBoundaryText : String
finiteQuaternionBoundaryText =
  "Q8 -> V4 is an exact nontrivial two-to-one spatial rotation subgroup cover.  Extending this producer to continuous Spin(3) -> SO(3), and then to Spin(3,1) -> SO+(3,1), requires the Clifford quotient and Lie/topological authority."
