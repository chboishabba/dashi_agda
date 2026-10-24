module DASHI.Mathematics.Topology.AlexanderHornedC3SpinLiftSplitExact where

------------------------------------------------------------------------
-- STEELMAN: A GENUINE DISCRETE SPIN LIFT OF OUR HORN C3 EXISTS.
--
-- Classical roots: Hamilton, Cartan/Spin3, Schur-Zassenhaus;
-- periodic cyclic cohomology H^2(C3,C2)=0.
--
-- EXISTING DASHI OWNERS (DO NOT REBUILD):
-- * Core.FiniteC3OrbitStabilizerExact: actual C3 group law.
-- * Algebra.FiniteQuaternionDoubleCover: actual Q8 central signs.
-- * Mathematics.Topology.AlexanderHornedC3AmbientRotationExact:
--   the literal xyz->zxy coordinate rotation.
-- * Mathematics.Topology.AlexanderHornedQuaternionC3SpinExact:
--   quaternion q=(1+i+j+k)/2 with q^3=-1, (-q)^3=1,
--   both conjugating pure quaternions by the SAME xyz cycle.
--
-- NEW EXACT FINITE THEOREM:
-- The pullback of Spin(3)->SO(3) to this C3 subgroup is C6,
-- isomorphic to C3 x C2. The path-selected lift q has order six,
-- but rephasing the generator by central -1 yields a genuine
-- homomorphic C3 section. We construct both on the SAME
-- existing phase/sign carriers and prove the projective
-- factor system is a *coboundary* (all nine multiplication cases).
--
-- No continuous path/Spin-bundle theorem is claimed here.
-- In particular the identity-starting rotation path q is NOT
-- itself a C3 group-action generator (its cube is -1).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Ambient

record SpinC3 : Set where
  constructor spinC3
  field
    spatial : C3.C3
    parity : Q8.Sign

open SpinC3 public

unit : SpinC3
unit = spinC3 C3.c0 Q8.positiveSign

centralMinus : SpinC3
centralMinus = spinC3 C3.c0 Q8.negativeSign

_*_ : SpinC3 → SpinC3 → SpinC3
spinC3 a s * spinC3 b t =
  spinC3 (C3._∙_ a b) (Q8.signMultiply s t)

signAssociative : ∀ a b c →
  Q8.signMultiply (Q8.signMultiply a b) c
  ≡ Q8.signMultiply a (Q8.signMultiply b c)
signAssociative Q8.positiveSign b c = refl
signAssociative Q8.negativeSign Q8.positiveSign c = refl
signAssociative Q8.negativeSign Q8.negativeSign Q8.positiveSign = refl
signAssociative Q8.negativeSign Q8.negativeSign Q8.negativeSign = refl

spinC3Associative : ∀ a b c → (a * b) * c ≡ a * (b * c)
spinC3Associative (spinC3 a s) (spinC3 b t) (spinC3 c u) =
  cong₂ spinC3 (C3.associative a b c) (signAssociative s t u)

spinC3UnitLeft : ∀ a → unit * a ≡ a
spinC3UnitLeft (spinC3 a s) = refl

spinC3UnitRight : ∀ a → a * unit ≡ a
spinC3UnitRight (spinC3 C3.c0 Q8.positiveSign) = refl
spinC3UnitRight (spinC3 C3.c0 Q8.negativeSign) = refl
spinC3UnitRight (spinC3 C3.c1 Q8.positiveSign) = refl
spinC3UnitRight (spinC3 C3.c1 Q8.negativeSign) = refl
spinC3UnitRight (spinC3 C3.c2 Q8.positiveSign) = refl
spinC3UnitRight (spinC3 C3.c2 Q8.negativeSign) = refl

forgetSign : SpinC3 → C3.C3
forgetSign = spatial

forgetSignPreservesProduct : ∀ a b →
  forgetSign (a * b) ≡ C3._∙_ (forgetSign a) (forgetSign b)
forgetSignPreservesProduct a b = refl

coherentSection : C3.C3 → SpinC3
coherentSection c = spinC3 c Q8.positiveSign

coherentSectionProjectsToIdentity : ∀ c →
  forgetSign (coherentSection c) ≡ c
coherentSectionProjectsToIdentity c = refl

coherentSectionIsHomomorphism : ∀ a b →
  coherentSection (C3._∙_ a b) ≡
    coherentSection a * coherentSection b
coherentSectionIsHomomorphism a b = refl

-- Selected 0->120-degree angular-path endpoint. This sign convention
-- matches the actual quaternion q in the previous source owner.
pathLiftGenerator : SpinC3
pathLiftGenerator = spinC3 C3.c1 Q8.negativeSign

discreteLiftGenerator : SpinC3
discreteLiftGenerator = spinC3 C3.c1 Q8.positiveSign

pathAndDiscreteHaveSameSpatialImage :
  forgetSign pathLiftGenerator ≡ forgetSign discreteLiftGenerator
pathAndDiscreteHaveSameSpatialImage = refl

pathLiftGeneratorCubed :
  ((pathLiftGenerator * pathLiftGenerator) * pathLiftGenerator)
  ≡ centralMinus
pathLiftGeneratorCubed = refl

discreteLiftGeneratorCubed :
  ((discreteLiftGenerator * discreteLiftGenerator)
    * discreteLiftGenerator) ≡ unit
discreteLiftGeneratorCubed = refl

centralMinusSquaresToUnit : centralMinus * centralMinus ≡ unit
centralMinusSquaresToUnit = refl

pathLiftGeneratorSixth :
  (((pathLiftGenerator * pathLiftGenerator) * pathLiftGenerator)
   * ((pathLiftGenerator * pathLiftGenerator) * pathLiftGenerator))
    ≡ unit
pathLiftGeneratorSixth = refl

centralMinusIsNotIdentity : centralMinus ≡ unit → ⊥
centralMinusIsNotIdentity ()

-- Three angular path endpoints, powers q^0, q^1, q^2, are a
-- non-homomorphic section of C3. Its factor set is the
-- central sign acquired on carrying past 360 degrees.
pathSection : C3.C3 → SpinC3
pathSection C3.c0 = unit
pathSection C3.c1 = pathLiftGenerator
pathSection C3.c2 = pathLiftGenerator * pathLiftGenerator

carry : C3.C3 → C3.C3 → Q8.Sign
carry C3.c0 _ = Q8.positiveSign
carry C3.c1 C3.c0 = Q8.positiveSign
carry C3.c1 C3.c1 = Q8.positiveSign
carry C3.c1 C3.c2 = Q8.negativeSign
carry C3.c2 C3.c0 = Q8.positiveSign
carry C3.c2 C3.c1 = Q8.negativeSign
carry C3.c2 C3.c2 = Q8.negativeSign

pathMultiplicationHasCentralCarry :
  ∀ a b →
  pathSection a * pathSection b ≡
  (spinC3 C3.c0 (carry a b)) * pathSection (C3._∙_ a b)
pathMultiplicationHasCentralCarry C3.c0 C3.c0 = refl
pathMultiplicationHasCentralCarry C3.c0 C3.c1 = refl
pathMultiplicationHasCentralCarry C3.c0 C3.c2 = refl
pathMultiplicationHasCentralCarry C3.c1 C3.c0 = refl
pathMultiplicationHasCentralCarry C3.c1 C3.c1 = refl
pathMultiplicationHasCentralCarry C3.c1 C3.c2 = refl
pathMultiplicationHasCentralCarry C3.c2 C3.c0 = refl
pathMultiplicationHasCentralCarry C3.c2 C3.c1 = refl
pathMultiplicationHasCentralCarry C3.c2 C3.c2 = refl

-- An explicit trivializing 1-cochain. This is stronger than
-- merely quoting H^2(C3,C2)=0: it proves OUR selected cocycle
-- is a coboundary by finite exact cases.
rephasing : C3.C3 → Q8.Sign
rephasing C3.c0 = Q8.positiveSign
rephasing C3.c1 = Q8.negativeSign
rephasing C3.c2 = Q8.positiveSign

centralCarryIsCoboundary :
  ∀ a b →
  Q8.signMultiply (rephasing a) (rephasing b) ≡
    Q8.signMultiply (carry a b)
      (rephasing (C3._∙_ a b))
centralCarryIsCoboundary C3.c0 C3.c0 = refl
centralCarryIsCoboundary C3.c0 C3.c1 = refl
centralCarryIsCoboundary C3.c0 C3.c2 = refl
centralCarryIsCoboundary C3.c1 C3.c0 = refl
centralCarryIsCoboundary C3.c1 C3.c1 = refl
centralCarryIsCoboundary C3.c1 C3.c2 = refl
centralCarryIsCoboundary C3.c2 C3.c0 = refl
centralCarryIsCoboundary C3.c2 C3.c1 = refl
centralCarryIsCoboundary C3.c2 C3.c2 = refl

rephasingRepairsPathSection :
  ∀ c →
  spinC3 C3.c0 (rephasing c) * pathSection c ≡ coherentSection c
rephasingRepairsPathSection C3.c0 = refl
rephasingRepairsPathSection C3.c1 = refl
rephasingRepairsPathSection C3.c2 = refl

-- Explicit spinor sign carrier, not an ordinary spatial vector.
record SpinSlot : Set where
  constructor spinSlot
  field
    sector : C3.C3
    spinSign : Q8.Sign
open SpinSlot public

spinAct : SpinC3 → SpinSlot → SpinSlot
spinAct (spinC3 c s) (spinSlot x t) =
  spinSlot (C3._∙_ c x) (Q8.signMultiply s t)

spinActComposition : ∀ g h x →
  spinAct (g * h) x ≡ spinAct g (spinAct h x)
spinActComposition (spinC3 c s) (spinC3 d t) (spinSlot x u) =
  cong₂ spinSlot (C3.associative c d x) (signAssociative s t u)

pathTripleActFlipsSpinSign :
  spinAct pathLiftGenerator
    (spinAct pathLiftGenerator
      (spinAct pathLiftGenerator
        (spinSlot C3.c0 Q8.positiveSign)))
  ≡ spinSlot C3.c0 Q8.negativeSign
pathTripleActFlipsSpinSign = refl

coherentTripleActPreservesSpinSign :
  spinAct discreteLiftGenerator
    (spinAct discreteLiftGenerator
      (spinAct discreteLiftGenerator
        (spinSlot C3.c0 Q8.positiveSign)))
  ≡ spinSlot C3.c0 Q8.positiveSign
coherentTripleActPreservesSpinSign = refl

-- The angular rotation seen by BOTH lifts is the previous literal
-- ambient C3 action, not a new invented geometric transformation.
bothProjectToExistingHornAxisRotation : ∀ c →
  Ambient.rotateXYZ (Ambient.basis c)
    ≡ Ambient.basis (C3._∙_ (forgetSign pathLiftGenerator) c)
bothProjectToExistingHornAxisRotation =
  Ambient.axisRotationIsC3Action

-- The continuous angular *path* and the spin structure on the wild
-- complement are not constructed here. The ambient SO3 path at
-- intermediate angles need not preserve the selected horn embedding.

------------------------------------------------------------------------
-- Uniqueness at odd order: among the TWO lifts of the selected
-- spatial generator, precisely ONE obeys the actual C3 relation.
------------------------------------------------------------------------

uniqueOrderThreeGeneratorLift :
  ∀ a →
  forgetSign a ≡ C3.c1 →
  ((a * a) * a) ≡ unit →
  a ≡ discreteLiftGenerator
uniqueOrderThreeGeneratorLift
  (spinC3 C3.c0 Q8.positiveSign) () cubeIdentity
uniqueOrderThreeGeneratorLift
  (spinC3 C3.c0 Q8.negativeSign) () cubeIdentity
uniqueOrderThreeGeneratorLift
  (spinC3 C3.c1 Q8.positiveSign) projection cubeIdentity = refl
uniqueOrderThreeGeneratorLift
  (spinC3 C3.c1 Q8.negativeSign) projection ()
uniqueOrderThreeGeneratorLift
  (spinC3 C3.c2 Q8.positiveSign) () cubeIdentity
uniqueOrderThreeGeneratorLift
  (spinC3 C3.c2 Q8.negativeSign) () cubeIdentity
