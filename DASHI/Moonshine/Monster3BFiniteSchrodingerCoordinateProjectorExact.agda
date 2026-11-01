module DASHI.Moonshine.Monster3BFiniteSchrodingerCoordinateProjectorExact where

------------------------------------------------------------------------
-- ONE-COORDINATE FOURIER PROJECTORS FROM THE ACTUAL MODULATION ACTION
--
-- For target t in F3 and modulation eigenvalue zeta^value, use the
-- unnormalised character projector
--
--   P_t = I + zeta^{-t} M + zeta^{-2t} M^2.
--
-- Pointwise this is 3 on coordinate t and 0 on the other two coordinates.
-- Thus an invariant Q(zeta_3)-subspace is closed under P_t without granting
-- arbitrary coordinate selection as an axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L

phase : Trit → C3.Cyclotomic3
phase = V.phase

phaseSquare : Trit → C3.Cyclotomic3
phaseSquare value = C3.multiply (phase value) (phase value)

negPhase : Trit → C3.Cyclotomic3
negPhase target = phase (H.negate3 target)

negDoublePhase : Trit → C3.Cyclotomic3
negDoublePhase target = phase (H.negate3 (H._+3_ target target))

projectAmplitude : Trit → Trit → C3.Cyclotomic3 → C3.Cyclotomic3
projectAmplitude target value amplitude =
  L.add amplitude
    (L.add
      (C3.multiply (negPhase target)
        (C3.multiply (phase value) amplitude))
      (C3.multiply (negDoublePhase target)
        (C3.multiply (phaseSquare value) amplitude)))

tripleAmplitude : C3.Cyclotomic3 → C3.Cyclotomic3
tripleAmplitude amplitude = L.add amplitude (L.add amplitude amplitude)

projectAmplitudeSame :
  (target : Trit) → (amplitude : C3.Cyclotomic3) →
  projectAmplitude target target amplitude ≡ tripleAmplitude amplitude
projectAmplitudeSame neg (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
projectAmplitudeSame zer (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
projectAmplitudeSame pos (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

projectAmplitudeDifferentNegZer : (a : C3.Cyclotomic3) →
  projectAmplitude neg zer a ≡ C3.zero
projectAmplitudeDifferentNegZer (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

projectAmplitudeDifferentNegPos : (a : C3.Cyclotomic3) →
  projectAmplitude neg pos a ≡ C3.zero
projectAmplitudeDifferentNegPos (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

projectAmplitudeDifferentZerNeg : (a : C3.Cyclotomic3) →
  projectAmplitude zer neg a ≡ C3.zero
projectAmplitudeDifferentZerNeg (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

projectAmplitudeDifferentZerPos : (a : C3.Cyclotomic3) →
  projectAmplitude zer pos a ≡ C3.zero
projectAmplitudeDifferentZerPos (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

projectAmplitudeDifferentPosNeg : (a : C3.Cyclotomic3) →
  projectAmplitude pos neg a ≡ C3.zero
projectAmplitudeDifferentPosNeg (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

projectAmplitudeDifferentPosZer : (a : C3.Cyclotomic3) →
  projectAmplitude pos zer a ≡ C3.zero
projectAmplitudeDifferentPosZer (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

------------------------------------------------------------------------
-- Actual function operator written only from I, M, M^2, addition and
-- cyclotomic scalar multiplication.
------------------------------------------------------------------------

modulationTwice : H.Axis6 → V.SchrodingerFunction → V.SchrodingerFunction
modulationTwice axis f = V.modulationAction axis (V.modulationAction axis f)

coordinateProjector :
  Trit → H.Axis6 → V.SchrodingerFunction → V.SchrodingerFunction
coordinateProjector target axis f =
  V.addFunction f
    (V.addFunction
      (V.cyclotomicScaleFunction (negPhase target)
        (V.modulationAction axis f))
      (V.cyclotomicScaleFunction (negDoublePhase target)
        (modulationTwice axis f)))

coordinateProjectorPointwise :
  (target : Trit) → (axis : H.Axis6) →
  (f : V.SchrodingerFunction) → (x : H.X6) →
  coordinateProjector target axis f x
  ≡ projectAmplitude target (H.coordinate axis x) (f x)
coordinateProjectorPointwise target axis f x = refl

------------------------------------------------------------------------
-- Invariance transport: P_t is not a primitive closure rule; it is built from
-- operations already required of a Heisenberg-invariant linear subspace.
------------------------------------------------------------------------

projectorPreservesInvariantSubspace :
  {Member : V.SchrodingerFunction → Set} →
  V.HeisenbergInvariantSubspace Member →
  (target : Trit) → (axis : H.Axis6) →
  (f : V.SchrodingerFunction) → Member f →
  Member (coordinateProjector target axis f)
projectorPreservesInvariantSubspace {Member} inv target axis f member =
  V.closedUnderAddition inv f
    (V.addFunction
      (V.cyclotomicScaleFunction (negPhase target) (V.modulationAction axis f))
      (V.cyclotomicScaleFunction (negDoublePhase target) (modulationTwice axis f)))
    member
    (V.closedUnderAddition inv
      (V.cyclotomicScaleFunction (negPhase target) (V.modulationAction axis f))
      (V.cyclotomicScaleFunction (negDoublePhase target) (modulationTwice axis f))
      (V.closedUnderCyclotomicScaling inv (negPhase target)
        (V.modulationAction axis f)
        (V.closedUnderModulation inv axis f member))
      (V.closedUnderCyclotomicScaling inv (negDoublePhase target)
        (modulationTwice axis f)
        (V.closedUnderModulation inv axis (V.modulationAction axis f)
          (V.closedUnderModulation inv axis f member))))

record CoordinateProjectorBoundary : Set where
  constructor coordinateProjectorBoundary
  field
    projectorDerivedFromModulationAction : Bool
    matchingCoordinateGetsTripleAmplitude : Bool
    mismatchingCoordinateCancels : Bool
    invariantSubspaceClosedUnderDerivedProjector : Bool
    sixCoordinatePointProjectorConstructedHere : Bool
    irreducibilityProvedHere : Bool
open CoordinateProjectorBoundary public

canonicalCoordinateProjectorBoundary : CoordinateProjectorBoundary
canonicalCoordinateProjectorBoundary =
  coordinateProjectorBoundary true true true true false false
