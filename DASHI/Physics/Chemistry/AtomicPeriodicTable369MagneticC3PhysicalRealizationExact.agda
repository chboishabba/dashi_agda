module DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact where

------------------------------------------------------------------------
-- Atomic magnetic-sector x C3 realization.
--
-- The repository already owns, separately:
--   * physical orbital labels with principal/angular/magnetic/spin coordinates;
--   * the depth-one ternary kernel;
--   * exact symbolic C3 characters/phases;
--   * the abstract ternary -> physical realization intertwiner.
--
-- This owner pays the missing finite same-object weld for the l = 1 magnetic
-- triplet.  It keeps two actions distinct:
--
--   (1) a 120-degree z-axis rotation is diagonal in the m basis and contributes
--       the character phase omega^m;
--   (2) a charge +1 sector transport cycles residues m mod 3.
--
-- Thus the cyclic ternary step is identified with C3-charge transport, NOT
-- with the spatial rotation itself.  No analytic spherical harmonic, radial
-- wavefunction, Hamiltonian spectrum, or transition amplitude is fabricated.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using ([]; _∷_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.TriadicFiniteQuotient as Quotient
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Physics.Foundations.AtomicFermionShellExact as Atomic
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as G
import DASHI.Physics.Chemistry.AtomicPeriodicTable369TernaryRealizationIntertwinerExact as R

------------------------------------------------------------------------
-- 1. Finite l = 1 magnetic basis and its residue-sector observer.
------------------------------------------------------------------------

data MagneticState : Set where
  mNegOne : MagneticState
  mZero : MagneticState
  mPosOne : MagneticState

data MagneticSector : Set where
  sectorNegative : MagneticSector
  sectorZero : MagneticSector
  sectorPositive : MagneticSector

magneticSector : MagneticState -> MagneticSector
magneticSector mNegOne = sectorNegative
magneticSector mZero = sectorZero
magneticSector mPosOne = sectorPositive

sectorResidue : MagneticSector -> Quotient.Residue3Pow Quotient.one
sectorResidue sectorNegative = Characters.rNeg
sectorResidue sectorZero = Characters.rZero
sectorResidue sectorPositive = Characters.rPos

------------------------------------------------------------------------
-- 2. Restriction of the magnetic basis to the C3 rotation subgroup.
--
-- In the conventional complex magnetic basis a z rotation by 2pi/3 acts by
-- the eigenvalue omega^m.  We reuse the repo's symbolic C3 phase ring rather
-- than manufacturing complex exponentials.
------------------------------------------------------------------------

C3Phase : Set
C3Phase = Characters.C3Phase

phaseNeutral phasePositive phaseNegative : C3Phase
phaseNeutral = Characters.phase0
phasePositive = Characters.phase1
phaseNegative = Characters.phase2

rotationPhase : MagneticState -> C3Phase
rotationPhase mNegOne = phaseNegative
rotationPhase mZero = phaseNeutral
rotationPhase mPosOne = phasePositive

rotationPhaseViaExistingCharacter : MagneticState -> C3Phase
rotationPhaseViaExistingCharacter m =
  Characters.characterValue Characters.rPos (sectorResidue (magneticSector m))

rotationPhaseIsExistingPositiveCharacter :
  (m : MagneticState) ->
  rotationPhaseViaExistingCharacter m ≡ rotationPhase m
rotationPhaseIsExistingPositiveCharacter mNegOne = refl
rotationPhaseIsExistingPositiveCharacter mZero = refl
rotationPhaseIsExistingPositiveCharacter mPosOne = refl

negativeAndPositiveRotationPhasesConjugate :
  Characters.conjugatePhase (rotationPhase mPosOne)
  ≡ rotationPhase mNegOne
negativeAndPositiveRotationPhasesConjugate = refl

zeroRotationPhaseFixed :
  Characters.conjugatePhase (rotationPhase mZero)
  ≡ rotationPhase mZero
zeroRotationPhaseFixed = refl

------------------------------------------------------------------------
-- 3. C3 charge transport.  This is the cyclic sector action that can inhabit
-- the existing ternary-step intertwiner.
------------------------------------------------------------------------

data C3Charge : Set where
  chargeNegative : C3Charge
  chargeZero : C3Charge
  chargePositive : C3Charge

chargeResidue : C3Charge -> Quotient.Residue3Pow Quotient.one
chargeResidue chargeNegative = Characters.rNeg
chargeResidue chargeZero = Characters.rZero
chargeResidue chargePositive = Characters.rPos

addSector : MagneticSector -> C3Charge -> MagneticSector
addSector sectorZero chargeZero = sectorZero
addSector sectorZero chargePositive = sectorPositive
addSector sectorZero chargeNegative = sectorNegative
addSector sectorPositive chargeZero = sectorPositive
addSector sectorPositive chargePositive = sectorNegative
addSector sectorPositive chargeNegative = sectorZero
addSector sectorNegative chargeZero = sectorNegative
addSector sectorNegative chargePositive = sectorZero
addSector sectorNegative chargeNegative = sectorPositive

sectorAdditionIsExistingC3Addition :
  (sector : MagneticSector) (charge : C3Charge) ->
  sectorResidue (addSector sector charge)
  ≡ Arithmetic.addResidue (sectorResidue sector) (chargeResidue charge)
sectorAdditionIsExistingC3Addition sectorNegative chargeNegative = refl
sectorAdditionIsExistingC3Addition sectorNegative chargeZero = refl
sectorAdditionIsExistingC3Addition sectorNegative chargePositive = refl
sectorAdditionIsExistingC3Addition sectorZero chargeNegative = refl
sectorAdditionIsExistingC3Addition sectorZero chargeZero = refl
sectorAdditionIsExistingC3Addition sectorZero chargePositive = refl
sectorAdditionIsExistingC3Addition sectorPositive chargeNegative = refl
sectorAdditionIsExistingC3Addition sectorPositive chargeZero = refl
sectorAdditionIsExistingC3Addition sectorPositive chargePositive = refl

chargePositiveStep : MagneticState -> MagneticState
chargePositiveStep mNegOne = mZero
chargePositiveStep mZero = mPosOne
chargePositiveStep mPosOne = mNegOne

chargePositiveStepOrderThree :
  (m : MagneticState) ->
  chargePositiveStep (chargePositiveStep (chargePositiveStep m)) ≡ m
chargePositiveStepOrderThree mNegOne = refl
chargePositiveStepOrderThree mZero = refl
chargePositiveStepOrderThree mPosOne = refl

chargePositiveStepRaisesSector :
  (m : MagneticState) ->
  magneticSector (chargePositiveStep m)
  ≡ addSector (magneticSector m) chargePositive
chargePositiveStepRaisesSector mNegOne = refl
chargePositiveStepRaisesSector mZero = refl
chargePositiveStepRaisesSector mPosOne = refl

------------------------------------------------------------------------
-- 4. Exact mod-3 selection rule as a typed equality, plus executable decision.
------------------------------------------------------------------------

TransitionAllowed : MagneticSector -> C3Charge -> MagneticSector -> Set
TransitionAllowed source charge target = target ≡ addSector source charge

sectorEq : MagneticSector -> MagneticSector -> Bool
sectorEq sectorNegative sectorNegative = true
sectorEq sectorNegative sectorZero = false
sectorEq sectorNegative sectorPositive = false
sectorEq sectorZero sectorNegative = false
sectorEq sectorZero sectorZero = true
sectorEq sectorZero sectorPositive = false
sectorEq sectorPositive sectorNegative = false
sectorEq sectorPositive sectorZero = false
sectorEq sectorPositive sectorPositive = true

transitionAllowed : MagneticSector -> C3Charge -> MagneticSector -> Bool
transitionAllowed source charge target = sectorEq target (addSector source charge)

negativeToZeroByPositiveCharge :
  TransitionAllowed sectorNegative chargePositive sectorZero
negativeToZeroByPositiveCharge = refl

negativeToZeroByZeroChargeRejected :
  transitionAllowed sectorNegative chargeZero sectorZero ≡ false
negativeToZeroByZeroChargeRejected = refl

------------------------------------------------------------------------
-- 5. Depth-one ternary axis -> physical p-shell magnetic triplet.
------------------------------------------------------------------------

DepthOneKernel : Set
DepthOneKernel = G.TernaryKernel 1

kernelNegative kernelZero kernelPositive : DepthOneKernel
kernelNegative = Triadic.negativeTrit ∷ []
kernelZero = Triadic.zeroTrit ∷ []
kernelPositive = Triadic.positiveTrit ∷ []

kernelResidue : DepthOneKernel -> Quotient.Residue3Pow Quotient.one
kernelResidue (Triadic.negativeTrit ∷ []) = Characters.rNeg
kernelResidue (Triadic.zeroTrit ∷ []) = Characters.rZero
kernelResidue (Triadic.positiveTrit ∷ []) = Characters.rPos

ternaryChargePositiveStep : DepthOneKernel -> DepthOneKernel
ternaryChargePositiveStep (Triadic.negativeTrit ∷ []) = kernelZero
ternaryChargePositiveStep (Triadic.zeroTrit ∷ []) = kernelPositive
ternaryChargePositiveStep (Triadic.positiveTrit ∷ []) = kernelNegative

realizeMagneticState : DepthOneKernel -> MagneticState
realizeMagneticState (Triadic.negativeTrit ∷ []) = mNegOne
realizeMagneticState (Triadic.zeroTrit ∷ []) = mZero
realizeMagneticState (Triadic.positiveTrit ∷ []) = mPosOne

realizationPreservesC3Residue :
  (x : DepthOneKernel) ->
  sectorResidue (magneticSector (realizeMagneticState x)) ≡ kernelResidue x
realizationPreservesC3Residue (Triadic.negativeTrit ∷ []) = refl
realizationPreservesC3Residue (Triadic.zeroTrit ∷ []) = refl
realizationPreservesC3Residue (Triadic.positiveTrit ∷ []) = refl

realizationIntertwinesChargeStep :
  (x : DepthOneKernel) ->
  realizeMagneticState (ternaryChargePositiveStep x)
  ≡ chargePositiveStep (realizeMagneticState x)
realizationIntertwinesChargeStep (Triadic.negativeTrit ∷ []) = refl
realizationIntertwinesChargeStep (Triadic.zeroTrit ∷ []) = refl
realizationIntertwinesChargeStep (Triadic.positiveTrit ∷ []) = refl

------------------------------------------------------------------------
-- 6. Adapter into the existing orbital-label carrier.
--
-- `magneticIndexCode` is intentionally treated as an encoding coordinate,
-- not silently identified with the signed quantum number m.  The local code
-- below is an explicit bijective convention for this three-state subsystem.
------------------------------------------------------------------------

magneticIndexCodeLocal : MagneticState -> Nat
magneticIndexCodeLocal mNegOne = 0
magneticIndexCodeLocal mZero = 1
magneticIndexCodeLocal mPosOne = 2

pShellOrbitalReadout : MagneticState -> G.OrbitalLabel
pShellOrbitalReadout m =
  Atomic.orbitalLabel 2 1 (magneticIndexCodeLocal m) Atomic.spinUp

pShellAngularIndexIsOne :
  (m : MagneticState) ->
  Atomic.angularIndex (pShellOrbitalReadout m) ≡ 1
pShellAngularIndexIsOne m = refl

------------------------------------------------------------------------
-- 7. Concrete inhabitant of the existing realization-intertwiner contract.
------------------------------------------------------------------------

pShellC3Realization : R.TernaryAtomicRealizationIntertwiner 1
pShellC3Realization =
  record
    { PhysicalState = MagneticState
    ; ternaryStep = ternaryChargePositiveStep
    ; physicalStep = chargePositiveStep
    ; realize = realizeMagneticState
    ; orbitalReadout = pShellOrbitalReadout
    ; intertwines = realizationIntertwinesChargeStep
    }

------------------------------------------------------------------------
-- 8. Boundary: what this pays and what it does not.
------------------------------------------------------------------------

record MagneticC3PhysicalBoundary : Set where
  constructor magneticC3PhysicalBoundary
  field
    pShellMagneticTripletRepresented : Bool
    c3RotationCharacterAssigned : Bool
    c3RotationCharacterReusesExistingFourierTable : Bool
    positiveChargeTransportIntertwinerPaid : Bool
    modThreeSelectionRulePaid : Bool
    ternaryPhysicalResidueSameObjectWeldPaid : Bool
    magneticIndexCodeIdentifiedWithSignedM : Bool
    analyticSphericalHarmonicActionPaid : Bool
    dipoleMatrixElementAmplitudePaid : Bool
    interactingHamiltonianIntertwinerPaid : Bool

canonicalMagneticC3PhysicalBoundary : MagneticC3PhysicalBoundary
canonicalMagneticC3PhysicalBoundary =
  magneticC3PhysicalBoundary
    true true true true true true
    false false false false

magneticIndexCodeIdentifiedWithSignedMIsFalse :
  MagneticC3PhysicalBoundary.magneticIndexCodeIdentifiedWithSignedM
    canonicalMagneticC3PhysicalBoundary
  ≡ false
magneticIndexCodeIdentifiedWithSignedMIsFalse = refl

interactingHamiltonianIntertwinerPaidIsFalse :
  MagneticC3PhysicalBoundary.interactingHamiltonianIntertwinerPaid
    canonicalMagneticC3PhysicalBoundary
  ≡ false
interactingHamiltonianIntertwinerPaidIsFalse = refl
