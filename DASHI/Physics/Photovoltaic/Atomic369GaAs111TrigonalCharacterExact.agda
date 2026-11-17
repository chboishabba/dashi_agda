module DASHI.Physics.Photovoltaic.Atomic369GaAs111TrigonalCharacterExact where

-- Spinless finite C3v character bridge on the source p-triplet.
-- Not a Hilbert-space complex 3x3 Fourier matrix and not a physical 8-band map.
-- Charge/residue step and spatial C3 are different operators.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as P

data Cartesian : Set where
  X Y Z : Cartesian

rotate111 : Cartesian -> Cartesian
rotate111 X = Y
rotate111 Y = Z
rotate111 Z = X

mirror111 : Cartesian -> Cartesian
mirror111 X = X
mirror111 Y = Z
mirror111 Z = Y

rotationOrderThree : (x : Cartesian) ->
  rotate111 (rotate111 (rotate111 x)) ≡ x
rotationOrderThree X = refl
rotationOrderThree Y = refl
rotationOrderThree Z = refl

mirrorOrderTwo : (x : Cartesian) -> mirror111 (mirror111 x) ≡ x
mirrorOrderTwo X = refl
mirrorOrderTwo Y = refl
mirrorOrderTwo Z = refl

mirrorConjugatesRotation : (x : Cartesian) ->
  mirror111 (rotate111 (mirror111 x)) ≡ rotate111 (rotate111 x)
mirrorConjugatesRotation X = refl
mirrorConjugatesRotation Y = refl
mirrorConjugatesRotation Z = refl

-- Eigenvector labels; analytic SALCs require coefficients in Q(omega,sqrt3).
data Trigonal : Set where
  a1 ePlus eMinus : Trigonal

spatialPhase : Trigonal -> Characters.C3Phase
spatialPhase a1 = Characters.phase0
spatialPhase ePlus = Characters.phase1
spatialPhase eMinus = Characters.phase2

mirrorTrigonal : Trigonal -> Trigonal
mirrorTrigonal a1 = a1
mirrorTrigonal ePlus = eMinus
mirrorTrigonal eMinus = ePlus

mirrorTrigonalInvolution : (x : Trigonal) ->
  mirrorTrigonal (mirrorTrigonal x) ≡ x
mirrorTrigonalInvolution a1 = refl
mirrorTrigonalInvolution ePlus = refl
mirrorTrigonalInvolution eMinus = refl

mirrorConjugatesCharacter : (x : Trigonal) ->
  spatialPhase (mirrorTrigonal x) ≡
  Characters.conjugatePhase (spatialPhase x)
mirrorConjugatesCharacter a1 = refl
mirrorConjugatesCharacter ePlus = refl
mirrorConjugatesCharacter eMinus = refl

-- A [111] trigonal quantization-axis choice, not the device material weld.
sourcePToTrigonal : P.MagneticState -> Trigonal
sourcePToTrigonal P.mNegOne = eMinus
sourcePToTrigonal P.mZero = a1
sourcePToTrigonal P.mPosOne = ePlus

sourceAndTrigonalSpatialCharactersAgree : (m : P.MagneticState) ->
  spatialPhase (sourcePToTrigonal m) ≡ P.rotationPhase m
sourceAndTrigonalSpatialCharactersAgree P.mNegOne = refl
sourceAndTrigonalSpatialCharactersAgree P.mZero = refl
sourceAndTrigonalSpatialCharactersAgree P.mPosOne = refl

-- The independent charge sector permutation is NOT the spatial rotation.
chargeSectorStep : Trigonal -> Trigonal
chargeSectorStep eMinus = a1
chargeSectorStep a1 = ePlus
chargeSectorStep ePlus = eMinus

sourceAndTrigonalChargeStepsAgree : (m : P.MagneticState) ->
  chargeSectorStep (sourcePToTrigonal m) ≡
  sourcePToTrigonal (P.chargePositiveStep m)
sourceAndTrigonalChargeStepsAgree P.mNegOne = refl
sourceAndTrigonalChargeStepsAgree P.mZero = refl
sourceAndTrigonalChargeStepsAgree P.mPosOne = refl

data False : Set where

neutralAndPositiveDiffer : a1 ≡ ePlus -> False
neutralAndPositiveDiffer ()

chargeStepDoesNotFixNeutral : chargeSectorStep a1 ≡ a1 -> False
chargeStepDoesNotFixNeutral ()

-- A C3v-invariant spinless Hamiltonian leaves E degenerate.
-- Spin-orbit double-group spectroscopy and a device-level weld remain open.
