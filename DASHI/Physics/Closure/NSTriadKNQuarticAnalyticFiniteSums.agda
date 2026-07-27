module DASHI.Physics.Closure.NSTriadKNQuarticAnalyticFiniteSums where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: David Darrow; Elizabeth Carlson; David Goluskin.
-- Title: "Quartic Lyapunov functions for global fluid stability".
-- Venue/year: arXiv preprint, 2026.
-- Journal DOI: none recorded on arXiv v1.
-- arXiv/DataCite DOI: 10.48550/arXiv.2606.18232.
-- arXiv: 2606.18232v1.
-- Uses: equation (16), with E^2 + 2 E W + Q.
-- Relationship: adapts the finite quartic ansatz to literal periodic
-- Fourier-mode sums.  The choice of weights, chart and coherence direction
-- below is a candidate family, not a claim of 3-D global control.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

Velocity :
  ∀ {r} (F : C3.RealField r) → Set r
Velocity F = Z3.FourierMode → C3.Complex3 F

sumScalars :
  ∀ {r} (F : C3.RealField r) →
  List (C3.Carrier F) → C3.Carrier F
sumScalars F [] = C3.zero F
sumScalars F (x ∷ xs) = C3.add F x (sumScalars F xs)

complexSquaredMagnitude :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Carrier F
complexSquaredMagnitude {F = F} z =
  C3.add F
    (C3.multiply F (C3.real z) (C3.real z))
    (C3.multiply F (C3.imaginary z) (C3.imaginary z))

complex3SquaredMagnitude :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Carrier F
complex3SquaredMagnitude {F = F} v =
  C3.add F
    (C3.add F
      (complexSquaredMagnitude (C3.x v))
      (complexSquaredMagnitude (C3.y v)))
    (complexSquaredMagnitude (C3.z v))

realHermitianCoordinate :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Carrier F
realHermitianCoordinate direction value =
  C3.real (C3.hermitianPairing3 direction value)

mapWeightedEnergy :
  ∀ {r} {F : C3.RealField r} →
  (Z3.FourierMode → C3.Carrier F) →
  Velocity F →
  List Z3.FourierMode →
  List (C3.Carrier F)
mapWeightedEnergy weight velocity [] = []
mapWeightedEnergy {F = F} weight velocity (mode ∷ modes) =
  C3.multiply F (weight mode)
    (complex3SquaredMagnitude (velocity mode))
  ∷ mapWeightedEnergy weight velocity modes

mapCoherence :
  ∀ {r} {F : C3.RealField r} →
  (Z3.FourierMode → C3.Complex3 F) →
  Velocity F →
  List Z3.FourierMode →
  List (C3.Carrier F)
mapCoherence direction velocity [] = []
mapCoherence direction velocity (mode ∷ modes) =
  realHermitianCoordinate (direction mode) (velocity mode)
  ∷ mapCoherence direction velocity modes

record FourierQuarticParameters {r c : Level}
    (F : C3.RealField r) : Set (lsuc (r ⊔ c)) where
  field
    Chart : Set c
    cutoffModes : Nat → List Z3.FourierMode

    referenceWeight : Nat → Z3.FourierMode → C3.Carrier F
    quadraticWeight :
      Chart → Nat → Z3.FourierMode → C3.Carrier F
    coherenceDirection :
      Chart → Nat → Z3.FourierMode → C3.Complex3 F

    selectChart : Nat → Velocity F → Chart

open FourierQuarticParameters public

kineticEnergy :
  ∀ {r c} {F : C3.RealField r} →
  FourierQuarticParameters {r} {c} F →
  Nat → Velocity F → C3.Carrier F
kineticEnergy {F = F} P N velocity =
  sumScalars F
    (mapWeightedEnergy
      (referenceWeight P N)
      velocity
      (cutoffModes P N))

coherenceCoordinateAt :
  ∀ {r c} {F : C3.RealField r} →
  (P : FourierQuarticParameters {r} {c} F) →
  Chart P → Nat → Velocity F → C3.Carrier F
coherenceCoordinateAt {F = F} P chart N velocity =
  sumScalars F
    (mapCoherence
      (coherenceDirection P chart N)
      velocity
      (cutoffModes P N))

quadraticCorrectionAt :
  ∀ {r c} {F : C3.RealField r} →
  (P : FourierQuarticParameters {r} {c} F) →
  Chart P → Nat → Velocity F → C3.Carrier F
quadraticCorrectionAt {F = F} P chart N velocity =
  sumScalars F
    (mapWeightedEnergy
      (quadraticWeight P chart N)
      velocity
      (cutoffModes P N))

selectedCoherence :
  ∀ {r c} {F : C3.RealField r} →
  (P : FourierQuarticParameters {r} {c} F) →
  Nat → Velocity F → C3.Carrier F
selectedCoherence P N velocity =
  coherenceCoordinateAt P (selectChart P N velocity) N velocity

selectedQuadraticCorrection :
  ∀ {r c} {F : C3.RealField r} →
  (P : FourierQuarticParameters {r} {c} F) →
  Nat → Velocity F → C3.Carrier F
selectedQuadraticCorrection P N velocity =
  quadraticCorrectionAt P (selectChart P N velocity) N velocity

two : ∀ {r} (F : C3.RealField r) → C3.Carrier F
two F = C3.add F (C3.one F) (C3.one F)

quarticLyapunovValue :
  ∀ {r c} {F : C3.RealField r} →
  FourierQuarticParameters {r} {c} F →
  Nat → Velocity F → C3.Carrier F
quarticLyapunovValue {F = F} P N velocity =
  C3.add F
    (C3.add F
      (C3.multiply F
        (kineticEnergy P N velocity)
        (kineticEnergy P N velocity))
      (C3.multiply F
        (two F)
        (C3.multiply F
          (kineticEnergy P N velocity)
          (selectedCoherence P N velocity))))
    (selectedQuadraticCorrection P N velocity)

quarticLyapunovValueIsLiteralFiniteFourierSum :
  ∀ {r c} {F : C3.RealField r}
    (P : FourierQuarticParameters {r} {c} F)
    (N : Nat) (velocity : Velocity F) →
  quarticLyapunovValue P N velocity
  ≡
  C3.add F
    (C3.add F
      (C3.multiply F
        (kineticEnergy P N velocity)
        (kineticEnergy P N velocity))
      (C3.multiply F
        (two F)
        (C3.multiply F
          (kineticEnergy P N velocity)
          (selectedCoherence P N velocity))))
    (selectedQuadraticCorrection P N velocity)
quarticLyapunovValueIsLiteralFiniteFourierSum P N velocity = refl

record CoerciveFourierQuarticCandidate
    {r c o : Level}
    {F : C3.RealField r}
    (P : FourierQuarticParameters {r} {c} F) :
    Set (lsuc (r ⊔ c ⊔ o)) where
  field
    _≤_ : C3.Carrier F → C3.Carrier F → Set o
    lowerConstant upperConstant : C3.Carrier F

    lowerEquivalent : ∀ N velocity →
      _≤_
        (C3.multiply F lowerConstant
          (kineticEnergy P N velocity))
        (quarticLyapunovValue P N velocity)

    upperEquivalent : ∀ N velocity →
      _≤_
        (quarticLyapunovValue P N velocity)
        (C3.multiply F upperConstant
          (kineticEnergy P N velocity))

open CoerciveFourierQuarticCandidate public

literalFourierQuarticCandidateFamilyImplemented : Bool
literalFourierQuarticCandidateFamilyImplemented = true

literalFourierQuarticCandidateFamilyImplementedIsTrue :
  literalFourierQuarticCandidateFamilyImplemented ≡ true
literalFourierQuarticCandidateFamilyImplementedIsTrue = refl

coerciveCutoffUniformMemberDiscovered : Bool
coerciveCutoffUniformMemberDiscovered = false

coerciveCutoffUniformMemberDiscoveredIsFalse :
  coerciveCutoffUniformMemberDiscovered ≡ false
coerciveCutoffUniformMemberDiscoveredIsFalse = refl
