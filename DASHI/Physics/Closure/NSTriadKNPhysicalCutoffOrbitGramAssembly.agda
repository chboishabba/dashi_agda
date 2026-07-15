module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitCoordinateVectors as Coordinates
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitInteraction as Interaction
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitModeSupport as Support
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitPairIncidences as Incidence
import DASHI.Physics.Closure.NSTriadKNPhysicalFourierInteraction as FourierInteraction

------------------------------------------------------------------------
-- Orbit-native finite Gram assembly.
--
-- This module consumes only the canonical swap-orbit incidence occurrences.
-- The older labelled-triad assembly is deliberately not used to define either
-- operator below; it remains a separately proved compatibility layer.
------------------------------------------------------------------------

OrbitVector :
  (K : Algebra.ExactOrderedCommutativeRing) → (N R : Nat) → Set
OrbitVector K N R = Coordinates.PhysicalCutoffOrbitVector
  (Algebra.orderedScalar K) N R

orbitInner :
  (K : Algebra.ExactOrderedCommutativeRing) → {N R : Nat} →
  OrbitVector K N R → OrbitVector K N R → Scalar.Scalar (Algebra.orderedScalar K)
orbitInner K = Algebra.innerFin (Algebra.orderedScalar K)

orbitIncidenceVector :
  (K : Algebra.ExactOrderedCommutativeRing) → (N R : Nat) →
  Support.OrbitPhysicalCutoffIncidence N R → OrbitVector K N R
orbitIncidenceVector K N R =
  Coordinates.orbitPairIncidenceVector (Algebra.orderedScalar K) N R

orbitNegativeCoefficient :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure S C) → (R : Nat) →
  (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  Support.OrbitPhysicalCutoffIncidence N R → Scalar.Scalar S
orbitNegativeCoefficient I R law u r =
  Incidence.orbitIncidenceMNeg I R law u (proj₁ r)

orbitAbsoluteCoefficient :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure S C) → (R : Nat) →
  (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  Support.OrbitPhysicalCutoffIncidence N R → Scalar.Scalar S
orbitAbsoluteCoefficient I R law u r =
  Incidence.orbitIncidenceMAbs I R law u (proj₁ r)

physicalOrbitLNeg :
  (K : Algebra.ExactOrderedCommutativeRing) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} →
  {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) →
  (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  OrbitVector K N R → OrbitVector K N R
physicalOrbitLNeg K {N = N} I R law u =
  Algebra.rankOneFold K
    (orbitNegativeCoefficient I R law u)
    (orbitIncidenceVector K N R)
    (Support.physicalCutoffOrbitIndexedIncidences N R)

physicalOrbitLAbs :
  (K : Algebra.ExactOrderedCommutativeRing) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} →
  {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) →
  (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  OrbitVector K N R → OrbitVector K N R
physicalOrbitLAbs K {N = N} I R law u =
  Algebra.rankOneFold K
    (orbitAbsoluteCoefficient I R law u)
    (orbitIncidenceVector K N R)
    (Support.physicalCutoffOrbitIndexedIncidences N R)

orbitNegativeRankOneQuadraticExpansion :
  (K : Algebra.ExactOrderedCommutativeRing) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} →
  {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  (z : OrbitVector K N R) →
  orbitInner K {N = N} {R = R} z (physicalOrbitLNeg K I R law u z) ≡
  Exact.weightedListSum {S = Scalar.exactScalarOperations (Algebra.orderedScalar K)}
    (λ r → Scalar._*_ (Algebra.orderedScalar K)
      (orbitNegativeCoefficient I R law u r)
      (Algebra.square (Algebra.orderedScalar K)
        (orbitInner K {N = N} {R = R} (orbitIncidenceVector K N R r) z)))
    (Support.physicalCutoffOrbitIndexedIncidences N R)
orbitNegativeRankOneQuadraticExpansion K {N = N} I R law u z =
  Algebra.rankOneFoldQuadraticExpansion K
    (orbitNegativeCoefficient I R law u)
    (orbitIncidenceVector K N R)
    (Support.physicalCutoffOrbitIndexedIncidences N R) z

orbitAbsoluteRankOneQuadraticExpansion :
  (K : Algebra.ExactOrderedCommutativeRing) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} →
  {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  (z : OrbitVector K N R) →
  orbitInner K {N = N} {R = R} z (physicalOrbitLAbs K I R law u z) ≡
  Exact.weightedListSum {S = Scalar.exactScalarOperations (Algebra.orderedScalar K)}
    (λ r → Scalar._*_ (Algebra.orderedScalar K)
      (orbitAbsoluteCoefficient I R law u r)
      (Algebra.square (Algebra.orderedScalar K)
        (orbitInner K {N = N} {R = R} (orbitIncidenceVector K N R r) z)))
    (Support.physicalCutoffOrbitIndexedIncidences N R)
orbitAbsoluteRankOneQuadraticExpansion K {N = N} I R law u z =
  Algebra.rankOneFoldQuadraticExpansion K
    (orbitAbsoluteCoefficient I R law u)
    (orbitIncidenceVector K N R)
    (Support.physicalCutoffOrbitIndexedIncidences N R) z

orbitContrastTerm :
  (K : Algebra.ExactOrderedCommutativeRing) → {N R : Nat} →
  Support.OrbitPhysicalCutoffIncidence N R → OrbitVector K N R →
  Scalar.Scalar (Algebra.orderedScalar K)
orbitContrastTerm K {N = N} {R = R} r z = Scalar._+_ (Algebra.orderedScalar K)
  (z (Support.orbitSourceCoordinate N R r))
  (Scalar.neg (Algebra.orderedScalar K)
    (z (Support.orbitTargetCoordinate N R r)))

physicalOrbitNegativeTransferContrast :
  (K : Algebra.ExactOrderedCommutativeRing) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} →
  {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  OrbitVector K N R → Scalar.Scalar (Algebra.orderedScalar K)
physicalOrbitNegativeTransferContrast K {N = N} I R law u z =
  Exact.weightedListSum {S = Scalar.exactScalarOperations (Algebra.orderedScalar K)}
    (λ r → Scalar._*_ (Algebra.orderedScalar K)
      (orbitNegativeCoefficient I R law u r)
      (Algebra.square (Algebra.orderedScalar K)
        (orbitContrastTerm K {N = N} {R = R} r z)))
    (Support.physicalCutoffOrbitIndexedIncidences N R)

weightedListSumCong :
  (S : Scalar.ExactOrderedScalar) → {A : Set} →
  (f g : A → Scalar.Scalar S) → (xs : List A) →
  ((a : A) → f a ≡ g a) →
  Exact.weightedListSum {S = Scalar.exactScalarOperations S} f xs ≡
  Exact.weightedListSum {S = Scalar.exactScalarOperations S} g xs
weightedListSumCong S f g [] pointwise = refl
weightedListSumCong S f g (a ∷ as) pointwise =
  cong₂ (Scalar._+_ S) (pointwise a)
    (weightedListSumCong S f g as pointwise)

orbitIncidenceEvaluation :
  (K : Algebra.ExactOrderedCommutativeRing) → {N R : Nat} →
  (r : Support.OrbitPhysicalCutoffIncidence N R) → (z : OrbitVector K N R) →
  orbitInner K {N = N} {R = R} (orbitIncidenceVector K N R r) z ≡
  orbitContrastTerm K {N = N} {R = R} r z
orbitIncidenceEvaluation K {N} {R} r z =
  Algebra.coordinateBasisDifferenceInner K
    (Support.orbitSourceCoordinate N R r)
    (Support.orbitTargetCoordinate N R r) z

physicalOrbitNegativeTransferContrastGramIdentity :
  (K : Algebra.ExactOrderedCommutativeRing) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} →
  {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  (z : OrbitVector K N R) →
  physicalOrbitNegativeTransferContrast K I R law u z ≡
  orbitInner K {N = N} {R = R} z (physicalOrbitLNeg K I R law u z)
physicalOrbitNegativeTransferContrastGramIdentity K {N = N} I R law u z =
  trans
    (weightedListSumCong (Algebra.orderedScalar K) _ _
      (Support.physicalCutoffOrbitIndexedIncidences N R)
      (λ r → cong (λ q → Scalar._*_ (Algebra.orderedScalar K)
        (orbitNegativeCoefficient I R law u r)
        (Algebra.square (Algebra.orderedScalar K) q))
        (sym (orbitIncidenceEvaluation K {N = N} {R = R} r z))))
    (sym (orbitNegativeRankOneQuadraticExpansion K I R law u z))
