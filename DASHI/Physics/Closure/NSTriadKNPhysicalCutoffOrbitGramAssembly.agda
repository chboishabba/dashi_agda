module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact
import DASHI.Physics.Closure.NSTriadKNExactRetainedPairIncidences as Slots
import DASHI.Physics.Closure.NSTriadKNFiniteConvolutionReconstruction as Reconstruction
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitCoordinateVectors as Coordinates
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitInteraction as Interaction
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitModeSupport as Support
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitPairIncidences as Incidence
import DASHI.Physics.Closure.NSTriadKNPhysicalFourierInteraction as FourierInteraction

------------------------------------------------------------------------
-- The finite Gram order needs only additive order closure and square
-- positivity.  This authority is intentionally separate from the weaker
-- symbolic coefficient interface and from any eventual concrete real model.
------------------------------------------------------------------------

record FiniteGramOrderAuthority
    (K : Algebra.ExactOrderedCommutativeRing) : Set₁ where
  field
    zeroNonnegative :
      Scalar.Nonnegative (Algebra.orderedScalar K)
        (Scalar.zero (Algebra.orderedScalar K))
    zeroLeZero :
      Scalar._≤_ (Algebra.orderedScalar K)
        (Scalar.zero (Algebra.orderedScalar K))
        (Scalar.zero (Algebra.orderedScalar K))
    squareNonnegative :
      (x : Scalar.Scalar (Algebra.orderedScalar K)) →
      Scalar.Nonnegative (Algebra.orderedScalar K)
        (Algebra.square (Algebra.orderedScalar K) x)
    addNonnegative :
      {a b : Scalar.Scalar (Algebra.orderedScalar K)} →
      Scalar.Nonnegative (Algebra.orderedScalar K) a →
      Scalar.Nonnegative (Algebra.orderedScalar K) b →
      Scalar.Nonnegative (Algebra.orderedScalar K)
        (Scalar._+_ (Algebra.orderedScalar K) a b)
    addMonotone :
      {a b c d : Scalar.Scalar (Algebra.orderedScalar K)} →
      Scalar._≤_ (Algebra.orderedScalar K) a b →
      Scalar._≤_ (Algebra.orderedScalar K) c d →
      Scalar._≤_ (Algebra.orderedScalar K)
        (Scalar._+_ (Algebra.orderedScalar K) a c)
        (Scalar._+_ (Algebra.orderedScalar K) b d)

open FiniteGramOrderAuthority public

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

------------------------------------------------------------------------
-- Finite ordered folds and the orbit-native Gram order.
------------------------------------------------------------------------

sumNonnegative :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (O : FiniteGramOrderAuthority K) → {A : Set} →
  (f : A → Scalar.Scalar (Algebra.orderedScalar K)) → (xs : List A) →
  ((a : A) → Scalar.Nonnegative (Algebra.orderedScalar K) (f a)) →
  Scalar.Nonnegative (Algebra.orderedScalar K)
    (Exact.weightedListSum {S = Scalar.exactScalarOperations (Algebra.orderedScalar K)} f xs)
sumNonnegative K O f [] allNonnegative =
  zeroNonnegative O
sumNonnegative K O f (x ∷ xs) allNonnegative =
  addNonnegative O (allNonnegative x)
    (sumNonnegative K O f xs allNonnegative)

sumMonotone :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (O : FiniteGramOrderAuthority K) → {A : Set} →
  (f g : A → Scalar.Scalar (Algebra.orderedScalar K)) → (xs : List A) →
  ((a : A) → Scalar._≤_ (Algebra.orderedScalar K) (f a) (g a)) →
  Scalar._≤_ (Algebra.orderedScalar K)
    (Exact.weightedListSum {S = Scalar.exactScalarOperations (Algebra.orderedScalar K)} f xs)
    (Exact.weightedListSum {S = Scalar.exactScalarOperations (Algebra.orderedScalar K)} g xs)
sumMonotone K O f g [] pointwise = zeroLeZero O
sumMonotone K O f g (x ∷ xs) pointwise =
  addMonotone O (pointwise x) (sumMonotone K O f g xs pointwise)

orbitNegativeRankOneTermNonnegative :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (O : FiniteGramOrderAuthority K) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} →
  {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  (r : Support.OrbitPhysicalCutoffIncidence N R) → (z : OrbitVector K N R) →
  Scalar.Nonnegative (Algebra.orderedScalar K)
    (Scalar._*_ (Algebra.orderedScalar K)
      (orbitNegativeCoefficient I R law u r)
      (Algebra.square (Algebra.orderedScalar K)
        (orbitInner K (orbitIncidenceVector K N R r) z)))
orbitNegativeRankOneTermNonnegative K O I R law u r z =
  Scalar.multiplicationPreservesNonnegative (Algebra.orderedScalar K)
    (Incidence.orbitIncidenceMNegNonnegative I R law u (proj₁ r))
    (squareNonnegative O (orbitInner K (orbitIncidenceVector K _ _ r) z))

orbitAbsoluteRankOneTermNonnegative :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (O : FiniteGramOrderAuthority K) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} →
  {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  (r : Support.OrbitPhysicalCutoffIncidence N R) → (z : OrbitVector K N R) →
  Scalar.Nonnegative (Algebra.orderedScalar K)
    (Scalar._*_ (Algebra.orderedScalar K)
      (orbitAbsoluteCoefficient I R law u r)
      (Algebra.square (Algebra.orderedScalar K)
        (orbitInner K (orbitIncidenceVector K N R r) z)))
orbitAbsoluteRankOneTermNonnegative K O I R law u r z =
  Scalar.multiplicationPreservesNonnegative (Algebra.orderedScalar K)
    (Incidence.orbitIncidenceMAbsNonnegative I R law u (proj₁ r))
    (squareNonnegative O (orbitInner K (orbitIncidenceVector K _ _ r) z))

orbitRankOneTermMonotone :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (O : FiniteGramOrderAuthority K) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} →
  {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  (r : Support.OrbitPhysicalCutoffIncidence N R) → (z : OrbitVector K N R) →
  Scalar._≤_ (Algebra.orderedScalar K)
    (Scalar._*_ (Algebra.orderedScalar K) (orbitNegativeCoefficient I R law u r)
      (Algebra.square (Algebra.orderedScalar K) (orbitInner K (orbitIncidenceVector K N R r) z)))
    (Scalar._*_ (Algebra.orderedScalar K) (orbitAbsoluteCoefficient I R law u r)
      (Algebra.square (Algebra.orderedScalar K) (orbitInner K (orbitIncidenceVector K N R r) z)) )
orbitRankOneTermMonotone K O I R law u r z
  rewrite Algebra.mulCommutative K
    (orbitNegativeCoefficient I R law u r)
    (Algebra.square (Algebra.orderedScalar K) (orbitInner K (orbitIncidenceVector K _ _ r) z))
  | Algebra.mulCommutative K
    (orbitAbsoluteCoefficient I R law u r)
    (Algebra.square (Algebra.orderedScalar K) (orbitInner K (orbitIncidenceVector K _ _ r) z)) =
  Scalar.multiplicationMonotoneNonnegativeRight (Algebra.orderedScalar K)
    (squareNonnegative O (orbitInner K (orbitIncidenceVector K _ _ r) z))
    (Incidence.orbitIncidenceMNegLeMAbs I R law u (proj₁ r))

orbitLNegPositiveSemidefinite :
  (K : Algebra.ExactOrderedCommutativeRing) → (O : FiniteGramOrderAuthority K) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} → {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  (z : OrbitVector K N R) →
  Scalar.Nonnegative (Algebra.orderedScalar K)
    (orbitInner K z (physicalOrbitLNeg K I R law u z))
orbitLNegPositiveSemidefinite K O I R law u z
  rewrite orbitNegativeRankOneQuadraticExpansion K I R law u z =
  sumNonnegative K O _ _ (λ r → orbitNegativeRankOneTermNonnegative K O I R law u r z)

orbitLAbsPositiveSemidefinite :
  (K : Algebra.ExactOrderedCommutativeRing) → (O : FiniteGramOrderAuthority K) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} → {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  (z : OrbitVector K N R) →
  Scalar.Nonnegative (Algebra.orderedScalar K)
    (orbitInner K z (physicalOrbitLAbs K I R law u z))
orbitLAbsPositiveSemidefinite K O I R law u z
  rewrite orbitAbsoluteRankOneQuadraticExpansion K I R law u z =
  sumNonnegative K O _ _ (λ r → orbitAbsoluteRankOneTermNonnegative K O I R law u r z)

orbitLNegLeLAbs :
  (K : Algebra.ExactOrderedCommutativeRing) → (O : FiniteGramOrderAuthority K) →
  {C : Fourier.ComplexFourierInterface (Algebra.orderedScalar K)} → {N : Nat} →
  {interaction : Fourier.PhysicalTriadInteractionLaw (Algebra.orderedScalar K) C N} →
  (I : FourierInteraction.ExactNSFourierInteractionStructure (Algebra.orderedScalar K) C) →
  (R : Nat) → (law : Interaction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData (Algebra.orderedScalar K) C N interaction) →
  (z : OrbitVector K N R) →
  Scalar._≤_ (Algebra.orderedScalar K)
    (orbitInner K z (physicalOrbitLNeg K I R law u z))
    (orbitInner K z (physicalOrbitLAbs K I R law u z))
orbitLNegLeLAbs K O I R law u z
  rewrite orbitNegativeRankOneQuadraticExpansion K I R law u z
        | orbitAbsoluteRankOneQuadraticExpansion K I R law u z =
  sumMonotone K O _ _ _ (λ r → orbitRankOneTermMonotone K O I R law u r z)

------------------------------------------------------------------------
-- Coordinate-level diagonal multigraph facts.  Function extensionality is
-- intentionally not assumed: these are the pointwise vector equalities used
-- by every finite-coordinate quadratic calculation.
------------------------------------------------------------------------

orbitIncidenceVectorZeroPointwise :
  (K : Algebra.ExactOrderedCommutativeRing) → {N R : Nat} →
  (r : Support.OrbitPhysicalCutoffIncidence N R) →
  Support.orbitSourceCoordinate N R r ≡ Support.orbitTargetCoordinate N R r →
  (i : Support.physicalCutoffOrbitModeCoordinate N R) →
  orbitIncidenceVector K N R r i ≡ Coordinates.orbitZeroVector
    (Algebra.orderedScalar K) N R i
orbitIncidenceVectorZeroPointwise K r source≡target i
  rewrite source≡target =
  trans
    (Algebra.addCommutative K
      (Coordinates.orbitBasisVector (Algebra.orderedScalar K)
        (Support.orbitTargetCoordinate _ _ r) i)
      (Scalar.neg (Algebra.orderedScalar K)
        (Coordinates.orbitBasisVector (Algebra.orderedScalar K)
          (Support.orbitTargetCoordinate _ _ r) i)))
    (Algebra.addInverseLeft K
      (Coordinates.orbitBasisVector (Algebra.orderedScalar K)
        (Support.orbitTargetCoordinate _ _ r) i))

orbitIncidenceVectorPointwiseCong :
  (K : Algebra.ExactOrderedCommutativeRing) → {N R : Nat} →
  (r s : Support.OrbitPhysicalCutoffIncidence N R) →
  Support.orbitSourceCoordinate N R r ≡ Support.orbitSourceCoordinate N R s →
  Support.orbitTargetCoordinate N R r ≡ Support.orbitTargetCoordinate N R s →
  (i : Support.physicalCutoffOrbitModeCoordinate N R) →
  orbitIncidenceVector K N R r i ≡ orbitIncidenceVector K N R s i
orbitIncidenceVectorPointwiseCong K r s source≡ target≡ i
  rewrite source≡ | target≡ = refl

diagonalFirstIncidenceVectorZeroPointwise :
  (K : Algebra.ExactOrderedCommutativeRing) → {N R : Nat} →
  (r : Support.OrbitPhysicalCutoffIncidence N R) →
  Incidence.slot (proj₁ r) ≡ Slots.firstPair →
  Reconstruction.orbitKind (Incidence.orbit (proj₁ r)) ≡
    Reconstruction.diagonal →
  (i : Support.physicalCutoffOrbitModeCoordinate N R) →
  orbitIncidenceVector K N R r i ≡ Coordinates.orbitZeroVector
    (Algebra.orderedScalar K) N R i
diagonalFirstIncidenceVectorZeroPointwise K {N} {R} r first diagonal i =
  orbitIncidenceVectorZeroPointwise K r coordinateEquality i
  where
    endpointEquality :
      Incidence.orbitIncidenceSource (proj₁ r) ≡
      Incidence.orbitIncidenceTarget (proj₁ r)
    endpointEquality rewrite first =
      Incidence.diagonalFirstSlotEndpointsAgree (Incidence.orbit (proj₁ r)) diagonal

    decodedEquality :
      Support.orbitCoordinateMode N R (Support.orbitSourceCoordinate N R r) ≡
      Support.orbitCoordinateMode N R (Support.orbitTargetCoordinate N R r)
    decodedEquality =
      trans (sym (Support.orbitSourceCoordinateCorrect N R r))
        (trans endpointEquality (Support.orbitTargetCoordinateCorrect N R r))

    coordinateEquality :
      Support.orbitSourceCoordinate N R r ≡ Support.orbitTargetCoordinate N R r
    coordinateEquality = Support.orbitCoordinateModeInjective N R _ _ decodedEquality

diagonalRemainingIncidenceVectorsEqualPointwise :
  (K : Algebra.ExactOrderedCommutativeRing) → {N R : Nat} →
  (r s : Support.OrbitPhysicalCutoffIncidence N R) →
  Incidence.orbit (proj₁ r) ≡ Incidence.orbit (proj₁ s) →
  Incidence.slot (proj₁ r) ≡ Slots.secondPair →
  Incidence.slot (proj₁ s) ≡ Slots.thirdPair →
  Reconstruction.orbitKind (Incidence.orbit (proj₁ s)) ≡ Reconstruction.diagonal →
  (i : Support.physicalCutoffOrbitModeCoordinate N R) →
  orbitIncidenceVector K N R r i ≡ orbitIncidenceVector K N R s i
diagonalRemainingIncidenceVectorsEqualPointwise K {N} {R} r s sameOrbit second third diagonal i =
  orbitIncidenceVectorPointwiseCong K r s sourceCoordinates targetCoordinates i
  where
    endpointEqualities :
      (Incidence.orbitIncidenceSource (proj₁ r) ≡
       Incidence.orbitIncidenceSource (proj₁ s)) ×
      (Incidence.orbitIncidenceTarget (proj₁ r) ≡
       Incidence.orbitIncidenceTarget (proj₁ s))
    endpointEqualities rewrite sameOrbit | second | third =
      Incidence.diagonalRemainingSlotEndpointsAgree (Incidence.orbit (proj₁ s)) diagonal

    sourceDecoded :
      Support.orbitCoordinateMode N R (Support.orbitSourceCoordinate N R r) ≡
      Support.orbitCoordinateMode N R (Support.orbitSourceCoordinate N R s)
    sourceDecoded =
      trans (sym (Support.orbitSourceCoordinateCorrect N R r))
        (trans (proj₁ endpointEqualities) (Support.orbitSourceCoordinateCorrect N R s))

    targetDecoded :
      Support.orbitCoordinateMode N R (Support.orbitTargetCoordinate N R r) ≡
      Support.orbitCoordinateMode N R (Support.orbitTargetCoordinate N R s)
    targetDecoded =
      trans (sym (Support.orbitTargetCoordinateCorrect N R r))
        (trans (proj₂ endpointEqualities) (Support.orbitTargetCoordinateCorrect N R s))

    sourceCoordinates :
      Support.orbitSourceCoordinate N R r ≡ Support.orbitSourceCoordinate N R s
    sourceCoordinates = Support.orbitCoordinateModeInjective N R _ _ sourceDecoded

    targetCoordinates :
      Support.orbitTargetCoordinate N R r ≡ Support.orbitTargetCoordinate N R s
    targetCoordinates = Support.orbitCoordinateModeInjective N R _ _ targetDecoded
