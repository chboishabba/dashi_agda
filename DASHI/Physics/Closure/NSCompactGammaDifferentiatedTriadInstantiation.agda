module DASHI.Physics.Closure.NSCompactGammaDifferentiatedTriadInstantiation where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Analysis.FiniteWeightedKernelSums using (map)
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSDifferentiatedTriadAnalyticLeaf as Analytic
import DASHI.Physics.Closure.NSCompactGammaOffPacketTriadMajorization as Major

------------------------------------------------------------------------
-- Adapter from the pointwise differentiated Fourier theorem to the exact finite
-- triad-summation owner used by the compact-Gamma Schur bridge.
------------------------------------------------------------------------

record DifferentiatedTriadAtomFamily
    {p m v : Level}
    (PairAtom : Set p)
    (Mode : Set m)
    (Vector : Set v)
    (A : AbsorptionArithmetic)
    (M : Major.FiniteMajorantArithmetic A) :
    Set (lsuc (p ⊔ m ⊔ v)) where
  field
    laws : Analytic.TriadAnalyticLaws Mode Vector (Scalar A)
    projectedBound : Analytic.ProjectedInteractionBound laws
    nearResponse : Analytic.CompactGammaNearResponse laws
    coefficientMonotonicity :
      Analytic.CompactGammaCoefficientMonotonicity laws

    -- Proof-relevant conversion from the normed analytic order to the order used
    -- by the absorption/Schur arithmetic.  This is safer than an equality of
    -- proposition-valued functions and is exactly what the local theorem needs.
    analyticOrderToAbsorption :
      ∀ {x y : Scalar A} →
      Analytic._≤_ laws x y →
      _≤_ A x y

    pairAtoms : List PairAtom

    targetMode : PairAtom → Mode
    leftMode : PairAtom → Mode
    rightMode : PairAtom → Mode

    baseLeft : PairAtom → Vector
    baseRight : PairAtom → Vector
    tangentLeft : PairAtom → Vector
    tangentRight : PairAtom → Vector

    signedTriadMagnitude : PairAtom → Scalar A
    triadMajorant : PairAtom → Scalar A

    signedMagnitudeIsAnalyticLeaf :
      (atom : PairAtom) →
      signedTriadMagnitude atom ≡
      Analytic.absolute laws
        (Analytic.numeratorDerivative nearResponse (targetMode atom)
          (Analytic.differentiatedProjectedTriad laws
            (targetMode atom)
            (leftMode atom)
            (rightMode atom)
            (baseLeft atom)
            (baseRight atom)
            (tangentLeft atom)
            (tangentRight atom)))

    majorantIsAnalyticLeaf :
      (atom : PairAtom) →
      triadMajorant atom ≡
      Analytic.compactGammaDifferentiatedTriadMajorant
        laws nearResponse
        (targetMode atom)
        (leftMode atom)
        (rightMode atom)
        (baseLeft atom)
        (baseRight atom)
        (tangentLeft atom)
        (tangentRight atom)

    concreteNearResponse : Scalar A
    majorantActionOutput : Scalar A

    nearBelowSignedTriadSum :
      _≤_ A concreteNearResponse
        (Major.sumScalars A (map signedTriadMagnitude pairAtoms))

    majorantSumEqualsActionOutput :
      Major.sumScalars A (map triadMajorant pairAtoms) ≡
      majorantActionOutput

open DifferentiatedTriadAtomFamily public

localTriadMajorizationFromAnalyticLeaf :
  ∀ {p m v}
    {PairAtom : Set p}
    {Mode : Set m}
    {Vector : Set v}
    {A : AbsorptionArithmetic}
    {M : Major.FiniteMajorantArithmetic A} →
  (F : DifferentiatedTriadAtomFamily PairAtom Mode Vector A M) →
  (atom : PairAtom) →
  _≤_ A (signedTriadMagnitude F atom) (triadMajorant F atom)
localTriadMajorizationFromAnalyticLeaf F atom
  rewrite signedMagnitudeIsAnalyticLeaf F atom
        | majorantIsAnalyticLeaf F atom =
  analyticOrderToAbsorption F
    (Analytic.concrete-differentiated-triad-bound
      (laws F)
      (projectedBound F)
      (nearResponse F)
      (coefficientMonotonicity F)
      (targetMode F atom)
      (leftMode F atom)
      (rightMode F atom)
      (baseLeft F atom)
      (baseRight F atom)
      (tangentLeft F atom)
      (tangentRight F atom))

asTriadMajorizationInputs :
  ∀ {p m v}
    {PairAtom : Set p}
    {Mode : Set m}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (M : Major.FiniteMajorantArithmetic A) →
  DifferentiatedTriadAtomFamily PairAtom Mode Vector A M →
  Major.TriadMajorizationInputs PairAtom A M
asTriadMajorizationInputs A M F = record
  { pairAtoms = pairAtoms F
  ; signedTriadMagnitude = signedTriadMagnitude F
  ; triadMajorant = triadMajorant F
  ; localTriadMajorization = localTriadMajorizationFromAnalyticLeaf F
  ; concreteNearResponse = concreteNearResponse F
  ; majorantActionOutput = majorantActionOutput F
  ; nearBelowSignedTriadSum = nearBelowSignedTriadSum F
  ; majorantSumEqualsActionOutput = majorantSumEqualsActionOutput F
  }

analyticTriadsMajorizeNearResponse :
  ∀ {p m v}
    {PairAtom : Set p}
    {Mode : Set m}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (M : Major.FiniteMajorantArithmetic A) →
  (F : DifferentiatedTriadAtomFamily PairAtom Mode Vector A M) →
  _≤_ A (concreteNearResponse F) (majorantActionOutput F)
analyticTriadsMajorizeNearResponse A M F =
  Major.triadMajorization A M (asTriadMajorizationInputs A M F)
