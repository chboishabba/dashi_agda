module DASHI.Physics.Closure.NSCompactGammaOffPacketTriadMajorization where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Analysis.FiniteWeightedKernelSums using (fold; map)
open import DASHI.Analysis.WeightedKernelSchurTest
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSWall1FourierShellInstance
open import DASHI.Physics.Closure.NSCompactGammaOffPacketWall1PairIncidenceBridge

------------------------------------------------------------------------
-- Local-to-global majorization for the compact-Gamma near response.
--
-- The previous Wall-1 adapter exposed one opaque analytic leaf
--
--   Near <= outputEnergy (exact Biot--Savart majorant action).
--
-- This module factors that leaf into the conventional proof obligations:
--
--   * reconstruct Near below the sum of absolute signed triad responses;
--   * prove one local bound for every differentiated triad contribution;
--   * identify the sum of those local majorants with the exact kernel action.
--
-- The finite sum inequality is proved here.  No local Fourier estimate or
-- cutoff-uniform constant is postulated or manufactured.
------------------------------------------------------------------------

data Pointwise
    {a b r : Level}
    {A : Set a}
    {B : Set b}
    (R : A → B → Set r) :
    List A → List B → Set (a ⊔ b ⊔ r) where
  pointwise[] : Pointwise R [] []
  pointwise∷ :
    ∀ {x y xs ys} →
    R x y →
    Pointwise R xs ys →
    Pointwise R (x ∷ xs) (y ∷ ys)

mapPointwise :
  ∀ {a b r}
    {A : Set a}
    {B : Set b}
    {R : A → B → Set r}
    (left : A → B)
    (right : A → B) →
  ((x : A) → R (left x) (right x)) →
  (xs : List A) →
  Pointwise R (map left xs) (map right xs)
mapPointwise left right local [] = pointwise[]
mapPointwise left right local (x ∷ xs) =
  pointwise∷ (local x) (mapPointwise left right local xs)

sumScalars :
  (A : AbsorptionArithmetic) →
  List (Scalar A) → Scalar A
sumScalars A = fold (_+_ A) (zero A)

record FiniteMajorantArithmetic
    (A : AbsorptionArithmetic) : Set₁ where
  field
    ≤-refl : (x : Scalar A) → _≤_ A x x

open FiniteMajorantArithmetic public

pointwiseSumMonotone :
  (A : AbsorptionArithmetic) →
  (M : FiniteMajorantArithmetic A) →
  ∀ {left right} →
  Pointwise (_≤_ A) left right →
  _≤_ A (sumScalars A left) (sumScalars A right)
pointwiseSumMonotone A M pointwise[] = ≤-refl M (zero A)
pointwiseSumMonotone A M (pointwise∷ headBound tailBound) =
  ≤-trans A
    (additionMonotoneRight A headBound)
    (additionMonotoneLeft A
      (pointwiseSumMonotone A M tailBound))

record TriadMajorizationInputs
    {p : Level}
    (PairAtom : Set p)
    (A : AbsorptionArithmetic)
    (M : FiniteMajorantArithmetic A) : Set (lsuc p) where
  field
    pairAtoms : List PairAtom

    signedTriadMagnitude : PairAtom → Scalar A
    triadMajorant : PairAtom → Scalar A

    localTriadMajorization :
      (pair : PairAtom) →
      _≤_ A (signedTriadMagnitude pair) (triadMajorant pair)

    concreteNearResponse : Scalar A
    majorantActionOutput : Scalar A

    nearBelowSignedTriadSum :
      _≤_ A concreteNearResponse
        (sumScalars A (map signedTriadMagnitude pairAtoms))

    majorantSumEqualsActionOutput :
      sumScalars A (map triadMajorant pairAtoms) ≡
      majorantActionOutput

open TriadMajorizationInputs public

triadMajorization :
  ∀ {p}
    {PairAtom : Set p}
    (A : AbsorptionArithmetic)
    (M : FiniteMajorantArithmetic A) →
  (I : TriadMajorizationInputs PairAtom A M) →
  _≤_ A (concreteNearResponse I) (majorantActionOutput I)
triadMajorization A M I =
  subst
    (λ upper → _≤_ A (concreteNearResponse I) upper)
    (majorantSumEqualsActionOutput I)
    (≤-trans A
      (nearBelowSignedTriadSum I)
      (pointwiseSumMonotone A M
        (mapPointwise
          (signedTriadMagnitude I)
          (triadMajorant I)
          (localTriadMajorization I)
          (pairAtoms I))))

------------------------------------------------------------------------
-- Wall-1 consumer.  Once the exact differentiated triad list is supplied, the
-- resulting local bounds inhabit the existing pair-incidence bridge directly.
------------------------------------------------------------------------

record Wall1TriadMajorizationInputs
    {p v : Level}
    (PairAtom : Set p)
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (M : FiniteMajorantArithmetic A)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) :
    Set (lsuc (p ⊔ v)) where
  field
    wall1ExactAction :
      ExactKernelAction
        (asWeightedKernelData (wall1PairIncidenceData W))
        L

    wall1Input : VectorIn L

    localTriadInputs :
      TriadMajorizationInputs PairAtom A M

    majorantOutputIsWall1Action :
      majorantActionOutput localTriadInputs ≡
      outputEnergy L
        (evaluateEntries wall1ExactAction
          (wall1BiotSavartKernel W)
          wall1Input)

open Wall1TriadMajorizationInputs public

wall1TriadMajorizationToNearInputs :
  ∀ {p v}
    {PairAtom : Set p}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (M : FiniteMajorantArithmetic A)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) →
  Wall1TriadMajorizationInputs PairAtom A M W L →
  Wall1NearMajorizationInputs A W L
wall1TriadMajorizationToNearInputs A M W L I = record
  { wall1ExactKernelAction = wall1ExactAction I
  ; wall1KernelInput = wall1Input I
  ; wall1ConcreteNearResponse =
      concreteNearResponse (localTriadInputs I)
  ; wall1ConcreteNearResponseBelowKernelAction =
      subst
        (λ upper →
          _≤_ A
            (concreteNearResponse (localTriadInputs I))
            upper)
        (majorantOutputIsWall1Action I)
        (triadMajorization A M (localTriadInputs I))
  }
