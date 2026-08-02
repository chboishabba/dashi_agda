module DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Loukas
-- Grafakos; Seungly Oh; DASHI repository contributors.
-- Title: "Ordered Euclidean and finite l2 carrier for the Stage-3 Fourier
-- shell estimate".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; Communications in Partial Differential Equations 39
-- (2014), 1128--1157; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7; 10.1080/03605302.2013.822885;
-- repository-original carrier definitions have no DOI.
-- Uses: positive squared complex modulus, the C3 Euclidean squared norm,
-- finite l2 sums, order compatibility, and finite Cauchy--Schwarz.
-- Relationship: extends the exact algebraic C3 carrier without adding order
-- or completeness axioms to RealField itself.  The definitions are concrete;
-- an ordered-real instance and its finite Cauchy--Schwarz theorem remain a
-- separate analytic instantiation.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

complexModulusSquared :
  ∀ {r} {F : C3.RealField r} → C3.Complex F → C3.Carrier F
complexModulusSquared {F = F} z =
  C3.add F
    (C3.multiply F (C3.real z) (C3.real z))
    (C3.multiply F (C3.imaginary z) (C3.imaginary z))

complex3NormSquared :
  ∀ {r} {F : C3.RealField r} → C3.Complex3 F → C3.Carrier F
complex3NormSquared {F = F} v =
  C3.add F
    (C3.add F
      (complexModulusSquared (C3.x v))
      (complexModulusSquared (C3.y v)))
    (complexModulusSquared (C3.z v))

finiteComplexL2NormSquared :
  ∀ {i r} {Index : Set i} {F : C3.RealField r} →
  List Index → (Index → C3.Complex F) → C3.Carrier F
finiteComplexL2NormSquared {F = F} [] values = C3.zero F
finiteComplexL2NormSquared {F = F} (index ∷ indices) values =
  C3.add F
    (complexModulusSquared (values index))
    (finiteComplexL2NormSquared indices values)

finiteComplex3L2NormSquared :
  ∀ {i r} {Index : Set i} {F : C3.RealField r} →
  List Index → (Index → C3.Complex3 F) → C3.Carrier F
finiteComplex3L2NormSquared {F = F} [] values = C3.zero F
finiteComplex3L2NormSquared {F = F} (index ∷ indices) values =
  C3.add F
    (complex3NormSquared (values index))
    (finiteComplex3L2NormSquared indices values)

record OrderedRealExtension
    {r : Level} (F : C3.RealField r) : Set (lsuc r) where
  field
    _≤_ : C3.Carrier F → C3.Carrier F → Set r

    leqReflexive : ∀ value → value ≤ value
    leqTransitive : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    addMonotone : ∀ {a b c d} → a ≤ b → c ≤ d →
      C3.add F a c ≤ C3.add F b d

    zeroBelowSquare : ∀ value →
      C3.zero F ≤ C3.multiply F value value
    zeroBelowAdd : ∀ {a b} →
      C3.zero F ≤ a → C3.zero F ≤ b → C3.zero F ≤ C3.add F a b

    subtract : C3.Carrier F → C3.Carrier F → C3.Carrier F
    subtractMeaning : ∀ a b →
      subtract a b ≡ C3.add F a (C3.negate F b)
    subtractNonnegativeBelow : ∀ {a b} →
      C3.zero F ≤ b → subtract a b ≤ a

open OrderedRealExtension public

record EuclideanComplex3Laws
    {r : Level}
    {F : C3.RealField r}
    (O : OrderedRealExtension F) : Set (lsuc r) where
  field
    selfPairingRealPartIsNormSquared : ∀ value →
      C3.real (C3.hermitianPairing3 value value)
      ≡ complex3NormSquared value

    normSquaredNonnegative : ∀ value →
      _≤_ O (C3.zero F) (complex3NormSquared value)

    normSquaredZeroImpliesZero : ∀ value →
      complex3NormSquared value ≡ C3.zero F →
      value ≡ C3.complex3Zero F

open EuclideanComplex3Laws public

record FiniteComplexL2Laws
    {i r : Level}
    {Index : Set i}
    {F : C3.RealField r}
    (O : OrderedRealExtension F) : Set (lsuc (i ⊔ r)) where
  field
    support : List Index

    finiteCauchySchwarz :
      ∀ left right pairedSumSquared →
      _≤_ O pairedSumSquared
        (C3.multiply F
          (finiteComplexL2NormSquared support left)
          (finiteComplexL2NormSquared support right))

    restrictionDoesNotIncreaseL2 :
      ∀ restricted full →
      _≤_ O
        (finiteComplexL2NormSquared support restricted)
        (finiteComplexL2NormSquared support full)

open FiniteComplexL2Laws public

complexModulusSquaredDefined : Bool
complexModulusSquaredDefined = true

complexModulusSquaredDefinedIsTrue : complexModulusSquaredDefined ≡ true
complexModulusSquaredDefinedIsTrue = refl

complex3NormSquaredDefined : Bool
complex3NormSquaredDefined = true

complex3NormSquaredDefinedIsTrue : complex3NormSquaredDefined ≡ true
complex3NormSquaredDefinedIsTrue = refl

finiteL2NormSquaredDefined : Bool
finiteL2NormSquaredDefined = true

finiteL2NormSquaredDefinedIsTrue : finiteL2NormSquaredDefined ≡ true
finiteL2NormSquaredDefinedIsTrue = refl

orderedEuclideanL2SurfaceRepresented : Bool
orderedEuclideanL2SurfaceRepresented = true

orderedEuclideanL2SurfaceRepresentedIsTrue :
  orderedEuclideanL2SurfaceRepresented ≡ true
orderedEuclideanL2SurfaceRepresentedIsTrue = refl

concreteOrderedRealAndFiniteCauchySchwarzClosed : Bool
concreteOrderedRealAndFiniteCauchySchwarzClosed = false

concreteOrderedRealAndFiniteCauchySchwarzClosedIsFalse :
  concreteOrderedRealAndFiniteCauchySchwarzClosed ≡ false
concreteOrderedRealAndFiniteCauchySchwarzClosedIsFalse = refl
