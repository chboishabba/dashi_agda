module DASHI.Physics.Closure.ShiftFiniteLocalOPECrossing where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Tangent
open import DASHI.Physics.Closure.ShiftFiniteScalingFusionWard as Finite

------------------------------------------------------------------------
-- Finite local operator-product analogue.
--
-- A field insertion is an operator paired with one of two explicit sites.  The
-- OPE coefficient is proof-relevant: it is inhabited exactly when the proposed
-- output equals the already-proved finite fusion product.  Locality is the
-- commutativity of that product and crossing is its associativity.
--
-- This is a genuine finite algebraic OPE/crossing theorem on the current
-- carrier.  It is not a continuum local quantum field theory: there is no
-- topology of insertion points, singular expansion, analytic coefficient,
-- convergence domain, reflection positivity, or conformal block expansion.

data InsertionSite : Set where
  leftSite : InsertionSite
  rightSite : InsertionSite

record LocalInsertion : Set where
  constructor insert
  field
    site : InsertionSite
    operator : Tangent.ShiftFinitePerturbation

open LocalInsertion public

OPECoefficient :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Set
OPECoefficient p q r = Finite._⊗p_ p q ≡ r

canonicalOPECoefficient :
  (p q : Tangent.ShiftFinitePerturbation) →
  OPECoefficient p q (Finite._⊗p_ p q)
canonicalOPECoefficient p q = refl

fusionCommutative :
  (p q : Tangent.ShiftFinitePerturbation) →
  Finite._⊗p_ p q ≡ Finite._⊗p_ q p
fusionCommutative Tangent.startPerturbation Tangent.startPerturbation = refl
fusionCommutative Tangent.startPerturbation Tangent.nextPerturbation = refl
fusionCommutative Tangent.startPerturbation Tangent.zeroPerturbation = refl
fusionCommutative Tangent.nextPerturbation Tangent.startPerturbation = refl
fusionCommutative Tangent.nextPerturbation Tangent.nextPerturbation = refl
fusionCommutative Tangent.nextPerturbation Tangent.zeroPerturbation = refl
fusionCommutative Tangent.zeroPerturbation Tangent.startPerturbation = refl
fusionCommutative Tangent.zeroPerturbation Tangent.nextPerturbation = refl
fusionCommutative Tangent.zeroPerturbation Tangent.zeroPerturbation = refl

localityExchange :
  (p q : Tangent.ShiftFinitePerturbation) →
  OPECoefficient p q (Finite._⊗p_ p q) →
  OPECoefficient q p (Finite._⊗p_ p q)
localityExchange p q refl = fusionCommutative q p

crossingAssociativity :
  (p q r : Tangent.ShiftFinitePerturbation) →
  Finite._⊗p_ (Finite._⊗p_ p q) r
    ≡
  Finite._⊗p_ p (Finite._⊗p_ q r)
crossingAssociativity = Finite.fusionAssociative

fourPointChannel :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation
fourPointChannel p q r = Finite._⊗p_ (Finite._⊗p_ p q) r

fourPointCrossing :
  (p q r : Tangent.ShiftFinitePerturbation) →
  fourPointChannel p q r
    ≡
  Finite._⊗p_ p (Finite._⊗p_ q r)
fourPointCrossing = crossingAssociativity

finiteOPESelectionValue :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Nat
finiteOPESelectionValue p q r with Finite._⊗p_ p q | r
... | Tangent.startPerturbation | Tangent.startPerturbation = suc zero
... | Tangent.startPerturbation | Tangent.nextPerturbation = zero
... | Tangent.startPerturbation | Tangent.zeroPerturbation = zero
... | Tangent.nextPerturbation | Tangent.startPerturbation = zero
... | Tangent.nextPerturbation | Tangent.nextPerturbation = suc zero
... | Tangent.nextPerturbation | Tangent.zeroPerturbation = zero
... | Tangent.zeroPerturbation | Tangent.startPerturbation = zero
... | Tangent.zeroPerturbation | Tangent.nextPerturbation = zero
... | Tangent.zeroPerturbation | Tangent.zeroPerturbation = suc zero

record ShiftFiniteLocalOPECrossing : Setω where
  field
    Operator : Set
    Site : Set
    insertion : Site → Operator → LocalInsertion
    coefficient : Operator → Operator → Operator → Set
    selectedCoefficient : Operator → Operator → Operator → Nat
    product : Operator → Operator → Operator

    canonicalCoefficient :
      (p q : Operator) →
      coefficient p q (product p q)

    locality :
      (p q : Operator) →
      product p q ≡ product q p

    crossing :
      (p q r : Operator) →
      product (product p q) r ≡ product p (product q r)

    nonClaimBoundary : List String

open ShiftFiniteLocalOPECrossing public

canonicalShiftFiniteLocalOPECrossing : ShiftFiniteLocalOPECrossing
canonicalShiftFiniteLocalOPECrossing =
  record
    { Operator = Tangent.ShiftFinitePerturbation
    ; Site = InsertionSite
    ; insertion = insert
    ; coefficient = OPECoefficient
    ; selectedCoefficient = finiteOPESelectionValue
    ; product = Finite._⊗p_
    ; canonicalCoefficient = canonicalOPECoefficient
    ; locality = fusionCommutative
    ; crossing = crossingAssociativity
    ; nonClaimBoundary =
        "ShiftFiniteLocalOPECrossing is an exact finite algebraic OPE surface"
        ∷ "OPECoefficient is proof-relevant equality with the existing finite fusion output"
        ∷ "selectedCoefficient is the exact finite 0/1 selection table"
        ∷ "locality is finite exchange symmetry and crossing is finite associativity"
        ∷ "No singular position dependence, analytic OPE coefficient, conformal block, continuum locality, or QFT reconstruction is claimed"
        ∷ []
    }
