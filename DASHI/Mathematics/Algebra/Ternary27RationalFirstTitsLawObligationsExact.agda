module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsLawObligationsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set₁)

open import DASHI.Core.Q using (ℚ; _*ℚ_; oneℚ)
import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCarrierExact as R

------------------------------------------------------------------------
-- PROOF-RELEVANT LAW SURFACE FOR THE LITERAL RATIONAL FIRST-TITS CARRIER
------------------------------------------------------------------------

LeftAdditive : Set
LeftAdditive =
  ∀ X Y Z →
  R.firstTitsJordanProduct (R.addJ X Y) Z
  ≡ R.addJ (R.firstTitsJordanProduct X Z) (R.firstTitsJordanProduct Y Z)

RightAdditive : Set
RightAdditive =
  ∀ X Y Z →
  R.firstTitsJordanProduct X (R.addJ Y Z)
  ≡ R.addJ (R.firstTitsJordanProduct X Y) (R.firstTitsJordanProduct X Z)

LeftHomogeneous : Set
LeftHomogeneous =
  ∀ (q : ℚ) X Y →
  R.firstTitsJordanProduct (R.scaleJ q X) Y
  ≡ R.scaleJ q (R.firstTitsJordanProduct X Y)

RightHomogeneous : Set
RightHomogeneous =
  ∀ (q : ℚ) X Y →
  R.firstTitsJordanProduct X (R.scaleJ q Y)
  ≡ R.scaleJ q (R.firstTitsJordanProduct X Y)

Commutative : Set
Commutative =
  ∀ X Y → R.firstTitsJordanProduct X Y ≡ R.firstTitsJordanProduct Y X

LeftUnit : Set
LeftUnit =
  ∀ X → R.firstTitsJordanProduct R.unitJ X ≡ X

RightUnit : Set
RightUnit =
  ∀ X → R.firstTitsJordanProduct X R.unitJ ≡ X

squareJ : R.RationalFirstTits27 → R.RationalFirstTits27
squareJ X = R.firstTitsJordanProduct X X

JordanIdentity : Set
JordanIdentity =
  ∀ X Y →
  R.firstTitsJordanProduct
    (R.firstTitsJordanProduct (squareJ X) Y)
    X
  ≡
  R.firstTitsJordanProduct
    (squareJ X)
    (R.firstTitsJordanProduct Y X)

CubicUnit : Set
CubicUnit = R.firstTitsCubic R.unitJ ≡ oneℚ

CubicHomogeneous : Set
CubicHomogeneous =
  ∀ (q : ℚ) X →
  R.firstTitsCubic (R.scaleJ q X)
  ≡ (q *ℚ q *ℚ q) *ℚ R.firstTitsCubic X

record PaidRationalFirstTitsLaws : Set₁ where
  field
    leftAdditiveWitness : LeftAdditive
    rightAdditiveWitness : RightAdditive
    leftHomogeneousWitness : LeftHomogeneous
    rightHomogeneousWitness : RightHomogeneous
    commutativeWitness : Commutative
    leftUnitWitness : LeftUnit
    rightUnitWitness : RightUnit
    jordanIdentityWitness : JordanIdentity
    cubicUnitWitness : CubicUnit
    cubicHomogeneousWitness : CubicHomogeneous
open PaidRationalFirstTitsLaws public

record RationalFirstTitsLawBoundary : Set where
  constructor rational-first-tits-law-boundary
  field
    literalCarrierAvailable : Bool
    bilinearityPropositionsConcrete : Bool
    commutativityPropositionConcrete : Bool
    unitPropositionsConcrete : Bool
    jordanIdentityPropositionConcrete : Bool
    cubicPropositionsConcrete : Bool
    paidLawPackageTypeAvailable : Bool
    paidLawPackageInhabitedHere : Bool
open RationalFirstTitsLawBoundary public

canonicalBoundary : RationalFirstTitsLawBoundary
canonicalBoundary =
  rational-first-tits-law-boundary true true true true true true true false

data ExecutableChecksCreateLawPackage : Set where

executableChecksDoNotCreateLawPackage : ExecutableChecksCreateLawPackage → {A : Set} → A
executableChecksDoNotCreateLawPackage ()
