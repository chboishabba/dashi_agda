module DASHI.Biology.IITTernaryAffineMinimalSufficiencyExact where

------------------------------------------------------------------------
-- TERNARY AFFINE MINIMAL-SUFFICIENCY CLASSIFICATION
--
-- Numerical companion: every affine law
--   mu(a,b)=c+alpha*a+beta*b mod 3
-- with alpha,beta nonzero has the same all-state-positive 2023 system-phi
-- profile log2(9) on A'=C, B'=A, C'=mu(A,B).
--
-- Structural explanation: in an affine F3 law, fixing either input leaves a
-- permutation of F3 exactly when the corresponding coefficient is nonzero.
-- Thus the 12 genuinely two-input affine laws are exactly the bipermutative
-- affine family.  Characteristic three splits that family into six symmetric
-- parity laws and six antisymmetric difference/orientation laws.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_)

data F3Coeff : Set where
  c0 c1 c2 : F3Coeff

negCoeff : F3Coeff → F3Coeff
negCoeff c0 = c0
negCoeff c1 = c2
negCoeff c2 = c1

negCoeffInvolutive : (x : F3Coeff) → negCoeff (negCoeff x) ≡ x
negCoeffInvolutive c0 = refl
negCoeffInvolutive c1 = refl
negCoeffInvolutive c2 = refl

data NonzeroCoeff : F3Coeff → Set where
  nz1 : NonzeroCoeff c1
  nz2 : NonzeroCoeff c2

record AffineF3Gate : Set where
  constructor affine-f3-gate
  field
    offset : F3Coeff
    leftCoeff : F3Coeff
    rightCoeff : F3Coeff

open AffineF3Gate public

EssentialTwoInput : AffineF3Gate → Set
EssentialTwoInput gate =
  NonzeroCoeff (leftCoeff gate) × NonzeroCoeff (rightCoeff gate)

------------------------------------------------------------------------
-- Bipermutativity is proof-relevant here: a witness carries the nonzero
-- coefficient proof for each input coordinate.  Within the affine family this
-- is exactly the condition that every one-input slice is a permutation of F3.
------------------------------------------------------------------------

record AffineBipermutative (gate : AffineF3Gate) : Set where
  constructor affine-bipermutative
  field
    leftPermutationCoefficient : NonzeroCoeff (leftCoeff gate)
    rightPermutationCoefficient : NonzeroCoeff (rightCoeff gate)

open AffineBipermutative public

essentialImpliesBipermutative :
  (gate : AffineF3Gate) →
  EssentialTwoInput gate →
  AffineBipermutative gate
essentialImpliesBipermutative gate (leftNZ , rightNZ) =
  affine-bipermutative leftNZ rightNZ

bipermutativeImpliesEssential :
  (gate : AffineF3Gate) →
  AffineBipermutative gate →
  EssentialTwoInput gate
bipermutativeImpliesEssential gate witness =
  leftPermutationCoefficient witness , rightPermutationCoefficient witness

------------------------------------------------------------------------
-- Four nonzero coefficient pairs, split into symmetric and antisymmetric
-- channels; each has three offsets, so 6+6=12 laws.
------------------------------------------------------------------------

data AffineChannel : AffineF3Gate → Set where
  symmetric11 : (c : F3Coeff) → AffineChannel (affine-f3-gate c c1 c1)
  symmetric22 : (c : F3Coeff) → AffineChannel (affine-f3-gate c c2 c2)
  antisymmetric12 : (c : F3Coeff) → AffineChannel (affine-f3-gate c c1 c2)
  antisymmetric21 : (c : F3Coeff) → AffineChannel (affine-f3-gate c c2 c1)

data SymmetricAffine : AffineF3Gate → Set where
  sym11 : (c : F3Coeff) → SymmetricAffine (affine-f3-gate c c1 c1)
  sym22 : (c : F3Coeff) → SymmetricAffine (affine-f3-gate c c2 c2)

data AntisymmetricAffine : AffineF3Gate → Set where
  anti12 : (c : F3Coeff) → AntisymmetricAffine (affine-f3-gate c c1 c2)
  anti21 : (c : F3Coeff) → AntisymmetricAffine (affine-f3-gate c c2 c1)

essentialAffineClassified :
  (gate : AffineF3Gate) →
  EssentialTwoInput gate →
  AffineChannel gate
essentialAffineClassified (affine-f3-gate c c0 b) (() , _)
essentialAffineClassified (affine-f3-gate c c1 c0) (_ , ())
essentialAffineClassified (affine-f3-gate c c1 c1) (_ , _) = symmetric11 c
essentialAffineClassified (affine-f3-gate c c1 c2) (_ , _) = antisymmetric12 c
essentialAffineClassified (affine-f3-gate c c2 c0) (_ , ())
essentialAffineClassified (affine-f3-gate c c2 c1) (_ , _) = antisymmetric21 c
essentialAffineClassified (affine-f3-gate c c2 c2) (_ , _) = symmetric22 c

channelIsSymmetricOrAntisymmetric :
  (gate : AffineF3Gate) →
  AffineChannel gate →
  SymmetricAffine gate ⊎ AntisymmetricAffine gate
channelIsSymmetricOrAntisymmetric .(affine-f3-gate c c1 c1) (symmetric11 c) = inj₁ (sym11 c)
channelIsSymmetricOrAntisymmetric .(affine-f3-gate c c2 c2) (symmetric22 c) = inj₁ (sym22 c)
channelIsSymmetricOrAntisymmetric .(affine-f3-gate c c1 c2) (antisymmetric12 c) = inj₂ (anti12 c)
channelIsSymmetricOrAntisymmetric .(affine-f3-gate c c2 c1) (antisymmetric21 c) = inj₂ (anti21 c)

essentialAffineIsParityOrDifference :
  (gate : AffineF3Gate) →
  EssentialTwoInput gate →
  SymmetricAffine gate ⊎ AntisymmetricAffine gate
essentialAffineIsParityOrDifference gate essential =
  channelIsSymmetricOrAntisymmetric gate (essentialAffineClassified gate essential)

bipermutativeAffineIsParityOrDifference :
  (gate : AffineF3Gate) →
  AffineBipermutative gate →
  SymmetricAffine gate ⊎ AntisymmetricAffine gate
bipermutativeAffineIsParityOrDifference gate witness =
  essentialAffineIsParityOrDifference gate
    (bipermutativeImpliesEssential gate witness)

triSumGate : AffineF3Gate
triSumGate = affine-f3-gate c0 c1 c1

triDifferenceGate : AffineF3Gate
triDifferenceGate = affine-f3-gate c0 c1 c2

triSumIsSymmetric : SymmetricAffine triSumGate
triSumIsSymmetric = sym11 c0

triDifferenceIsAntisymmetric : AntisymmetricAffine triDifferenceGate
triDifferenceIsAntisymmetric = anti12 c0

triSumIsBipermutative : AffineBipermutative triSumGate
triSumIsBipermutative = affine-bipermutative nz1 nz1

triDifferenceIsBipermutative : AffineBipermutative triDifferenceGate
triDifferenceIsBipermutative = affine-bipermutative nz1 nz2

record TernaryAffineMinimalSufficiencyBoundary : Set where
  constructor ternary-affine-minimal-sufficiency-boundary
  field
    affineFamilyHasTwentySevenParameterChoices : Bool
    essentialAffineFamilyHasTwelveChoices : Bool
    essentialAffineFamilyIsExactlyBipermutative : Bool
    essentialFamilySplitsSixSymmetricSixAntisymmetric : Bool
    symmetricChannelIsPhysicalTorque : Bool
    antisymmetricChannelIsPhysicalTorqueMagnitude : Bool
    numericalAllStatePhiReceiptRequiredSeparately : Bool
    currentIIT2026PositivePhiManufacturedHere : Bool

canonicalTernaryAffineMinimalSufficiencyBoundary :
  TernaryAffineMinimalSufficiencyBoundary
canonicalTernaryAffineMinimalSufficiencyBoundary =
  ternary-affine-minimal-sufficiency-boundary
    true true true true false false true false
