module DASHI.Biology.IITTernaryAffineMinimalSufficiencyExact where

------------------------------------------------------------------------
-- TERNARY AFFINE MINIMAL-SUFFICIENCY CLASSIFICATION
--
-- The numerical companion scans every affine two-input law
--
--   mu(a,b) = c + alpha*a + beta*b  (mod 3)
--
-- on the fixed recurrent fabric A'=C, B'=A, C'=mu(A,B).  It reports that all
-- 12 laws with alpha,beta nonzero have the same all-state-positive 2023
-- system-phi profile log2(9).  This owner pays the finite algebraic
-- classification independently of that numerical IIT receipt.
--
-- In F3 there are exactly four nonzero coefficient pairs.  They split into:
--   symmetric parity channel     alpha = beta     : (1,1), (2,2)
--   antisymmetric difference     beta = -alpha   : (1,2), (2,1)
-- and each admits three output offsets c, giving 6 + 6 = 12 essential affine
-- laws.  Thus characteristic three separates the parity channel from the
-- orientation/handedness channel that collapses in characteristic two.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- 1. Three exact coefficients.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- 2. The complete 27-law affine family is 3 offsets x 3 x 3 coefficients.
------------------------------------------------------------------------

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
-- 3. The two structural channels.
------------------------------------------------------------------------

data AffineChannel : AffineF3Gate → Set where
  symmetric11 :
    (c : F3Coeff) →
    AffineChannel (affine-f3-gate c c1 c1)
  symmetric22 :
    (c : F3Coeff) →
    AffineChannel (affine-f3-gate c c2 c2)
  antisymmetric12 :
    (c : F3Coeff) →
    AffineChannel (affine-f3-gate c c1 c2)
  antisymmetric21 :
    (c : F3Coeff) →
    AffineChannel (affine-f3-gate c c2 c1)

data SymmetricAffine : AffineF3Gate → Set where
  sym11 : (c : F3Coeff) → SymmetricAffine (affine-f3-gate c c1 c1)
  sym22 : (c : F3Coeff) → SymmetricAffine (affine-f3-gate c c2 c2)

data AntisymmetricAffine : AffineF3Gate → Set where
  anti12 : (c : F3Coeff) → AntisymmetricAffine (affine-f3-gate c c1 c2)
  anti21 : (c : F3Coeff) → AntisymmetricAffine (affine-f3-gate c c2 c1)

------------------------------------------------------------------------
-- 4. Every genuinely two-input affine F3 law belongs to one of the four
-- coefficient families, hence to symmetric parity or antisymmetric difference.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- 5. Canonical zero-offset representatives.
------------------------------------------------------------------------

triSumGate : AffineF3Gate
triSumGate = affine-f3-gate c0 c1 c1

triDifferenceGate : AffineF3Gate
triDifferenceGate = affine-f3-gate c0 c1 c2

triSumIsSymmetric : SymmetricAffine triSumGate
triSumIsSymmetric = sym11 c0

triDifferenceIsAntisymmetric : AntisymmetricAffine triDifferenceGate
triDifferenceIsAntisymmetric = anti12 c0

------------------------------------------------------------------------
-- 6. Authority boundary.
------------------------------------------------------------------------

record TernaryAffineMinimalSufficiencyBoundary : Set where
  constructor ternary-affine-minimal-sufficiency-boundary
  field
    affineFamilyHasTwentySevenParameterChoices : Bool
    essentialAffineFamilyHasTwelveChoices : Bool
    essentialFamilySplitsSixSymmetricSixAntisymmetric : Bool
    symmetricChannelIsPhysicalTorque : Bool
    antisymmetricChannelIsPhysicalTorqueMagnitude : Bool
    numericalAllStatePhiReceiptRequiredSeparately : Bool
    currentIIT2026PositivePhiManufacturedHere : Bool

canonicalTernaryAffineMinimalSufficiencyBoundary :
  TernaryAffineMinimalSufficiencyBoundary
canonicalTernaryAffineMinimalSufficiencyBoundary =
  ternary-affine-minimal-sufficiency-boundary
    true true true false false true false
