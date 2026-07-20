module Ontology.DNA.ChemistryTernaryQuantizer where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Vec using (Vec; map)

open import Ontology.DNA.ChemistrySheetHamiltonian using
  (Signed; neg; zer; pos; SheetCoordinates; sheetCoordinates)

------------------------------------------------------------------------
-- The current signed chemistry coordinates already have the balanced ternary
-- carrier.  Quantisation is therefore exact on this discrete image.  This does
-- not prove that an arbitrary future real-valued sheet tower quantises without
-- loss; that promotion remains indexed by an explicit distortion certificate.

data Trit : Set where
  minus neutral plus : Trit

quantizeSigned : Signed → Trit
quantizeSigned neg = minus
quantizeSigned zer = neutral
quantizeSigned pos = plus

reconstructSigned : Trit → Signed
reconstructSigned minus = neg
reconstructSigned neutral = zer
reconstructSigned plus = pos

signed-roundtrip : ∀ s → reconstructSigned (quantizeSigned s) ≡ s
signed-roundtrip neg = refl
signed-roundtrip zer = refl
signed-roundtrip pos = refl

record TernarySheet (n : Nat) : Set where
  constructor ternarySheet
  field
    uTrits : Vec Trit n
    vTrits : Vec Trit n

quantizeSheet : ∀ {n} → SheetCoordinates n → TernarySheet n
quantizeSheet (sheetCoordinates u v) =
  ternarySheet (map quantizeSigned u) (map quantizeSigned v)

reconstructSheet : ∀ {n} → TernarySheet n → SheetCoordinates n
reconstructSheet (ternarySheet u v) =
  sheetCoordinates (map reconstructSigned u) (map reconstructSigned v)

record QuantizerDistortionCertificate (Coefficient : Set) : Set₁ where
  field
    quantize : Coefficient → Trit
    reconstruct : Trit → Coefficient
    Distortion : Set
    distortion : Coefficient → Distortion
    chemistryBound : Set

record TernaryMinimalityHypotheses (Alphabet : Set) : Set₁ where
  field
    negative : Alphabet
    neutral : Alphabet
    positive : Alphabet
    signDistinct : Set
    neutralDistinct : Set

record ConditionalTernaryMinimality : Set₁ where
  field
    threeSignedBasinsRequired : Set
    twoSymbolsInsufficient : Set
    ternarySufficient : Set

record ExactSignedTernaryReceipt : Set where
  field
    distortion : Nat
    distortion-zero : distortion ≡ zero

exactSignedTernaryReceipt : ExactSignedTernaryReceipt
exactSignedTernaryReceipt = record
  { distortion = zero
  ; distortion-zero = refl
  }
