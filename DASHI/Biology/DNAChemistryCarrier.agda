module DASHI.Biology.DNAChemistryCarrier where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Chemistry-native DNA carrier.
--
-- This module records the exact finite base carrier and the algebraic
-- complement / reverse-complement actions used by later 4-adic lift modules.
-- It does not claim that the UV projection is a complete microscopic quantum
-- chemistry model.  UV is an exact bijective coordinate chart on the four
-- bases; thermodynamic authority remains in later explicitly bounded bridges.

------------------------------------------------------------------------
-- Base carrier and complement involution.

data DNABase : Set where
  A : DNABase
  C : DNABase
  G : DNABase
  T : DNABase

baseName : DNABase → String
baseName A = "A"
baseName C = "C"
baseName G = "G"
baseName T = "T"

complement : DNABase → DNABase
complement A = T
complement T = A
complement C = G
complement G = C

complement-involutive :
  ∀ b → complement (complement b) ≡ b
complement-involutive A = refl
complement-involutive C = refl
complement-involutive G = refl
complement-involutive T = refl

reverse :
  List DNABase →
  List DNABase
reverse [] = []
reverse (b ∷ bs) = append (reverse bs) (b ∷ [])
  where
  append : List DNABase → List DNABase → List DNABase
  append [] ys = ys
  append (x ∷ xs) ys = x ∷ append xs ys

mapComplement :
  List DNABase →
  List DNABase
mapComplement [] = []
mapComplement (b ∷ bs) = complement b ∷ mapComplement bs

reverseComplement :
  List DNABase →
  List DNABase
reverseComplement xs = mapComplement (reverse xs)

------------------------------------------------------------------------
-- Exact UV chart.
--
-- U records GC/AT strength class.
-- V records purine/pyrimidine class.
-- Together the pair distinguishes all four bases exactly.

data SignedAxis : Set where
  axisNegative : SignedAxis
  axisPositive : SignedAxis

record UVCoordinate : Set where
  constructor uv
  field
    U : SignedAxis
    V : SignedAxis

open UVCoordinate public

toUV : DNABase → UVCoordinate
toUV A = uv axisNegative axisPositive
toUV C = uv axisPositive axisNegative
toUV G = uv axisPositive axisPositive
toUV T = uv axisNegative axisNegative

fromUV : UVCoordinate → DNABase
fromUV (uv axisNegative axisPositive) = A
fromUV (uv axisPositive axisNegative) = C
fromUV (uv axisPositive axisPositive) = G
fromUV (uv axisNegative axisNegative) = T

fromUV-toUV :
  ∀ b → fromUV (toUV b) ≡ b
fromUV-toUV A = refl
fromUV-toUV C = refl
fromUV-toUV G = refl
fromUV-toUV T = refl

toUV-fromUV :
  ∀ q → toUV (fromUV q) ≡ q
toUV-fromUV (uv axisNegative axisNegative) = refl
toUV-fromUV (uv axisNegative axisPositive) = refl
toUV-fromUV (uv axisPositive axisNegative) = refl
toUV-fromUV (uv axisPositive axisPositive) = refl

flipAxis : SignedAxis → SignedAxis
flipAxis axisNegative = axisPositive
flipAxis axisPositive = axisNegative

complementUV : UVCoordinate → UVCoordinate
complementUV (uv u v) = uv u (flipAxis v)

complement-UV-equivariant :
  ∀ b → toUV (complement b) ≡ complementUV (toUV b)
complement-UV-equivariant A = refl
complement-UV-equivariant C = refl
complement-UV-equivariant G = refl
complement-UV-equivariant T = refl

------------------------------------------------------------------------
-- Scope receipt.

record DNAChemistryCarrierReceipt : Set where
  constructor mkDNAChemistryCarrierReceipt
  field
    alphabetIsCAGT : Bool
    complementIsTyped : Bool
    complementIsInvolutive : Bool
    uvChartIsExact : Bool
    uvIsCompleteQuantumChemistry : Bool
    carrierBoundaryHolds : Bool
    carrierBoundaryHoldsIsTrue : carrierBoundaryHolds ≡ true

open DNAChemistryCarrierReceipt public

canonicalDNAChemistryCarrierReceipt : DNAChemistryCarrierReceipt
canonicalDNAChemistryCarrierReceipt =
  mkDNAChemistryCarrierReceipt
    true
    true
    true
    true
    false
    true
    refl
