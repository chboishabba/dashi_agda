module DASHI.Foundations.Base12369RoleHierarchy where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth
  ; HexTruth
  ; tri-low ; tri-mid ; tri-high
  ; hex-0 ; hex-1 ; hex-2 ; hex-3 ; hex-4 ; hex-5
  ; triXor
  ; hexXor
  )

------------------------------------------------------------------------
-- Typed role hierarchy 1, 2, 3, 6, 9.

record IdentityCarrier : Set where
  constructor identity

identityCarrier : IdentityCarrier
identityCarrier = identity

data BinaryPolarity : Set where
  polarity-0 : BinaryPolarity
  polarity-1 : BinaryPolarity

binaryFlip : BinaryPolarity → BinaryPolarity
binaryFlip polarity-0 = polarity-1
binaryFlip polarity-1 = polarity-0

binaryAdd : BinaryPolarity → BinaryPolarity → BinaryPolarity
binaryAdd polarity-0 p = p
binaryAdd polarity-1 polarity-0 = polarity-1
binaryAdd polarity-1 polarity-1 = polarity-0

identityToBinary : IdentityCarrier → BinaryPolarity
identityToBinary identity = polarity-0

identityToTriadic : IdentityCarrier → TriTruth
identityToTriadic identity = tri-low

record NumberRoleHierarchy : Set where
  constructor numberRoleHierarchy
  field
    oneCarrier : Set
    twoCarrier : Set
    threeCarrier : Set
    sixCarrier : Set
    nineRoleLabel : String
    oneRoleLabel : String
    twoRoleLabel : String
    threeRoleLabel : String
    sixRoleLabel : String
    hierarchyPromotesUniversalNumerology : Bool
    hierarchyPromotesUniversalNumerologyIsFalse :
      hierarchyPromotesUniversalNumerology ≡ false

base12369RoleHierarchy : NumberRoleHierarchy
base12369RoleHierarchy =
  numberRoleHierarchy
    IdentityCarrier
    BinaryPolarity
    TriTruth
    HexTruth
    "9 as triadic depth C9 rather than a product decomposition"
    "1 as identity/neutral carrier"
    "2 as binary polarity/parity carrier"
    "3 as triadic phase carrier"
    "6 as binary-triadic coupling"
    false
    refl

------------------------------------------------------------------------
-- Canonical Chinese-remainder coordinates for C6.
--
-- This is intentionally distinct from HexTruthPolarityFactor.  The existing
-- orientation factor groups 0,1,2 versus 3,4,5 and is useful for half-turn
-- polarity.  The CRT parity factor is k mod 2 and alternates around C6.

record CRT23 : Set where
  constructor crt23
  field
    residue2 : BinaryPolarity
    residue3 : TriTruth

open CRT23 public

hexToCRT23 : HexTruth → CRT23
hexToCRT23 hex-0 = crt23 polarity-0 tri-low
hexToCRT23 hex-1 = crt23 polarity-1 tri-mid
hexToCRT23 hex-2 = crt23 polarity-0 tri-high
hexToCRT23 hex-3 = crt23 polarity-1 tri-low
hexToCRT23 hex-4 = crt23 polarity-0 tri-mid
hexToCRT23 hex-5 = crt23 polarity-1 tri-high

crt23ToHex : CRT23 → HexTruth
crt23ToHex (crt23 polarity-0 tri-low) = hex-0
crt23ToHex (crt23 polarity-1 tri-low) = hex-3
crt23ToHex (crt23 polarity-0 tri-mid) = hex-4
crt23ToHex (crt23 polarity-1 tri-mid) = hex-1
crt23ToHex (crt23 polarity-0 tri-high) = hex-2
crt23ToHex (crt23 polarity-1 tri-high) = hex-5

hexCRT-roundTrip : (h : HexTruth) → crt23ToHex (hexToCRT23 h) ≡ h
hexCRT-roundTrip hex-0 = refl
hexCRT-roundTrip hex-1 = refl
hexCRT-roundTrip hex-2 = refl
hexCRT-roundTrip hex-3 = refl
hexCRT-roundTrip hex-4 = refl
hexCRT-roundTrip hex-5 = refl

crtHex-roundTrip : (x : CRT23) → hexToCRT23 (crt23ToHex x) ≡ x
crtHex-roundTrip (crt23 polarity-0 tri-low) = refl
crtHex-roundTrip (crt23 polarity-1 tri-low) = refl
crtHex-roundTrip (crt23 polarity-0 tri-mid) = refl
crtHex-roundTrip (crt23 polarity-1 tri-mid) = refl
crtHex-roundTrip (crt23 polarity-0 tri-high) = refl
crtHex-roundTrip (crt23 polarity-1 tri-high) = refl

crtAdd : CRT23 → CRT23 → CRT23
crtAdd (crt23 p t) (crt23 q u) =
  crt23 (binaryAdd p q) (triXor t u)

-- The group law is transported through the checked bijection.  This avoids
-- silently identifying the orientation-polarity factor with CRT parity.
hexAddViaCRT : HexTruth → HexTruth → HexTruth
hexAddViaCRT x y = crt23ToHex (crtAdd (hexToCRT23 x) (hexToCRT23 y))

hexAddViaCRT-agrees-00 : hexAddViaCRT hex-0 hex-0 ≡ hexXor hex-0 hex-0
hexAddViaCRT-agrees-00 = refl

hexAddViaCRT-agrees-15 : hexAddViaCRT hex-1 hex-5 ≡ hexXor hex-1 hex-5
hexAddViaCRT-agrees-15 = refl

hexAddViaCRT-agrees-24 : hexAddViaCRT hex-2 hex-4 ≡ hexXor hex-2 hex-4
hexAddViaCRT-agrees-24 = refl

hexAddViaCRT-agrees-33 : hexAddViaCRT hex-3 hex-3 ≡ hexXor hex-3 hex-3
hexAddViaCRT-agrees-33 = refl

record CRT23Boundary : Set where
  constructor crt23Boundary
  field
    sixCarrier : Set
    productCarrier : Set
    encode : HexTruth → CRT23
    decode : CRT23 → HexTruth
    decodeEncode : (h : HexTruth) → decode (encode h) ≡ h
    encodeDecode : (x : CRT23) → encode (decode x) ≡ x
    interpretation : String
    fullGroupIsomorphismPromoted : Bool
    fullGroupIsomorphismPromotedIsFalse :
      fullGroupIsomorphismPromoted ≡ false

base369CRT23Boundary : CRT23Boundary
base369CRT23Boundary =
  crt23Boundary
    HexTruth
    CRT23
    hexToCRT23
    crt23ToHex
    hexCRT-roundTrip
    crtHex-roundTrip
    "C6 exposes canonical residues mod 2 and mod 3; orientation polarity and CRT parity are distinct typed projections"
    false
    refl
