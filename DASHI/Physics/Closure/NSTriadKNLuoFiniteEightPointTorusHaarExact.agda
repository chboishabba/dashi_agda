module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointTorusHaarExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Audrey Terras.
-- Title: "Fourier Analysis on Finite Groups and Applications".
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Construct an actual normalized Haar/Fourier model, rather than another
-- record of assumed integral laws.  The carrier is the finite quotient torus
--
--   (Z/2Z)^3,
--
-- equipped with its eight-point normalized Haar average.  The real characters
-- are derived from the parity pairing.  Character multiplication, zero-mode
-- normalization, translation invariance, character orthogonality and the
-- Fourier transform of a constant are all proved by exact rational algebra.
--
-- This is a concrete finite torus approximation.  It validates the selected
-- normalization and algebra, but it is not the continuum Haar/Bochner
-- realization on T^3.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record BitTorus3 : Set where
  constructor bit3
  field
    x y z : Bool

open BitTorus3 public

xor : Bool → Bool → Bool
xor false right = right
xor true false = true
xor true true = false

addPoint : BitTorus3 → BitTorus3 → BitTorus3
addPoint (bit3 ax ay az) (bit3 bx by bz) =
  bit3 (xor ax bx) (xor ay by) (xor az bz)

zeroMode : BitTorus3
zeroMode = bit3 false false false

bitCharacter : Bool → Bool → ℚ
bitCharacter false point = 1ℚ
bitCharacter true false = 1ℚ
bitCharacter true true = - 1ℚ

character : BitTorus3 → BitTorus3 → ℚ
character (bit3 kx ky kz) (bit3 px py pz) =
  bitCharacter kx px * bitCharacter ky py * bitCharacter kz pz

bitCharacterAdd :
  (left right point : Bool) →
  bitCharacter (xor left right) point
  ≡ bitCharacter left point * bitCharacter right point
bitCharacterAdd false false false = refl
bitCharacterAdd false false true = refl
bitCharacterAdd false true false = refl
bitCharacterAdd false true true = refl
bitCharacterAdd true false false = refl
bitCharacterAdd true false true = refl
bitCharacterAdd true true false = refl
bitCharacterAdd true true true = refl

characterAdd :
  (left right point : BitTorus3) →
  character (addPoint left right) point
  ≡ character left point * character right point
characterAdd
  (bit3 lx ly lz)
  (bit3 rx ry rz)
  (bit3 px py pz)
  rewrite bitCharacterAdd lx rx px
        | bitCharacterAdd ly ry py
        | bitCharacterAdd lz rz pz =
  solve
    ( bitCharacter lx px
    ∷ bitCharacter rx px
    ∷ bitCharacter ly py
    ∷ bitCharacter ry py
    ∷ bitCharacter lz pz
    ∷ bitCharacter rz pz
    ∷ []
    )

characterZero :
  (point : BitTorus3) →
  character zeroMode point ≡ 1ℚ
characterZero (bit3 px py pz) = refl

p000 p001 p010 p011 p100 p101 p110 p111 : BitTorus3
p000 = bit3 false false false
p001 = bit3 false false true
p010 = bit3 false true false
p011 = bit3 false true true
p100 = bit3 true false false
p101 = bit3 true false true
p110 = bit3 true true false
p111 = bit3 true true true

sumEight : (BitTorus3 → ℚ) → ℚ
sumEight value =
  value p000 + value p001 + value p010 + value p011
  + value p100 + value p101 + value p110 + value p111

oneEighth : ℚ
oneEighth = Int.+ 1 / 8

haarAverage : (BitTorus3 → ℚ) → ℚ
haarAverage value = oneEighth * sumEight value

haarMassOne :
  haarAverage (λ point → 1ℚ) ≡ 1ℚ
haarMassOne = solve []

zeroModeIndicator : BitTorus3 → ℚ
zeroModeIndicator (bit3 false false false) = 1ℚ
zeroModeIndicator (bit3 false false true) = 0ℚ
zeroModeIndicator (bit3 false true false) = 0ℚ
zeroModeIndicator (bit3 false true true) = 0ℚ
zeroModeIndicator (bit3 true false false) = 0ℚ
zeroModeIndicator (bit3 true false true) = 0ℚ
zeroModeIndicator (bit3 true true false) = 0ℚ
zeroModeIndicator (bit3 true true true) = 0ℚ

haarCharacterOrthogonality :
  (mode : BitTorus3) →
  haarAverage (character mode) ≡ zeroModeIndicator mode
haarCharacterOrthogonality (bit3 false false false) = solve []
haarCharacterOrthogonality (bit3 false false true) = solve []
haarCharacterOrthogonality (bit3 false true false) = solve []
haarCharacterOrthogonality (bit3 false true true) = solve []
haarCharacterOrthogonality (bit3 true false false) = solve []
haarCharacterOrthogonality (bit3 true false true) = solve []
haarCharacterOrthogonality (bit3 true true false) = solve []
haarCharacterOrthogonality (bit3 true true true) = solve []

translationInvariant :
  (value : BitTorus3 → ℚ) →
  (shift : BitTorus3) →
  haarAverage (λ point → value (addPoint point shift))
  ≡ haarAverage value
translationInvariant value (bit3 false false false) = solve []
translationInvariant value (bit3 false false true) =
  solve
    ( value p000 ∷ value p001 ∷ value p010 ∷ value p011
    ∷ value p100 ∷ value p101 ∷ value p110 ∷ value p111 ∷ [] )
translationInvariant value (bit3 false true false) =
  solve
    ( value p000 ∷ value p001 ∷ value p010 ∷ value p011
    ∷ value p100 ∷ value p101 ∷ value p110 ∷ value p111 ∷ [] )
translationInvariant value (bit3 false true true) =
  solve
    ( value p000 ∷ value p001 ∷ value p010 ∷ value p011
    ∷ value p100 ∷ value p101 ∷ value p110 ∷ value p111 ∷ [] )
translationInvariant value (bit3 true false false) =
  solve
    ( value p000 ∷ value p001 ∷ value p010 ∷ value p011
    ∷ value p100 ∷ value p101 ∷ value p110 ∷ value p111 ∷ [] )
translationInvariant value (bit3 true false true) =
  solve
    ( value p000 ∷ value p001 ∷ value p010 ∷ value p011
    ∷ value p100 ∷ value p101 ∷ value p110 ∷ value p111 ∷ [] )
translationInvariant value (bit3 true true false) =
  solve
    ( value p000 ∷ value p001 ∷ value p010 ∷ value p011
    ∷ value p100 ∷ value p101 ∷ value p110 ∷ value p111 ∷ [] )
translationInvariant value (bit3 true true true) =
  solve
    ( value p000 ∷ value p001 ∷ value p010 ∷ value p011
    ∷ value p100 ∷ value p101 ∷ value p110 ∷ value p111 ∷ [] )

fourierCoefficient :
  (BitTorus3 → ℚ) → BitTorus3 → ℚ
fourierCoefficient value mode =
  haarAverage (λ point → value point * character mode point)

fourierCoefficientOfConstant :
  (constant : ℚ) →
  (mode : BitTorus3) →
  fourierCoefficient (λ point → constant) mode
  ≡ constant * zeroModeIndicator mode
fourierCoefficientOfConstant constant (bit3 false false false) =
  solve (constant ∷ [])
fourierCoefficientOfConstant constant (bit3 false false true) =
  solve (constant ∷ [])
fourierCoefficientOfConstant constant (bit3 false true false) =
  solve (constant ∷ [])
fourierCoefficientOfConstant constant (bit3 false true true) =
  solve (constant ∷ [])
fourierCoefficientOfConstant constant (bit3 true false false) =
  solve (constant ∷ [])
fourierCoefficientOfConstant constant (bit3 true false true) =
  solve (constant ∷ [])
fourierCoefficientOfConstant constant (bit3 true true false) =
  solve (constant ∷ [])
fourierCoefficientOfConstant constant (bit3 true true true) =
  solve (constant ∷ [])
