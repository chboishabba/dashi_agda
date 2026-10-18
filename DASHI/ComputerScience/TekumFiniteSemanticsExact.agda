module DASHI.ComputerScience.TekumFiniteSemanticsExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor

------------------------------------------------------------------------
-- Exact finite semantics surface.
--
-- Ordinary Tekum values are represented by exact symbolic data
--   s * (1+f) * 3^e
-- rather than by an ambient machine Float.  The rational interpretation of f
-- and the ordered-real embedding can be supplied by independent consumers.

data IntCode : Set where
  nonnegative : Nat → IntCode
  negative : Nat → IntCode

negateIntCode : IntCode → IntCode
negateIntCode (nonnegative zero) = nonnegative zero
negateIntCode (nonnegative (suc n)) = negative (suc n)
negateIntCode (negative n) = nonnegative n

data SpecialValue : Set where
  naR : SpecialValue
  zeroValue : SpecialValue
  infinity : SpecialValue

record OrdinaryTekum : Set where
  constructor ordinaryTekum
  field
    sign : Anchor.TekumSign
    exponent : IntCode
    fractionNumerator : IntCode
    fractionTritCount : Nat
open OrdinaryTekum public

data TekumValue : Set where
  special : SpecialValue → TekumValue
  ordinary : OrdinaryTekum → TekumValue

negateTekumValue : TekumValue → TekumValue
negateTekumValue (special naR) = special naR
negateTekumValue (special zeroValue) = special zeroValue
negateTekumValue (special infinity) = special infinity
negateTekumValue (ordinary (ordinaryTekum s e f p)) =
  ordinary (ordinaryTekum (Anchor.flipSign s) e f p)

record TekumSemanticBoundary : Set where
  constructor tekumSemanticBoundary
  field
    ordinaryValuesUseExactSymbolicPowerOfThree : Bool
    machineFloatIsNotSemanticAuthority : Bool
    naRAndInfinityRemainTypeDistinct : Bool
    nativeNegationChangesOnlyExternalSignForOrdinaryValues : Bool

canonicalTekumSemanticBoundary : TekumSemanticBoundary
canonicalTekumSemanticBoundary =
  tekumSemanticBoundary true true true true
