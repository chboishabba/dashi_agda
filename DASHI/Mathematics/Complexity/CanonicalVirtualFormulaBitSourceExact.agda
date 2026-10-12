module DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact where

------------------------------------------------------------------------
-- CANONICAL VIRTUAL BIT SOURCE FOR THE ACTUAL BINARY FORMULA CODE
--
-- This pays the semantic indexed-access obligation directly from the literal
-- recursive List Bool encoder.  It does NOT yet compile the lookup/construction
-- to a finite standard TM; that is now a strictly narrower downstream task.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as Clock
import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual

------------------------------------------------------------------------
-- Literal indexed lookup.
------------------------------------------------------------------------

lookupBit : Nat → List Bool → Maybe Bool
lookupBit zero [] = nothing
lookupBit zero (bit ∷ rest) = just bit
lookupBit (suc index) [] = nothing
lookupBit (suc index) (head ∷ rest) = lookupBit index rest

lookupBitSound :
  ∀ {index bits bit} →
  lookupBit index bits ≡ just bit →
  Virtual.BitAt index bits bit
lookupBitSound {zero} {[]} ()
lookupBitSound {zero} {bit ∷ rest} refl = Virtual.bitHere
lookupBitSound {suc index} {[]} ()
lookupBitSound {suc index} {head ∷ rest} proof =
  Virtual.bitThere (lookupBitSound proof)

lookupBitComplete :
  ∀ {index bits bit} →
  Virtual.BitAt index bits bit →
  lookupBit index bits ≡ just bit
lookupBitComplete Virtual.bitHere = refl
lookupBitComplete (Virtual.bitThere proof) =
  lookupBitComplete proof

------------------------------------------------------------------------
-- Honest semantic work charge: linear scan to the requested index.
------------------------------------------------------------------------

lookupWork : Nat → Nat
lookupWork index = suc index

one : Nat
one = suc zero

lookupWorkPolynomial :
  (formula : Cook.BooleanFormula) →
  (index : Nat) →
  lookupWork index
  ≤ Virtual.queryPolynomialBudget one one formula index
lookupWorkPolynomial formula index
  rewrite NatP.*-identityˡ
            (Clock.natPower
              (suc (Binary.formulaBitCodeLength formula + index)) one)
        | NatP.*-identityʳ
            (suc (Binary.formulaBitCodeLength formula + index)) =
  s≤s
    (NatP.m≤n+m
      index
      (Binary.formulaBitCodeLength formula))

canonicalVirtualFormulaBitSource :
  (formula : Cook.BooleanFormula) →
  Virtual.VirtualFormulaBitSource formula
canonicalVirtualFormulaBitSource formula = record
  { Virtual.readBit =
      λ index → lookupBit index (Binary.encodeFormulaBits formula)
  ; Virtual.readSound =
      lookupBitSound
  ; Virtual.readComplete =
      lookupBitComplete
  ; Virtual.queryWork =
      lookupWork
  ; Virtual.queryCoefficient =
      one
  ; Virtual.queryDegree =
      one
  ; Virtual.queryWorkPolynomial =
      lookupWorkPolynomial formula
  }

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- There is no longer an abstract semantic-source premise for virtual quotation:
-- every Cook.BooleanFormula has a canonical exact indexed source.  The live
-- producer obligation is to compile the actual guarded Cook constructor plus
-- this indexed lookup to one universal finite standard machine on the canonical
-- answer-blind GuardedCookBitQuery encoding.
------------------------------------------------------------------------
