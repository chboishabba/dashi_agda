module DASHI.Mathematics.Complexity.VirtualFormulaQueryTraceExact where

------------------------------------------------------------------------
-- FINITE QUERY TRACE FOR VIRTUAL FORMULA INPUT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _,_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual

record SuccessfulBitQuery
    {formula : Cook.BooleanFormula}
    (source : Virtual.VirtualFormulaBitSource formula) : Set where
  field
    index : Nat
    bit : Bool
    resultExact : Virtual.readBit source index ≡ just bit

open SuccessfulBitQuery public

QueryTrace :
  ∀ {formula : Cook.BooleanFormula} →
  Virtual.VirtualFormulaBitSource formula → Set
QueryTrace source = List (SuccessfulBitQuery source)

queryTraceLength :
  ∀ {formula : Cook.BooleanFormula}
    {source : Virtual.VirtualFormulaBitSource formula} →
  QueryTrace source → Nat
queryTraceLength [] = zero
queryTraceLength (_ ∷ rest) = suc (queryTraceLength rest)

queryTraceWork :
  ∀ {formula : Cook.BooleanFormula}
    {source : Virtual.VirtualFormulaBitSource formula} →
  QueryTrace source → Nat
queryTraceWork {source = source} [] = zero
queryTraceWork {source = source} (query ∷ rest) =
  Virtual.queryWork source (index query)
  + queryTraceWork rest

queryTraceAllSound :
  ∀ {formula : Cook.BooleanFormula}
    {source : Virtual.VirtualFormulaBitSource formula}
    (trace : QueryTrace source) →
  List
    (Σ Nat
      (λ index →
        Σ Bool
          (λ bit →
            Virtual.BitAt index
              (Binary.encodeFormulaBits formula)
              bit)))
queryTraceAllSound [] = []
queryTraceAllSound {source = source} (query ∷ rest) =
  (index query ,
    (bit query ,
      Virtual.readSound source (resultExact query)))
  ∷ queryTraceAllSound rest

record QueryTraceCostReceipt
    {formula : Cook.BooleanFormula}
    (source : Virtual.VirtualFormulaBitSource formula)
    (targetSteps : Nat) : Set where
  field
    trace : QueryTrace source
    queryWorkFitsTarget : queryTraceWork trace ≤ targetSteps

open QueryTraceCostReceipt public

------------------------------------------------------------------------
-- This does not yet bound query COUNT by simulated source steps or construct a
-- virtual-input TM. Those are downstream compiler obligations.
------------------------------------------------------------------------
