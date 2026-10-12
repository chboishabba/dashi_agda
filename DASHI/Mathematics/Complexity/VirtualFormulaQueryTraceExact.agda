module DASHI.Mathematics.Complexity.VirtualFormulaQueryTraceExact where

------------------------------------------------------------------------
-- FINITE QUERY TRACE FOR VIRTUAL FORMULA INPUT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual

record SuccessfulBitQuery
    {formula : Cook.BooleanFormula}
    (source : Virtual.VirtualFormulaBitSource formula) : Set where
  field
    index : Nat
    bit : Agda.Builtin.Bool.Bool
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
queryTraceLength (_ ∷ rest) = Agda.Builtin.Nat.suc (queryTraceLength rest)

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
    (Agda.Builtin.Sigma.Σ Nat
      (λ index →
        Agda.Builtin.Sigma.Σ Agda.Builtin.Bool.Bool
          (λ bit →
            Virtual.BitAt index
              (DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact.encodeFormulaBits formula)
              bit)))
queryTraceAllSound [] = []
queryTraceAllSound {source = source} (query ∷ rest) =
  (index query Agda.Builtin.Sigma.,
    (bit query Agda.Builtin.Sigma.,
      Virtual.readSound source (resultExact query)))
  ∷ queryTraceAllSound rest

------------------------------------------------------------------------
-- A simulation receipt must pay these reads inside its own target-machine
-- clock. This record keeps that budget explicit without presupposing a specific
-- virtual-input interpreter construction.
------------------------------------------------------------------------

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
-- virtual-input TM. Those are downstream compiler obligations rather than an
-- implicit oracle assumption.
------------------------------------------------------------------------
