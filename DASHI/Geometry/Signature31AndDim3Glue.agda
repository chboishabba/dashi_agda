module DASHI.Geometry.Signature31AndDim3Glue where

open import Agda.Builtin.Equality using (_≡_)
open import Ultrametric as UMetric
open import DASHI.Physics.ClosureGlue as Glue

record CausalAxioms′ : Set₁ where
  field
    A : Glue.ClosureAxioms

  open Glue.ClosureAxioms A public

  S′ : Set
  S′ = Glue.S A

  U′ : UMetric.Ultrametric S′
  U′ = Glue.U A

  T′ : S′ → S′
  T′ = Glue.T A

  fp′ : S′
  fp′ = Glue.fp A

  fixed′ : T′ fp′ ≡ fp′
  fixed′ = Glue.T-fixes-fp A
