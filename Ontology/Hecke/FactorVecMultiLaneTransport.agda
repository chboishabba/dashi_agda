module Ontology.Hecke.FactorVecMultiLaneTransport where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Maybe    using (Maybe; just; nothing)
open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecSignedTransport using
  (transferPrime; transferDiscrepancy)
import Ontology.Hecke.MultiLaneSignedTransport as HM

------------------------------------------------------------------------
-- First concrete multi-lane mode family: compose two signed single-prime
-- transfers. This gives a genuinely mode-labelled transport surface without
-- forcing a new arithmetic layer yet.

record PairMode : Set where
  constructor pairMode
  field
    first  : SSP
    second : SSP

open PairMode public

pairTransport : PairMode → FactorVec → Maybe FactorVec
pairTransport m v with transferPrime (first m) v
... | nothing = nothing
... | just v₁ with transferPrime (second m) v₁
... | nothing = nothing
... | just v₂ = just v₂

pairLegal : PairMode → FactorVec → Bool
pairLegal m v with pairTransport m v
... | just _  = true
... | nothing = false

pairDelta : PairMode → FactorVec → HM.SignedDeltaOn FactorVec
pairDelta m v = record
  { apply = λ _ → pairTransport m v
  }

pairDiscrepancy : PairMode → FactorVec → Nat
pairDiscrepancy m v with transferPrime (first m) v
... | nothing = suc (transferDiscrepancy (first m) v)
... | just v₁ = transferDiscrepancy (first m) v + transferDiscrepancy (second m) v₁

factorVecMultiLaneTransport : HM.MultiLaneSignedTransportOn PairMode FactorVec
factorVecMultiLaneTransport = record
  { delta           = pairDelta
  ; legal           = pairLegal
  ; transport       = pairTransport
  ; transport-sound = λ m s s' stepEq → stepEq
  ; illegal-fails   = illegal-fails
  }
  where
  illegal-fails : ∀ m s → pairLegal m s ≡ false → pairTransport m s ≡ nothing
  illegal-fails m s legalEq with pairTransport m s
  ... | nothing = refl
  ... | just s' with legalEq
  ... | ()

factorVecMultiLaneReverseHecke :
  HM.MultiLaneSignedReverseHeckeOn PairMode FactorVec
factorVecMultiLaneReverseHecke = record
  { address           = λ v → v
  ; modeTransport     = factorVecMultiLaneTransport
  ; pullback          = pairTransport
  ; discrepancy       = pairDiscrepancy
  ; compatible        = pairLegal
  ; compatible-sound  = λ m s s' stepEq okEq → stepEq
  }
