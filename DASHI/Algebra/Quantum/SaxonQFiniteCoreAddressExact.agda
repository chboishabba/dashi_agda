module DASHI.Algebra.Quantum.SaxonQFiniteCoreAddressExact where

-- Finite classical core/site namespace for the manufacturer's 16 x 8
-- architecture assertion; all quantum meaning is inherited from the
-- existing NVSpinOneMulticoreAdapter in PR #1262, not redefined here.
-- A pure index receipt intentionally compiles without cross-PR imports.
-- Attribution: architecture to SAXON Q, index arithmetic to standard
-- finite combinatorics, adaptation to Johl Brown/OpenAI, 2026-10-26.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin; zero; suc)

Core : Set
Core = Fin 16

Site : Set
Site = Fin 8

record Address : Set where
  constructor mkAddress
  field
    core : Core
    site : Site

open Address public

-- The same-core predicate here is *index* equality, not a hardware
-- interaction or a demonstrated ability to entangle qubits.
record LocalPair : Set where
  constructor pair
  field
    location : Core
    first : Site
    second : Site

leftAddress : LocalPair → Address
leftAddress p = mkAddress (LocalPair.location p) (LocalPair.first p)

rightAddress : LocalPair → Address
rightAddress p = mkAddress (LocalPair.location p) (LocalPair.second p)

localPairSameCore : (p : LocalPair) →
  Address.core (leftAddress p) ≡ Address.core (rightAddress p)
localPairSameCore (pair c a b) = refl

-- A distinct-core address pair is not represented by LocalPair; any
-- future remote gate must add an explicitly evidenced quantum link.
