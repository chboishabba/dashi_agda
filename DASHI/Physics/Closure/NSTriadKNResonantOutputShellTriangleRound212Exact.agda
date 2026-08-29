module DASHI.Physics.Closure.NSTriadKNResonantOutputShellTriangleRound212Exact where

------------------------------------------------------------------------
-- ROUND212 / CONCRETE RESONANT DYADIC OUTPUT-SHELL TRIANGLE
--
-- The official max-norm owner already proves
--
--   |k|_inf <= |p|_inf + |q|_inf
--
-- on every physical resonance p+q=k.  Instead of requiring the older abstract
-- DyadicShellBounds package, combine that directly with total order of the two
-- input norms and the stdlib ceil-log doubling identity
--
--   ceil(log2(2 n)) = 1 + ceil(log2 n),  n>0.
--
-- Therefore every physical resonance has one input whose literal dyadic shell
-- controls the output shell:
--
--   j_k <= 1 + j_p   OR   j_k <= 1 + j_q.
--
-- This is cutoff-independent and needs no nonphysical shell assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; z≤n)
import Data.Nat.Properties as NatP
open import Data.Nat.Logarithm using (⌈log₂2*n⌉≡1+⌈log₂n⌉)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell

one : Nat
one = 1

resonantOutputShellTracksOneInput :
  (tau : Physical.PhysicalTriadIncidence) →
  (Shell.shellIndex (Physical.k tau) ≤ one + Shell.shellIndex (Physical.p tau))
  ⊎
  (Shell.shellIndex (Physical.k tau) ≤ one + Shell.shellIndex (Physical.q tau))
resonantOutputShellTracksOneInput tau
  with NatP.≤-total
    (Infinity.infinityNorm (Physical.p tau))
    (Infinity.infinityNorm (Physical.q tau))
... | inj₁ pNorm≤qNorm
  with Infinity.infinityNorm (Physical.q tau)
...   | zero =
  let
    outputNorm≤zero : Infinity.infinityNorm (Physical.k tau) ≤ zero
    outputNorm≤zero = NatP.≤-trans
      (Infinity.outputTriangle (Infinity.officialResonantNormConsequences tau))
      (NatP.+-mono-≤ pNorm≤qNorm NatP.≤-refl)

    outputShell≤zero : Shell.shellIndex (Physical.k tau) ≤ zero
    outputShell≤zero = Shell.shellIndexMonotone outputNorm≤zero
  in inj₂ (NatP.≤-trans outputShell≤zero z≤n)
...   | suc qNorm =
  let
    outputNorm≤sum :
      Infinity.infinityNorm (Physical.k tau)
      ≤ Infinity.infinityNorm (Physical.p tau) + suc qNorm
    outputNorm≤sum =
      Infinity.outputTriangle (Infinity.officialResonantNormConsequences tau)

    sum≤double :
      Infinity.infinityNorm (Physical.p tau) + suc qNorm
      ≤ suc qNorm + suc qNorm
    sum≤double = NatP.+-mono-≤ pNorm≤qNorm NatP.≤-refl

    outputNorm≤double :
      Infinity.infinityNorm (Physical.k tau) ≤ 2 * suc qNorm
    outputNorm≤double =
      subst
        (Infinity.infinityNorm (Physical.k tau) ≤_)
        (sym (NatP.*-comm 2 (suc qNorm)))
        (NatP.≤-trans outputNorm≤sum sum≤double)

    logBound :
      Shell.shellIndex (Physical.k tau)
      ≤ Shell.shellIndexMagnitude (2 * suc qNorm)
    logBound = Shell.shellIndexMonotone outputNorm≤double
  in
  inj₂
    (subst
      (Shell.shellIndex (Physical.k tau) ≤_)
      (⌈log₂2*n⌉≡1+⌈log₂n⌉ (suc qNorm))
      logBound)
... | inj₂ qNorm≤pNorm
  with Infinity.infinityNorm (Physical.p tau)
...   | zero =
  let
    outputNorm≤zero : Infinity.infinityNorm (Physical.k tau) ≤ zero
    outputNorm≤zero = NatP.≤-trans
      (Infinity.outputTriangle (Infinity.officialResonantNormConsequences tau))
      (NatP.+-mono-≤ NatP.≤-refl qNorm≤pNorm)

    outputShell≤zero : Shell.shellIndex (Physical.k tau) ≤ zero
    outputShell≤zero = Shell.shellIndexMonotone outputNorm≤zero
  in inj₁ (NatP.≤-trans outputShell≤zero z≤n)
...   | suc pNorm =
  let
    outputNorm≤sum :
      Infinity.infinityNorm (Physical.k tau)
      ≤ suc pNorm + Infinity.infinityNorm (Physical.q tau)
    outputNorm≤sum =
      Infinity.outputTriangle (Infinity.officialResonantNormConsequences tau)

    sum≤double :
      suc pNorm + Infinity.infinityNorm (Physical.q tau)
      ≤ suc pNorm + suc pNorm
    sum≤double = NatP.+-mono-≤ NatP.≤-refl qNorm≤pNorm

    outputNorm≤double :
      Infinity.infinityNorm (Physical.k tau) ≤ 2 * suc pNorm
    outputNorm≤double =
      subst
        (Infinity.infinityNorm (Physical.k tau) ≤_)
        (sym (NatP.*-comm 2 (suc pNorm)))
        (NatP.≤-trans outputNorm≤sum sum≤double)

    logBound :
      Shell.shellIndex (Physical.k tau)
      ≤ Shell.shellIndexMagnitude (2 * suc pNorm)
    logBound = Shell.shellIndexMonotone outputNorm≤double
  in
  inj₁
    (subst
      (Shell.shellIndex (Physical.k tau) ≤_)
      (⌈log₂2*n⌉≡1+⌈log₂n⌉ (suc pNorm))
      logBound)

round212ConcreteResonantOutputShellTriangleClosed : Bool
round212ConcreteResonantOutputShellTriangleClosed = true

round212UsesAbstractDyadicShellBounds : Bool
round212UsesAbstractDyadicShellBounds = false

round212ConcreteResonantOutputShellTriangleClosedIsTrue :
  round212ConcreteResonantOutputShellTriangleClosed ≡ true
round212ConcreteResonantOutputShellTriangleClosedIsTrue = refl
