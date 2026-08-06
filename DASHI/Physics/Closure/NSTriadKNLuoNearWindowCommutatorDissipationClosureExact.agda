module DASHI.Physics.Closure.NSTriadKNLuoNearWindowCommutatorDissipationClosureExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- PURPOSE
-- Compose the two non-circular ingredients isolated in round nine:
--
--   (1) the commutator second moment changes 2 lambda_q into the critical
--       constant 2;
--   (2) an independently proved normalized terminal dissipation tail is at
--       most 1/128.
--
-- Their product is at most 1/64.  This theorem closes the scalar budget once
-- a continuum PDE estimate has genuinely bounded the newest-layer term by
-- this product.  It does not manufacture that PDE estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong; subst; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowScalingObstructionExact as Obstruction
import DASHI.Physics.Closure.NSTriadKNLuoCommutatorScaleAuditExact as ScaleAudit
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTerminalDissipationTailClosureExact as Tail

record NearWindowCommutatorDissipationData : Set where
  constructor near-window-commutator-dissipation-data
  field
    outputShell : Nat
    terminalSmallness : Tail.TerminalDissipationSmallness

open NearWindowCommutatorDissipationData public

commutatorDissipationNearContribution :
  NearWindowCommutatorDissipationData → ℚ
commutatorDissipationNearContribution inputs =
  Obstruction.nearEnergyOnlyModel (outputShell inputs)
  * ScaleAudit.inverseOutputScale (outputShell inputs)
  * Tail.tailMass (terminalSmallness inputs)

commutatorDissipationMeaning :
  (inputs : NearWindowCommutatorDissipationData) →
  commutatorDissipationNearContribution inputs
  ≡ Tail.criticalizedNearContribution (terminalSmallness inputs)
commutatorDissipationMeaning inputs =
  begin
    commutatorDissipationNearContribution inputs
  ≡⟨ cong
       (λ criticalFactor →
         criticalFactor * Tail.tailMass (terminalSmallness inputs))
       (ScaleAudit.bareCriticalCommutatorLeavesConstantTwo
         (outputShell inputs)) ⟩
    Tail.two * Tail.tailMass (terminalSmallness inputs)
  ≡⟨ solve
       ( Tail.two
       ∷ Tail.tailMass (terminalSmallness inputs)
       ∷ []) ⟩
    Tail.criticalizedNearContribution (terminalSmallness inputs)
  ∎

commutatorDissipationClosesNearHalfBudget :
  (inputs : NearWindowCommutatorDissipationData) →
  commutatorDissipationNearContribution inputs
  ≤ Tail.oneSixtyFourth
commutatorDissipationClosesNearHalfBudget inputs =
  subst
    (λ lower → lower ≤ Tail.oneSixtyFourth)
    (Eq.sym (commutatorDissipationMeaning inputs))
    (Tail.terminalDissipationClosesNearHalfBudget
      (terminalSmallness inputs))
