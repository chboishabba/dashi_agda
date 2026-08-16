module DASHI.Physics.Closure.NSTriadKNLiteralBonyInteractionRoutingRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 63 B0 CONTRIBUTION
--
-- The raw odd-P/Q commutator contains interactions that should not all be
-- interpreted as the near-diagonal Com owner.  This file classifies EVERY
-- literal physical triad by the actual dyadic shell geometry, at the official
-- separation Csep=3:
--
--   LH : j(p)+3 <= j(q),
--   HL : j(q)+3 <= j(p),
--   HH->L : j(k)+3 <= j(p) and j(k)+3 <= j(q),
--   residual : none of the above.
--
-- The already-proved resonance geometry then gives, constructively:
--
--   LH     => output k is within one shell of input q,
--   HL     => output k is within one shell of advector p,
--   HH->L  => the two high inputs p,q are within one shell.
--
-- Therefore the Round62 shell-0 -> shell-3 odd-P/Q witness is not a failure of
-- Bony localization: it is classified EXACTLY as HL and should be routed to the
-- HL owner before the near-Com common-hat theorem is attempted.
--
-- This is a finite exact partition of triad geometry.  It does not yet claim
-- that every residual interaction is width-one in (q,k); the remaining B0
-- analytic/combinatorial task is precisely to split that finite residual into
-- the actual near-Com piece and any remaining owner/tail terms.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; ∣_-_∣)
import Data.Nat.Properties as Nat
open import Relation.Nullary using (¬_; yes; no)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicConsequencesClosed as Dyadic
import DASHI.Physics.Closure.NSTriadKNComRawHardLowPassCommonHatNoGoRound62Exact as Raw

data LiteralBonyClass (τ : Physical.PhysicalTriadIncidence) : Set where
  lowHigh :
    Shell.shellIndex (Physical.p τ) + Shell.Csep
      ≤ Shell.shellIndex (Physical.q τ) →
    LiteralBonyClass τ
  highLow :
    Shell.shellIndex (Physical.q τ) + Shell.Csep
      ≤ Shell.shellIndex (Physical.p τ) →
    LiteralBonyClass τ
  highHighToLow :
    Shell.shellIndex (Physical.k τ) + Shell.Csep
      ≤ Shell.shellIndex (Physical.p τ) →
    Shell.shellIndex (Physical.k τ) + Shell.Csep
      ≤ Shell.shellIndex (Physical.q τ) →
    LiteralBonyClass τ
  residual :
    ¬ (Shell.shellIndex (Physical.p τ) + Shell.Csep
      ≤ Shell.shellIndex (Physical.q τ)) →
    ¬ (Shell.shellIndex (Physical.q τ) + Shell.Csep
      ≤ Shell.shellIndex (Physical.p τ)) →
    ( ¬ (Shell.shellIndex (Physical.k τ) + Shell.Csep
          ≤ Shell.shellIndex (Physical.p τ))
      ⊎
      ¬ (Shell.shellIndex (Physical.k τ) + Shell.Csep
          ≤ Shell.shellIndex (Physical.q τ)) ) →
    LiteralBonyClass τ

classifyLiteralBony :
  (τ : Physical.PhysicalTriadIncidence) → LiteralBonyClass τ
classifyLiteralBony τ
  with Nat._≤?_
    (Shell.shellIndex (Physical.p τ) + Shell.Csep)
    (Shell.shellIndex (Physical.q τ))
... | yes pLow = lowHigh pLow
... | no notPLow
  with Nat._≤?_
    (Shell.shellIndex (Physical.q τ) + Shell.Csep)
    (Shell.shellIndex (Physical.p τ))
... | yes qLow = highLow qLow
... | no notQLow
  with Nat._≤?_
    (Shell.shellIndex (Physical.k τ) + Shell.Csep)
    (Shell.shellIndex (Physical.p τ))
... | no notKLowP = residual notPLow notQLow (inj₁ notKLowP)
... | yes kLowP
  with Nat._≤?_
    (Shell.shellIndex (Physical.k τ) + Shell.Csep)
    (Shell.shellIndex (Physical.q τ))
... | yes kLowQ = highHighToLow kLowP kLowQ
... | no notKLowQ = residual notPLow notQLow (inj₂ notKLowQ)
  where
  open import Data.Sum.Base using (inj₁; inj₂)

lowHighTracksInputWithinOne :
  (τ : Physical.PhysicalTriadIncidence) →
  Shell.shellIndex (Physical.p τ) + Shell.Csep
    ≤ Shell.shellIndex (Physical.q τ) →
  ∣ Shell.shellIndex (Physical.k τ)
    - Shell.shellIndex (Physical.q τ) ∣ ≤ 1
lowHighTracksInputWithinOne = Dyadic.lowHighOutputTracksHighOne

highLowTracksAdvectorWithinOne :
  (τ : Physical.PhysicalTriadIncidence) →
  Shell.shellIndex (Physical.q τ) + Shell.Csep
    ≤ Shell.shellIndex (Physical.p τ) →
  ∣ Shell.shellIndex (Physical.k τ)
    - Shell.shellIndex (Physical.p τ) ∣ ≤ 1
highLowTracksAdvectorWithinOne = Dyadic.highLowOutputTracksHighOne

highHighInputsWithinOne :
  (τ : Physical.PhysicalTriadIncidence) →
  Shell.shellIndex (Physical.k τ) + Shell.Csep
    ≤ Shell.shellIndex (Physical.p τ) →
  Shell.shellIndex (Physical.k τ) + Shell.Csep
    ≤ Shell.shellIndex (Physical.q τ) →
  ∣ Shell.shellIndex (Physical.p τ)
    - Shell.shellIndex (Physical.q τ) ∣ ≤ 1
highHighInputsWithinOne = Dyadic.highHighToLowInputsComparableOne

farPhysicalTriad : Physical.PhysicalTriadIncidence
farPhysicalTriad =
  Physical.physicalTriad Raw.farP Raw.farInput Raw.farOutput Raw.farResonance

farPShellIsThree :
  Shell.shellIndex Raw.farP ≡ suc (suc (suc zero))
farPShellIsThree = refl

farTriadIsHighLow :
  Shell.shellIndex (Physical.q farPhysicalTriad) + Shell.Csep
  ≤ Shell.shellIndex (Physical.p farPhysicalTriad)
farTriadIsHighLow
  rewrite Raw.farInputShellIsZero
        | farPShellIsThree = Nat.≤-refl

farTriadOutputTracksAdvector :
  ∣ Shell.shellIndex (Physical.k farPhysicalTriad)
    - Shell.shellIndex (Physical.p farPhysicalTriad) ∣ ≤ 1
farTriadOutputTracksAdvector =
  highLowTracksAdvectorWithinOne farPhysicalTriad farTriadIsHighLow

round62FarWitnessRoutesToHL : Bool
round62FarWitnessRoutesToHL = true

literalBonyTriadClassificationConstructed : Bool
literalBonyTriadClassificationConstructed = true

round62FarWitnessRoutesToHLIsTrue :
  round62FarWitnessRoutesToHL ≡ true
round62FarWitnessRoutesToHLIsTrue = refl

literalBonyTriadClassificationConstructedIsTrue :
  literalBonyTriadClassificationConstructed ≡ true
literalBonyTriadClassificationConstructedIsTrue = refl
