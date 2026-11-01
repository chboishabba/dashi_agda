module DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceRound60Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 60 CONTRIBUTION
--
-- Keep the canonical physical B source independent of the legacy Cotlar/Schur
-- consumer graph.  Earlier the source record lived in an adapter importing the
-- full Round47/42 envelope path, so merely checking the three literal fibre
-- inequalities could elaborate a very large transitive graph.
--
-- This module owns ONLY the source data:
--   * literal odd-(P/Q) active output-fibre relation;
--   * common-hat realization;
--   * normalized squared Gram energy;
--   * the three active same/adjacent estimates;
--   * shell distance and exact off-support annihilation.
--
-- Heavy legacy transport is downstream and optional.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (0ℚ)

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as Gram

record PhysicalNormalizedOddPQSource : Set₁ where
  field
    support : Hat.PhysicalOddPQCommonHatIdentification
    realization : Gram.PhysicalNormalizedOddPQGramRealization support
    bounds : Gram.SameAdjacentNormalizedFibreMassBounds realization

    shellDistance : Nat → Nat → Nat
    sameShellDistance : ∀ q → shellDistance q q ≡ zero
    forwardAdjacentDistance : ∀ q →
      shellDistance q (suc q) ≡ suc zero
    reverseAdjacentDistance : ∀ q →
      shellDistance (suc q) q ≡ suc zero

    inactiveSupportAnnihilatesPairProduct : ∀ q r →
      Hat.supportActive support q r ≡ false →
      Gram.pairProduct realization q r ≡ 0ℚ

open PhysicalNormalizedOddPQSource public

activeRelationIsLiteralOutputFibre :
  (source : PhysicalNormalizedOddPQSource) →
  ∀ q r →
  Hat.supportActive (support source) q r
  ≡ Hat.literalOddPQOutputFibreActive (support source) q r
activeRelationIsLiteralOutputFibre source q r = refl

-- Fail closed: the source type is canonical and lightweight, but its three
-- active estimates remain the physical analytic B frontier.
physicalNormalizedFibreBoundsConstructed : Bool
physicalNormalizedFibreBoundsConstructed = false

physicalNormalizedFibreBoundsConstructedIsFalse :
  physicalNormalizedFibreBoundsConstructed ≡ false
physicalNormalizedFibreBoundsConstructedIsFalse = refl
