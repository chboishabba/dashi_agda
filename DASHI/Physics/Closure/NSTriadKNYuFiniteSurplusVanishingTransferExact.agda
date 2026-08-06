module DASHI.Physics.Closure.NSTriadKNYuFiniteSurplusVanishingTransferExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv:2606.27560v1.
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Formalise the final ordered step behind Yu's Theorem 10.3.  If the
-- post-near-field surplus obeys
--
--   S_k <= F_k + C Se_k + L_k,
--
-- and the three nonnegative residual envelopes are jointly eventually below
-- epsilon/3, then S_k tends to zero.  Source-side summability, Carleson
-- closure and increment/localization estimates are the producers of this
-- joint tail property; the epsilon transfer itself is closed exactly here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; _≤_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

oneThird : ℚ
oneThird = Int.+ 1 / 3

record ThreeResidualSurplusData : Set where
  constructor three-residual-surplus-data
  field
    farField commutatorEnvelope localization surplus : ℕ → ℚ
    pointwiseSurplusBound :
      (shell : ℕ) →
      surplus shell
      ≤ farField shell
        + commutatorEnvelope shell
        + localization shell

open ThreeResidualSurplusData public

record JointResidualVanishing
  (dataSet : ThreeResidualSurplusData) : Set where
  constructor joint-residual-vanishing
  field
    commonTail :
      (epsilon : ℚ) →
      0ℚ < epsilon →
      ℕ

    farTailBound :
      (epsilon : ℚ) →
      (epsilonPositive : 0ℚ < epsilon) →
      (shell : ℕ) →
      commonTail epsilon epsilonPositive ≤ shell →
      farField dataSet shell ≤ oneThird * epsilon

    commutatorTailBound :
      (epsilon : ℚ) →
      (epsilonPositive : 0ℚ < epsilon) →
      (shell : ℕ) →
      commonTail epsilon epsilonPositive ≤ shell →
      commutatorEnvelope dataSet shell ≤ oneThird * epsilon

    localizationTailBound :
      (epsilon : ℚ) →
      (epsilonPositive : 0ℚ < epsilon) →
      (shell : ℕ) →
      commonTail epsilon epsilonPositive ≤ shell →
      localization dataSet shell ≤ oneThird * epsilon

open JointResidualVanishing public

surplusVanishingFromResidualVanishing :
  (dataSet : ThreeResidualSurplusData) →
  JointResidualVanishing dataSet →
  Limit.TendsToZero (surplus dataSet)
surplusVanishingFromResidualVanishing dataSet residualVanishing =
  Limit.tends-to-zero transfer
  where
    transfer :
      (epsilon : ℚ) →
      0ℚ < epsilon →
      Limit.EventuallyBelow (surplus dataSet) epsilon
    transfer epsilon epsilonPositive =
      let
        cutoff = commonTail residualVanishing epsilon epsilonPositive

        tail :
          (shell : ℕ) →
          cutoff ≤ shell →
          surplus dataSet shell ≤ epsilon
        tail shell cutoffBelowShell =
          let
            summedResiduals :
              farField dataSet shell
                + commutatorEnvelope dataSet shell
                + localization dataSet shell
              ≤ oneThird * epsilon
                + oneThird * epsilon
                + oneThird * epsilon
            summedResiduals =
              ℚₚ.+-mono-≤
                (ℚₚ.+-mono-≤
                  (farTailBound
                    residualVanishing epsilon epsilonPositive
                    shell cutoffBelowShell)
                  (commutatorTailBound
                    residualVanishing epsilon epsilonPositive
                    shell cutoffBelowShell))
                (localizationTailBound
                  residualVanishing epsilon epsilonPositive
                  shell cutoffBelowShell)

            epsilonMeaning :
              oneThird * epsilon
                + oneThird * epsilon
                + oneThird * epsilon
              ≡ epsilon
            epsilonMeaning = solve (epsilon ∷ [])
          in
          ℚₚ.≤-trans
            (pointwiseSurplusBound dataSet shell)
            (subst
              (λ upper →
                farField dataSet shell
                  + commutatorEnvelope dataSet shell
                  + localization dataSet shell
                ≤ upper)
              epsilonMeaning
              summedResiduals)
      in
      Limit.eventually-below cutoff tail
