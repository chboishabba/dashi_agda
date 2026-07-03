module DASHI.Physics.Closure.QuarterMarginBase where

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; sym)
open import DASHI.MDL.MDLDescentTradeoff
  using (AddMonoid; OrderedMonoid)

----------------------------------------------------------------------
-- Abstract quarter-margin model.
--
-- Packages an ordered additive carrier with distinguished constants:
--
--   • θ-principal  — principal directional transport contribution
--   • η-defect     — total defect contribution from Lemma A
--   • one-sixth    — observed principal target
--   • one-twelfth  — remaining slack to the quarter margin
--   • one-quarter  — closing threshold for the Gate 2-A budget
--
-- Lemma C (internal):
--     θ-principal + η-defect ≤ 1/4
--
-- via the abstract hypotheses
--     θ-principal ≤ 1/6
--     η-defect   ≤ 1/12
--     1/6 + 1/12 ≤ 1/4.

record QuarterMarginModel : Set₁ where
  constructor mkQuarterMarginModel
  field
    orderedMonoid : OrderedMonoid {zero}

  open OrderedMonoid orderedMonoid public
  open AddMonoid M public

  field
    θ-principal η-defect : N
    one-sixth one-twelfth one-quarter : N

    θ≤1/6 : θ-principal ≤ one-sixth
    η≤1/12 : η-defect ≤ one-twelfth
    sixthPlusTwelfth≤Quarter : (one-sixth + one-twelfth) ≤ one-quarter

  lemma-c : (θ-principal + η-defect) ≤ one-quarter
  lemma-c =
    trans≤
      (θ-principal + η-defect)
      (one-sixth + one-twelfth)
      one-quarter
      (mono+ θ-principal one-sixth η-defect one-twelfth θ≤1/6 η≤1/12)
      sixthPlusTwelfth≤Quarter

open QuarterMarginModel public
