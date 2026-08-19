module DASHI.Physics.Closure.NSTriadKNTwoThirdsSignedDominationToViscousMarginRound92Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND92 / EXACT TWO-THIRDS COMPILER
--
-- The older signed-Schur programme targets the exact inequality
--
--      3 B <= 2 G.
--
-- On its own this only says that the bad sector is at most two-thirds of the
-- good sector.  If, on the SAME physical carrier, the good sector also funds
-- literal dissipation,
--
--      mu D <= G,
--
-- then the two facts have a stronger consumer-facing consequence:
--
--      B + (mu/3) D <= G.
--
-- Equivalently, the proposed two-thirds domination constant buys exactly one
-- third of whatever dissipation floor is carried by the good sector.  This is
-- the shortest algebraic bridge from the Gate-1 constant to the Round92 strict
-- surplus consumer.  No statistical/helical claim is imported from Waleffe;
-- no geometric depletion theorem is imported from Constantin--Fefferman.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

oneThird two three : ℚ
oneThird = Int.+ 1 Data.Rational.Base./ 3
two = Int.+ 2 Data.Rational.Base./ 1
three = Int.+ 3 Data.Rational.Base./ 1

record TwoThirdsSignedDissipationData : Set where
  constructor two-thirds-signed-dissipation-data
  field
    bad good dissipation mu : ℚ

    badNonnegative : 0ℚ ≤ bad
    goodNonnegative : 0ℚ ≤ good
    dissipationNonnegative : 0ℚ ≤ dissipation
    muNonnegative : 0ℚ ≤ mu

    twoThirdsSignedDomination :
      three * bad ≤ two * good

    goodFundsDissipation :
      mu * dissipation ≤ good

open TwoThirdsSignedDissipationData public

oneThirdNonnegative : 0ℚ ≤ oneThird
oneThirdNonnegative = ℚP.0≤p⇒0≤p/q (ℚP.0≤1)

thirdGoodFunding :
  (data : TwoThirdsSignedDissipationData) →
  oneThird * (mu data * dissipation data) ≤ oneThird * good data
thirdGoodFunding data =
  let instance oneThirdNN = nonNegative oneThirdNonnegative
  in ℚP.*-monoˡ-≤-nonNeg oneThird (goodFundsDissipation data)

twoThirdsDominationAsBadPlusThirdGood :
  (data : TwoThirdsSignedDissipationData) →
  bad data + oneThird * good data ≤ good data
twoThirdsDominationAsBadPlusThirdGood data =
  let
    oneThirdThree : oneThird * three ≡ Int.+ 1 Data.Rational.Base./ 1
    oneThirdThree = refl

    scaled :
      oneThird * (three * bad data) ≤ oneThird * (two * good data)
    scaled =
      let instance oneThirdNN = nonNegative oneThirdNonnegative
      in ℚP.*-monoˡ-≤-nonNeg oneThird (twoThirdsSignedDomination data)

    leftMeaning :
      oneThird * (three * bad data) ≡ bad data
    leftMeaning = solve (bad data ∷ [])

    rightMeaning :
      oneThird * (two * good data)
      ≡ good data + (- (oneThird * good data))
    rightMeaning = solve (good data ∷ [])

    reduced :
      bad data ≤ good data + (- (oneThird * good data))
    reduced =
      subst
        (λ left → left ≤ good data + (- (oneThird * good data)))
        leftMeaning
        (subst
          (λ right → oneThird * (three * bad data) ≤ right)
          rightMeaning
          scaled)

    shifted = ℚP.+-monoʳ-≤ (oneThird * good data) reduced
  in
  subst
    (λ left → left ≤ good data)
    (solve (bad data ∷ good data ∷ []))
    (subst
      (λ right → bad data + oneThird * good data ≤ right)
      (solve (good data ∷ []))
      shifted)

oneThirdMuDissipationBelowOneThirdGood :
  (data : TwoThirdsSignedDissipationData) →
  (oneThird * mu data) * dissipation data ≤ oneThird * good data
oneThirdMuDissipationBelowOneThirdGood data =
  let raw = thirdGoodFunding data
      leftMeaning :
        oneThird * (mu data * dissipation data)
        ≡ (oneThird * mu data) * dissipation data
      leftMeaning = solve (mu data ∷ dissipation data ∷ [])
  in subst
    (λ left → left ≤ oneThird * good data)
    leftMeaning raw

twoThirdsSignedDominationProducesViscousMargin :
  (data : TwoThirdsSignedDissipationData) →
  bad data + (oneThird * mu data) * dissipation data ≤ good data
twoThirdsSignedDominationProducesViscousMargin data =
  ℚP.≤-trans
    (ℚP.+-mono-≤ ℚP.≤-refl
      (oneThirdMuDissipationBelowOneThirdGood data))
    (twoThirdsDominationAsBadPlusThirdGood data)

round92TwoThirdsDominationPlusGoodFundingGivesMuOverThreeMargin : Bool
round92TwoThirdsDominationPlusGoodFundingGivesMuOverThreeMargin = true

round92TwoThirdsDominationAloneGivesAbsoluteViscousMargin : Bool
round92TwoThirdsDominationAloneGivesAbsoluteViscousMargin = false

round92TwoThirdsDominationPlusGoodFundingGivesMuOverThreeMarginIsTrue :
  round92TwoThirdsDominationPlusGoodFundingGivesMuOverThreeMargin ≡ true
round92TwoThirdsDominationPlusGoodFundingGivesMuOverThreeMarginIsTrue = refl

round92TwoThirdsDominationAloneGivesAbsoluteViscousMarginIsFalse :
  round92TwoThirdsDominationAloneGivesAbsoluteViscousMargin ≡ false
round92TwoThirdsDominationAloneGivesAbsoluteViscousMarginIsFalse = refl
