module DASHI.Physics.Closure.NSTriadKNLuoFiniteSourceFaithfulSection4Exact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Implement the finite source-faithful analogue of Luo's Section-4 Step 1.
-- The J11 lower and upper halves, J12, and J2 are represented by finite time
-- or dyadic sample lists.  Their final square bounds are derived from
--
--   * the exact finite Jensen/Cauchy theorem;
--   * separately supplied sums-of-squares estimates; and
--   * the exact lower/upper half recombination theorem.
--
-- In particular, the J11 estimate is not silently replaced by the unrelated
-- pointwise Schur-factorization lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact as Jensen
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact as Half

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = toWitness {a? = 0ℚ ≤? 1ℚ} _

rationalLengthNonnegative :
  (values : List ℚ) →
  0ℚ ≤ Jensen.rationalLength values
rationalLengthNonnegative [] = ℚₚ.≤-refl
rationalLengthNonnegative (_ ∷ values) =
  L2.addNonnegative
    oneNonnegative
    (rationalLengthNonnegative values)

record FiniteSourceFaithfulSection4Data : Set where
  constructor finite-source-section4
  field
    j11LowerSamples j11UpperSamples j12Samples j2Samples : List ℚ

    j11LowerEnergy j11UpperEnergy j12Energy j2Energy : ℚ

    j11LowerSquaresBound :
      Jensen.sumSquares j11LowerSamples ≤ j11LowerEnergy

    j11UpperSquaresBound :
      Jensen.sumSquares j11UpperSamples ≤ j11UpperEnergy

    j12SquaresBound :
      Jensen.sumSquares j12Samples ≤ j12Energy

    j2SquaresBound :
      Jensen.sumSquares j2Samples ≤ j2Energy

open FiniteSourceFaithfulSection4Data public

jensenWithEnergyBudget :
  (samples : List ℚ) →
  (energy : ℚ) →
  Jensen.sumSquares samples ≤ energy →
  L2.square (Jensen.sumValues samples)
  ≤ Jensen.rationalLength samples * energy
jensenWithEnergyBudget samples energy squaresBound =
  let
    first :
      L2.square (Jensen.sumValues samples)
      ≤ Jensen.sumSquares samples * Jensen.rationalLength samples
    first = Jensen.finiteJensenSquare samples

    second :
      Jensen.sumSquares samples * Jensen.rationalLength samples
      ≤ energy * Jensen.rationalLength samples
    second =
      let instance countIsNonnegative =
        nonNegative (rationalLengthNonnegative samples)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Jensen.rationalLength samples)
        squaresBound

    targetMeaning :
      energy * Jensen.rationalLength samples
      ≡ Jensen.rationalLength samples * energy
    targetMeaning = solve (energy ∷ Jensen.rationalLength samples ∷ [])
  in
  ℚₚ.≤-trans
    first
    (subst
      (λ upper →
        Jensen.sumSquares samples * Jensen.rationalLength samples
        ≤ upper)
      targetMeaning
      second)

j11LowerSourceBound :
  (data : FiniteSourceFaithfulSection4Data) →
  L2.square (Jensen.sumValues (j11LowerSamples data))
  ≤ Jensen.rationalLength (j11LowerSamples data)
      * j11LowerEnergy data
j11LowerSourceBound data =
  jensenWithEnergyBudget
    (j11LowerSamples data)
    (j11LowerEnergy data)
    (j11LowerSquaresBound data)

j11UpperSourceBound :
  (data : FiniteSourceFaithfulSection4Data) →
  L2.square (Jensen.sumValues (j11UpperSamples data))
  ≤ Jensen.rationalLength (j11UpperSamples data)
      * j11UpperEnergy data
j11UpperSourceBound data =
  jensenWithEnergyBudget
    (j11UpperSamples data)
    (j11UpperEnergy data)
    (j11UpperSquaresBound data)

j12SourceBound :
  (data : FiniteSourceFaithfulSection4Data) →
  L2.square (Jensen.sumValues (j12Samples data))
  ≤ Jensen.rationalLength (j12Samples data) * j12Energy data
j12SourceBound data =
  jensenWithEnergyBudget
    (j12Samples data)
    (j12Energy data)
    (j12SquaresBound data)

j2SourceBound :
  (data : FiniteSourceFaithfulSection4Data) →
  L2.square (Jensen.sumValues (j2Samples data))
  ≤ Jensen.rationalLength (j2Samples data) * j2Energy data
j2SourceBound data =
  jensenWithEnergyBudget
    (j2Samples data)
    (j2Energy data)
    (j2SquaresBound data)

j11SourceBound :
  (data : FiniteSourceFaithfulSection4Data) →
  L2.square
    ( Jensen.sumValues (j11LowerSamples data)
    + Jensen.sumValues (j11UpperSamples data)
    )
  ≤ Half.two
      * ( Jensen.rationalLength (j11LowerSamples data)
          * j11LowerEnergy data
        + Jensen.rationalLength (j11UpperSamples data)
          * j11UpperEnergy data
        )
j11SourceBound data =
  let
    splitBound =
      Half.squareOfSumBelowTwiceSquares
        (Jensen.sumValues (j11LowerSamples data))
        (Jensen.sumValues (j11UpperSamples data))

    componentBound :
      L2.square (Jensen.sumValues (j11LowerSamples data))
        + L2.square (Jensen.sumValues (j11UpperSamples data))
      ≤ Jensen.rationalLength (j11LowerSamples data)
          * j11LowerEnergy data
        + Jensen.rationalLength (j11UpperSamples data)
          * j11UpperEnergy data
    componentBound =
      ℚₚ.+-mono-≤
        (j11LowerSourceBound data)
        (j11UpperSourceBound data)

    scaledComponentBound :
      Half.two
        * ( L2.square (Jensen.sumValues (j11LowerSamples data))
          + L2.square (Jensen.sumValues (j11UpperSamples data))
          )
      ≤ Half.two
        * ( Jensen.rationalLength (j11LowerSamples data)
            * j11LowerEnergy data
          + Jensen.rationalLength (j11UpperSamples data)
            * j11UpperEnergy data
          )
    scaledComponentBound =
      let instance twoIsNonnegative = nonNegative Half.twoNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg Half.two componentBound
  in
  ℚₚ.≤-trans splitBound scaledComponentBound

finiteSourceFaithfulJ11Closed : Bool
finiteSourceFaithfulJ11Closed = true

finiteSourceFaithfulJ12J2Closed : Bool
finiteSourceFaithfulJ12J2Closed = true

finiteSourceFaithfulJ11ClosedIsTrue :
  finiteSourceFaithfulJ11Closed ≡ true
finiteSourceFaithfulJ11ClosedIsTrue = refl

finiteSourceFaithfulJ12J2ClosedIsTrue :
  finiteSourceFaithfulJ12J2Closed ≡ true
finiteSourceFaithfulJ12J2ClosedIsTrue = refl
