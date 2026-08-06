module DASHI.Physics.Closure.NSTriadKNLuoFiniteBKMTimeShellFubiniExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- Authors: Tuomas Hytönen; Jan van Neerven; Mark Veraar; Lutz Weis.
-- Title: "Analysis in Banach Spaces, Volume I: Martingales and Littlewood--
-- Paley Theory".
-- Springer, 2016.
-- DOI: 10.1007/978-3-319-48520-1.
--
-- PURPOSE
-- Close the finite time/shell identification hidden inside the BKM proxy.
-- For explicit finite time cells and shell cutoffs, a pointwise Bernstein or
-- reconstruction bound
--
--   vorticityMagnitude(t,q) <= criterionDensity(t,q)
--
-- implies
--
--   sum_t sum_q vorticityMagnitude(t,q)
--     <= sum_q sum_t criterionDensity(t,q).
--
-- The equality between the two summation orders is the already-proved finite
-- scalar Fubini theorem.  Thus the finite truncated true time-shell quantity
-- and shell-first proxy are connected by actual mathematics, not a Boolean
-- receipt.  The continuum leaf is the passage from finite shell sums to the
-- genuine L-infinity norm and from rational time cells to Lebesgue time.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteBochnerFubiniExact as Finite

sumByMonotone :
  ∀ {A : Set}
    (items : List A)
    (left right : A → ℚ) →
  ((item : A) → left item ≤ right item) →
  Finite.sumBy items left ≤ Finite.sumBy items right
sumByMonotone [] left right pointwise = ℚₚ.≤-refl
sumByMonotone (item ∷ items) left right pointwise =
  ℚₚ.+-mono-≤
    (pointwise item)
    (sumByMonotone items left right pointwise)

record FiniteTimeShellBKMData : Set₁ where
  field
    TimeCell : Set
    Shell : Set
    timeCells : List TimeCell
    shells : List Shell
    vorticityMagnitude : TimeCell → Shell → ℚ
    criterionDensity : TimeCell → Shell → ℚ
    pointwiseReconstruction :
      (time : TimeCell) →
      (shell : Shell) →
      vorticityMagnitude time shell
      ≤ criterionDensity time shell

open FiniteTimeShellBKMData public

truncatedTrueTimeShellBKM :
  FiniteTimeShellBKMData → ℚ
truncatedTrueTimeShellBKM dataSet =
  Finite.sumBy (timeCells dataSet)
    (λ time →
      Finite.sumBy (shells dataSet)
        (vorticityMagnitude dataSet time))

shellFirstCriterionProxy :
  FiniteTimeShellBKMData → ℚ
shellFirstCriterionProxy dataSet =
  Finite.sumBy (shells dataSet)
    (λ shell →
      Finite.sumBy (timeCells dataSet)
        (λ time → criterionDensity dataSet time shell))

finiteBKMTimeShellIdentification :
  (dataSet : FiniteTimeShellBKMData) →
  truncatedTrueTimeShellBKM dataSet
  ≤ shellFirstCriterionProxy dataSet
finiteBKMTimeShellIdentification dataSet =
  let
    timeFirstBound :
      truncatedTrueTimeShellBKM dataSet
      ≤ Finite.sumBy (timeCells dataSet)
          (λ time →
            Finite.sumBy (shells dataSet)
              (criterionDensity dataSet time))
    timeFirstBound =
      sumByMonotone
        (timeCells dataSet)
        (λ time →
          Finite.sumBy (shells dataSet)
            (vorticityMagnitude dataSet time))
        (λ time →
          Finite.sumBy (shells dataSet)
            (criterionDensity dataSet time))
        (λ time →
          sumByMonotone
            (shells dataSet)
            (vorticityMagnitude dataSet time)
            (criterionDensity dataSet time)
            (pointwiseReconstruction dataSet time))

    fubiniMeaning :
      Finite.sumBy (timeCells dataSet)
        (λ time →
          Finite.sumBy (shells dataSet)
            (criterionDensity dataSet time))
      ≡ shellFirstCriterionProxy dataSet
    fubiniMeaning =
      Finite.finiteScalarFubini
        (timeCells dataSet)
        (shells dataSet)
        (criterionDensity dataSet)
  in
  subst
    (λ upper → truncatedTrueTimeShellBKM dataSet ≤ upper)
    fubiniMeaning
    timeFirstBound
