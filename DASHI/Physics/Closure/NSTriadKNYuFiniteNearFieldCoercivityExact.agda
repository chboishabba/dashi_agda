module DASHI.Physics.Closure.NSTriadKNYuFiniteNearFieldCoercivityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv:2606.27560v1.
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- Classical geometric reference:
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- PURPOSE
-- Prove the exact algebraic composition of Yu's Theorems 2.1 and 2.2.
-- The literal source coefficient 3/(8 pi) is not rational.  Therefore the
-- field geometricCoefficient below is an explicitly supplied nonnegative
-- rational majorant for the source coefficient, together with the already
-- transported bound
--
--   V_near <= geometricCoefficient * A_pair.
--
-- From that rationalized source bound and
--
--   A_pair <= eta P + c_res O
--
-- derive
--
--   V_near <= (g eta) P + (g c_res) O.
--
-- A second theorem substitutes a chosen retained-diffusion coefficient
-- 1-epsilon.  The continuum singular-integral estimate, the comparison of
-- 3/(8 pi) with the chosen rational majorant, and the difference-quotient
-- estimate remain visible source producers; their rational coercive
-- composition is fully closed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record NearFieldCoercivityData : Set where
  constructor near-field-coercivity-data
  field
    positiveNearField pairwiseDefect diffusion reservoir : ℚ
    geometricCoefficient eta reservoirCoefficient : ℚ

    geometricCoefficientNonnegative :
      0ℚ ≤ geometricCoefficient

    geometricDepletionBound :
      positiveNearField ≤ geometricCoefficient * pairwiseDefect

    pairwiseDefectBound :
      pairwiseDefect
      ≤ eta * diffusion + reservoirCoefficient * reservoir

open NearFieldCoercivityData public

composedNearFieldCoercivity :
  (dataSet : NearFieldCoercivityData) →
  positiveNearField dataSet
  ≤ (geometricCoefficient dataSet * eta dataSet)
      * diffusion dataSet
    + (geometricCoefficient dataSet * reservoirCoefficient dataSet)
      * reservoir dataSet
composedNearFieldCoercivity dataSet =
  let
    multiplied :
      geometricCoefficient dataSet * pairwiseDefect dataSet
      ≤ geometricCoefficient dataSet
        * (eta dataSet * diffusion dataSet
          + reservoirCoefficient dataSet * reservoir dataSet)
    multiplied =
      let
        instance
          geometricCoefficientIsNonnegative =
            nonNegative (geometricCoefficientNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (geometricCoefficient dataSet)
        (pairwiseDefectBound dataSet)

    chained :
      positiveNearField dataSet
      ≤ geometricCoefficient dataSet
        * (eta dataSet * diffusion dataSet
          + reservoirCoefficient dataSet * reservoir dataSet)
    chained =
      ℚₚ.≤-trans (geometricDepletionBound dataSet) multiplied

    targetMeaning :
      geometricCoefficient dataSet
        * (eta dataSet * diffusion dataSet
          + reservoirCoefficient dataSet * reservoir dataSet)
      ≡ (geometricCoefficient dataSet * eta dataSet)
          * diffusion dataSet
        + (geometricCoefficient dataSet * reservoirCoefficient dataSet)
          * reservoir dataSet
    targetMeaning =
      solve
        ( geometricCoefficient dataSet
        ∷ eta dataSet
        ∷ diffusion dataSet
        ∷ reservoirCoefficient dataSet
        ∷ reservoir dataSet
        ∷ [])
  in
  subst
    (λ upper → positiveNearField dataSet ≤ upper)
    targetMeaning
    chained

record AbsorbedNearFieldData : Set where
  constructor absorbed-near-field-data
  field
    coercivity : NearFieldCoercivityData
    retainedDiffusionCoefficient : ℚ
    coefficientChoice :
      geometricCoefficient coercivity * eta coercivity
      ≡ retainedDiffusionCoefficient

open AbsorbedNearFieldData public

absorbedNearFieldCoercivity :
  (absorbed : AbsorbedNearFieldData) →
  positiveNearField (coercivity absorbed)
  ≤ retainedDiffusionCoefficient absorbed
      * diffusion (coercivity absorbed)
    + (geometricCoefficient (coercivity absorbed)
        * reservoirCoefficient (coercivity absorbed))
      * reservoir (coercivity absorbed)
absorbedNearFieldCoercivity absorbed =
  subst
    (λ coefficient →
      positiveNearField (coercivity absorbed)
      ≤ coefficient * diffusion (coercivity absorbed)
        + (geometricCoefficient (coercivity absorbed)
            * reservoirCoefficient (coercivity absorbed))
          * reservoir (coercivity absorbed))
    (coefficientChoice absorbed)
    (composedNearFieldCoercivity (coercivity absorbed))
