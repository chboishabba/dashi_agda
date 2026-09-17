module DASHI.Analysis.BishopComplexSeriesConvergenceExact where

------------------------------------------------------------------------
-- COMPONENTWISE COMPLEX SERIES CONVERGENCE ON THE VENDORED BISHOP REALS
--
-- DASHI CONTRIBUTION
--
-- The existing finite Eisenstein evaluator is complex-valued, while DASHI's
-- strongest concrete checked convergence backend is the vendored Bishop/Murray
-- real library.  This module pays the generic mathematical lift once: a complex
-- series is absolutely convergent componentwise when its real and imaginary
-- component series are absolutely convergent, and its canonical limit is the
-- pair of their Bishop limits.
--
-- This does NOT identify this carrier with the older
-- `DASHI.Analysis.ConcreteComplex.ComplexPair` package.  That same-carrier weld
-- remains explicit at consumers.
--
-- SOURCE / CODE ATTRIBUTION
-- Errett Bishop and Douglas Bridges, Constructive Analysis, Springer, 1985,
-- DOI 10.1007/978-3-642-61667-9.
-- Zachary Murray, Constructive Analysis in the Agda Proof Assistant, 2022,
-- arXiv:2205.08354 (no DOI assigned).
-- Viktor Csimma's continuation is vendored by DASHI at bishop commit
-- 240e38c7f6938f20f865b1f956c5f084da48bd54.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop

record BishopComplex : Set where
  constructor complex
  field
    re im : BishopReal.ℝ

open BishopComplex public

infix 4 _≈C_
_≈C_ : BishopComplex -> BishopComplex -> Set
complex a b ≈C complex c d =
  (BishopReal._≃_ a c) × (BishopReal._≃_ b d)
  where
  open import Data.Product using (_×_)

≈C-refl : (z : BishopComplex) -> z ≈C z
≈C-refl (complex a b) = BishopProperties.≃-refl , BishopProperties.≃-refl
  where
  open import Data.Product using (_,_)

realTerms : (Nat -> BishopComplex) -> Nat -> BishopReal.ℝ
realTerms terms n = re (terms n)

imagTerms : (Nat -> BishopComplex) -> Nat -> BishopReal.ℝ
imagTerms terms n = im (terms n)

record ComponentwiseAbsoluteSeriesConvergent
    (terms : Nat -> BishopComplex) : Set where
  constructor componentwise-absolute-series-convergent
  field
    realAbsolute : Bishop.BishopAbsoluteSeriesConvergent (realTerms terms)
    imagAbsolute : Bishop.BishopAbsoluteSeriesConvergent (imagTerms terms)

open ComponentwiseAbsoluteSeriesConvergent public

complexSeriesLimit :
  (terms : Nat -> BishopComplex) ->
  ComponentwiseAbsoluteSeriesConvergent terms ->
  BishopComplex
complexSeriesLimit terms absolute =
  complex
    (Bishop.bishopSeriesLimit (realTerms terms) (realAbsolute absolute))
    (Bishop.bishopSeriesLimit (imagTerms terms) (imagAbsolute absolute))

record ComplexSeriesConvergesTo
    (terms : Nat -> BishopComplex)
    (limit : BishopComplex) : Set where
  constructor complex-series-converges-to
  field
    realConverges :
      Bishop.BishopConvergesTo
        (BishopSequence.SeriesOf (realTerms terms))
        (re limit)
    imagConverges :
      Bishop.BishopConvergesTo
        (BishopSequence.SeriesOf (imagTerms terms))
        (im limit)

open ComplexSeriesConvergesTo public

complexSeriesLimitConvergence :
  (terms : Nat -> BishopComplex) ->
  (absolute : ComponentwiseAbsoluteSeriesConvergent terms) ->
  ComplexSeriesConvergesTo terms (complexSeriesLimit terms absolute)
complexSeriesLimitConvergence terms absolute =
  complex-series-converges-to
    (Bishop.bishopSeriesLimitConvergence
      (realTerms terms)
      (realAbsolute absolute))
    (Bishop.bishopSeriesLimitConvergence
      (imagTerms terms)
      (imagAbsolute absolute))

complexSeriesLimitUnique :
  (terms : Nat -> BishopComplex) ->
  (absolute : ComponentwiseAbsoluteSeriesConvergent terms) ->
  (other : BishopComplex) ->
  ComplexSeriesConvergesTo terms other ->
  complexSeriesLimit terms absolute ≈C other
complexSeriesLimitUnique terms absolute other otherConvergence =
  Bishop.bishopSeriesLimitUnique
    (realTerms terms)
    (realAbsolute absolute)
    (realConverges otherConvergence)
  ,
  Bishop.bishopSeriesLimitUnique
    (imagTerms terms)
    (imagAbsolute absolute)
    (imagConverges otherConvergence)
  where
  open import Data.Product using (_,_)
