{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE1DifferentiatedCovarianceExact where

------------------------------------------------------------------------
-- MARKED E1 AS DIFFERENTIATED EUCLIDEAN COVARIANCE.
--
-- Base continuum Schwinger O(4) covariance is already supplied on the selected
-- family by the existing symmetry-restoration lane.  For the stress insertion,
-- the only extra theorem needed is that differentiating the SAME covariant
-- source family commutes with the Euclidean action.
--
-- Abstractly:
--
--   F(g · phi) = F(phi)
--   D F(g · phi)[g · h] = D F(phi)[h]
--
-- hence the marked first variation transforms covariantly.
--
-- This module deliberately does not pretend the current R106 metric domain has
-- a vector-space O(4) action.  It works at the source-derivative level, where
-- Round109 already owns the completed stress functional.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)

record DifferentiatedEuclideanCovariance
    (Action BaseObservable StressMark Scalar : Set) : Set₁ where
  field
    actBase :
      Action → BaseObservable → BaseObservable

    actStress :
      Action → StressMark → StressMark

    baseExpectation :
      BaseObservable → Scalar

    markedDerivative :
      BaseObservable → StressMark → Scalar

    baseCovariant :
      ∀ action observable →
      baseExpectation (actBase action observable)
      ≡ baseExpectation observable

    -- This is the actual residual for marked E1:
    -- source differentiation is natural under the SAME Euclidean action.
    derivativeEquivariant :
      ∀ action observable mark →
      markedDerivative
        (actBase action observable)
        (actStress action mark)
      ≡
      markedDerivative observable mark

open DifferentiatedEuclideanCovariance public

markedFirstVariationCovariant :
  ∀ {Action BaseObservable StressMark Scalar}
    (dataSet :
      DifferentiatedEuclideanCovariance
        Action BaseObservable StressMark Scalar)
    action observable mark →
  markedDerivative dataSet
    (actBase dataSet action observable)
    (actStress dataSet action mark)
  ≡
  markedDerivative dataSet observable mark
markedFirstVariationCovariant dataSet =
  derivativeEquivariant dataSet

record RankTwoMarkedE1
    (Action BaseObservable StressMark Scalar : Set) : Set₁ where
  field
    differentiated :
      DifferentiatedEuclideanCovariance
        Action BaseObservable StressMark Scalar

    RankTwoStressMark : StressMark → Set

    selectedStressMark :
      StressMark

    selectedStressIsRankTwo :
      RankTwoStressMark selectedStressMark

open RankTwoMarkedE1 public

selectedRankTwoMarkedCovariance :
  ∀ {Action BaseObservable StressMark Scalar}
    (dataSet :
      RankTwoMarkedE1
        Action BaseObservable StressMark Scalar)
    action observable →
  markedDerivative (differentiated dataSet)
    (actBase (differentiated dataSet) action observable)
    (actStress (differentiated dataSet) action
      (selectedStressMark dataSet))
  ≡
  markedDerivative (differentiated dataSet)
    observable
    (selectedStressMark dataSet)
selectedRankTwoMarkedCovariance dataSet =
  markedFirstVariationCovariant
    (differentiated dataSet)

baseO4CovarianceNoLongerPartOfNovelMarkedE1 : Bool
baseO4CovarianceNoLongerPartOfNovelMarkedE1 = true

markedE1ResidualIsDerivativeEquivariance : Bool
markedE1ResidualIsDerivativeEquivariance = true
