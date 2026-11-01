module DASHI.Physics.Closure.NSTriadKNLuoIntegratedHighHighResidenceExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Shin-ichi Inage.
-- Title: "Conditional Regularity of the Three-Dimensional Navier-Stokes
-- Equations via High-High Triadic Absorption".
-- Preprint DOI: 10.20944/preprints202603.1591.v1.
-- Status: non-peer-reviewed preprint.
--
-- Author: Shin-ichi Inage.
-- Title: "Structural Reduction Framework and Residence-Time Compression of
-- Coherent Same-Scale Triadic Interactions in the 3D Navier-Stokes Equations".
-- DOI: 10.3390/math14091410.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- PURPOSE
-- Prove the finite integrated high-high absorption theorem suggested by the
-- source architecture.  Good coherent time cells are absorbed pointwise into
-- eta times viscosity plus a residual.  Bad cells are controlled only by an
-- amplitude cap and their total residence charge.  Finite time summation then
-- yields
--
--   integral HH
--     <= eta * integral V + integral residual + bad residual.
--
-- This is strictly weaker than a pointwise high-high theorem and strictly
-- stronger than a bare directional-defect identity.  The proof below performs
-- the duration-weighted summation and residence compression explicitly.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record ResidenceParameters : Set where
  constructor residence-parameters
  field
    eta badAmplitudeCap : ℚ
    etaNonnegative : 0ℚ ≤ eta
    badAmplitudeCapNonnegative : 0ℚ ≤ badAmplitudeCap

open ResidenceParameters public

record ResidenceCell (parameter : ResidenceParameters) : Set where
  constructor residence-cell
  field
    duration goodTransfer badTransfer viscous residual badCharge : ℚ

    durationNonnegative : 0ℚ ≤ duration
    goodTransferNonnegative : 0ℚ ≤ goodTransfer
    badTransferNonnegative : 0ℚ ≤ badTransfer
    viscousNonnegative : 0ℚ ≤ viscous
    residualNonnegative : 0ℚ ≤ residual
    badChargeNonnegative : 0ℚ ≤ badCharge

    goodPointwiseAbsorption :
      goodTransfer
      ≤ eta parameter * viscous + residual

    badPointwiseAmplitude :
      badTransfer
      ≤ badAmplitudeCap parameter * badCharge

open ResidenceCell public

durationTimesNonnegative :
  ∀ {parameter}
    (cell : ResidenceCell parameter)
    (value : ℚ) →
  0ℚ ≤ value →
  0ℚ ≤ duration cell * value
durationTimesNonnegative cell value valueNonnegative =
  let
    instance
      durationNN = nonNegative (durationNonnegative cell)
      valueNN = nonNegative valueNonnegative
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg (duration cell) value
  in
  ℚₚ.nonNegative⁻¹ (duration cell * value)

localGoodIntegratedAbsorption :
  ∀ {parameter}
    (cell : ResidenceCell parameter) →
  duration cell * goodTransfer cell
  ≤
  eta parameter * (duration cell * viscous cell)
  + duration cell * residual cell
localGoodIntegratedAbsorption {parameter} cell =
  let
    scaled :
      duration cell * goodTransfer cell
      ≤ duration cell
        * (eta parameter * viscous cell + residual cell)
    scaled =
      L2.nonnegativeProductMonotone
        (durationNonnegative cell)
        (goodTransferNonnegative cell)
        (durationNonnegative cell)
        (L2.addNonnegative
          productNonnegative
          (residualNonnegative cell))
        ℚₚ.≤-refl
        (goodPointwiseAbsorption cell)

    factorized :
      duration cell
        * (eta parameter * viscous cell + residual cell)
      ≡
      eta parameter * (duration cell * viscous cell)
      + duration cell * residual cell
    factorized =
      solve
        ( duration cell
        ∷ eta parameter
        ∷ viscous cell
        ∷ residual cell
        ∷ [])
  in
  subst
    (λ upper → duration cell * goodTransfer cell ≤ upper)
    factorized
    scaled
  where
    productNonnegative :
      0ℚ ≤ eta parameter * viscous cell
    productNonnegative =
      let
        instance
          etaNN = nonNegative (etaNonnegative parameter)
          viscousNN = nonNegative (viscousNonnegative cell)
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (eta parameter)
              (viscous cell)
      in
      ℚₚ.nonNegative⁻¹
        (eta parameter * viscous cell)

localBadIntegratedResidence :
  ∀ {parameter}
    (cell : ResidenceCell parameter) →
  duration cell * badTransfer cell
  ≤ badAmplitudeCap parameter
    * (duration cell * badCharge cell)
localBadIntegratedResidence {parameter} cell =
  let
    scaled :
      duration cell * badTransfer cell
      ≤ duration cell
        * (badAmplitudeCap parameter * badCharge cell)
    scaled =
      L2.nonnegativeProductMonotone
        (durationNonnegative cell)
        (badTransferNonnegative cell)
        (durationNonnegative cell)
        badProductNonnegative
        ℚₚ.≤-refl
        (badPointwiseAmplitude cell)

    reassociated :
      duration cell
        * (badAmplitudeCap parameter * badCharge cell)
      ≡ badAmplitudeCap parameter
        * (duration cell * badCharge cell)
    reassociated =
      solve
        ( duration cell
        ∷ badAmplitudeCap parameter
        ∷ badCharge cell
        ∷ [])
  in
  subst
    (λ upper → duration cell * badTransfer cell ≤ upper)
    reassociated
    scaled
  where
    badProductNonnegative :
      0ℚ ≤ badAmplitudeCap parameter * badCharge cell
    badProductNonnegative =
      let
        instance
          capNN =
            nonNegative (badAmplitudeCapNonnegative parameter)
          chargeNN =
            nonNegative (badChargeNonnegative cell)
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (badAmplitudeCap parameter)
              (badCharge cell)
      in
      ℚₚ.nonNegative⁻¹
        (badAmplitudeCap parameter * badCharge cell)

integratedGoodTransfer :
  (parameter : ResidenceParameters) →
  List (ResidenceCell parameter) →
  ℚ
integratedGoodTransfer parameter [] = 0ℚ
integratedGoodTransfer parameter (cell ∷ cells) =
  duration cell * goodTransfer cell
  + integratedGoodTransfer parameter cells

integratedBadTransfer :
  (parameter : ResidenceParameters) →
  List (ResidenceCell parameter) →
  ℚ
integratedBadTransfer parameter [] = 0ℚ
integratedBadTransfer parameter (cell ∷ cells) =
  duration cell * badTransfer cell
  + integratedBadTransfer parameter cells

integratedViscosity :
  (parameter : ResidenceParameters) →
  List (ResidenceCell parameter) →
  ℚ
integratedViscosity parameter [] = 0ℚ
integratedViscosity parameter (cell ∷ cells) =
  duration cell * viscous cell
  + integratedViscosity parameter cells

integratedResidual :
  (parameter : ResidenceParameters) →
  List (ResidenceCell parameter) →
  ℚ
integratedResidual parameter [] = 0ℚ
integratedResidual parameter (cell ∷ cells) =
  duration cell * residual cell
  + integratedResidual parameter cells

badResidenceCharge :
  (parameter : ResidenceParameters) →
  List (ResidenceCell parameter) →
  ℚ
badResidenceCharge parameter [] = 0ℚ
badResidenceCharge parameter (cell ∷ cells) =
  duration cell * badCharge cell
  + badResidenceCharge parameter cells

integratedGoodAbsorption :
  (parameter : ResidenceParameters) →
  (cells : List (ResidenceCell parameter)) →
  integratedGoodTransfer parameter cells
  ≤ eta parameter * integratedViscosity parameter cells
    + integratedResidual parameter cells
integratedGoodAbsorption parameter [] = ℚₚ.≤-refl
integratedGoodAbsorption parameter (cell ∷ cells) =
  let
    local = localGoodIntegratedAbsorption cell
    tail = integratedGoodAbsorption parameter cells
    summed = ℚₚ.+-mono-≤ local tail

    rearranged :
      ( eta parameter * (duration cell * viscous cell)
        + duration cell * residual cell
      )
      +
      ( eta parameter * integratedViscosity parameter cells
        + integratedResidual parameter cells
      )
      ≡
      eta parameter
        * (duration cell * viscous cell
          + integratedViscosity parameter cells)
      +
      (duration cell * residual cell
        + integratedResidual parameter cells)
    rearranged =
      solve
        ( eta parameter
        ∷ duration cell
        ∷ viscous cell
        ∷ residual cell
        ∷ integratedViscosity parameter cells
        ∷ integratedResidual parameter cells
        ∷ [])
  in
  subst
    (λ upper →
      duration cell * goodTransfer cell
      + integratedGoodTransfer parameter cells
      ≤ upper)
    rearranged
    summed

integratedBadResidenceBound :
  (parameter : ResidenceParameters) →
  (cells : List (ResidenceCell parameter)) →
  integratedBadTransfer parameter cells
  ≤ badAmplitudeCap parameter * badResidenceCharge parameter cells
integratedBadResidenceBound parameter [] = ℚₚ.≤-refl
integratedBadResidenceBound parameter (cell ∷ cells) =
  let
    local = localBadIntegratedResidence cell
    tail = integratedBadResidenceBound parameter cells
    summed = ℚₚ.+-mono-≤ local tail

    factorized :
      badAmplitudeCap parameter
        * (duration cell * badCharge cell)
      + badAmplitudeCap parameter
        * badResidenceCharge parameter cells
      ≡
      badAmplitudeCap parameter
        * ( duration cell * badCharge cell
          + badResidenceCharge parameter cells)
    factorized =
      solve
        ( badAmplitudeCap parameter
        ∷ duration cell
        ∷ badCharge cell
        ∷ badResidenceCharge parameter cells
        ∷ [])
  in
  subst
    (λ upper →
      duration cell * badTransfer cell
      + integratedBadTransfer parameter cells
      ≤ upper)
    factorized
    summed

record IntegratedResidenceBudget : Set₁ where
  constructor integrated-residence-budget
  field
    parameter : ResidenceParameters
    cells : List (ResidenceCell parameter)
    badResidual : ℚ
    badResidualNonnegative : 0ℚ ≤ badResidual
    residenceCompression :
      badAmplitudeCap parameter
        * badResidenceCharge parameter cells
      ≤ badResidual

open IntegratedResidenceBudget public

integratedHighHighTransfer :
  (budget : IntegratedResidenceBudget) → ℚ
integratedHighHighTransfer budget =
  integratedGoodTransfer
    (parameter budget) (cells budget)
  + integratedBadTransfer
    (parameter budget) (cells budget)

integratedHighHighAbsorption :
  (budget : IntegratedResidenceBudget) →
  integratedHighHighTransfer budget
  ≤
  eta (parameter budget)
    * integratedViscosity
      (parameter budget) (cells budget)
  +
  ( integratedResidual
      (parameter budget) (cells budget)
    + badResidual budget
  )
integratedHighHighAbsorption budget =
  let
    good =
      integratedGoodAbsorption
        (parameter budget) (cells budget)

    badToResidence =
      integratedBadResidenceBound
        (parameter budget) (cells budget)

    bad =
      ℚₚ.≤-trans
        badToResidence
        (residenceCompression budget)

    summed = ℚₚ.+-mono-≤ good bad

    rearranged :
      ( eta (parameter budget)
          * integratedViscosity
            (parameter budget) (cells budget)
        + integratedResidual
            (parameter budget) (cells budget)
      )
      + badResidual budget
      ≡
      eta (parameter budget)
        * integratedViscosity
          (parameter budget) (cells budget)
      +
      ( integratedResidual
          (parameter budget) (cells budget)
        + badResidual budget
      )
    rearranged =
      solve
        ( eta (parameter budget)
        ∷ integratedViscosity
            (parameter budget) (cells budget)
        ∷ integratedResidual
            (parameter budget) (cells budget)
        ∷ badResidual budget
        ∷ [])
  in
  subst
    (λ upper → integratedHighHighTransfer budget ≤ upper)
    rearranged
    summed
