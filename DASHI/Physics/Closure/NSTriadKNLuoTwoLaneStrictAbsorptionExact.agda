module DASHI.Physics.Closure.NSTriadKNLuoTwoLaneStrictAbsorptionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Michel Bony,
-- "Calcul symbolique et propagation des singularites pour les equations
-- aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Shin-ichi Inage,
-- "Conditional Regularity of the Three-Dimensional Navier-Stokes Equations
-- via High-High Triadic Absorption".
-- DOI: 10.20944/preprints202603.1591.v1.
-- Status: non-peer-reviewed preprint.
--
-- DASHI CONTRIBUTION
--
-- Lower/comparable interactions and the high-high lane are assembled with
-- one shared viscosity quantity.  Exact coefficient accounting proves
--
--   L <= eta_L V + R_L
--   H <= eta_H V + R_H
--   eta_L + eta_H <= eta < 1
--
-- imply
--
--   L + H <= eta V + R_L + R_H
--
-- and expose the strict remaining viscosity coefficient 1-eta.
--
-- This closes the finite terminal margin algebra.  It does not produce the
-- physical lower-lane or high-high estimates.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

record TwoLaneAbsorptionCell : Set where
  constructor twoLaneAbsorptionCell
  field
    lowerTransfer : ℚ
    highHighTransfer : ℚ
    viscosity : ℚ
    lowerResidual : ℚ
    highHighResidual : ℚ
    etaLower : ℚ
    etaHighHigh : ℚ
    etaTotal : ℚ

    viscosityNonnegative : 0ℚ ≤ viscosity
    oneMinusEtaTotalNonnegative : 0ℚ ≤ 1ℚ - etaTotal

    lowerAbsorption :
      lowerTransfer ≤ etaLower * viscosity + lowerResidual

    highHighAbsorption :
      highHighTransfer ≤ etaHighHigh * viscosity + highHighResidual

    coefficientBudget : etaLower + etaHighHigh ≤ etaTotal

open TwoLaneAbsorptionCell public

totalTransfer : TwoLaneAbsorptionCell → ℚ
totalTransfer cell = lowerTransfer cell + highHighTransfer cell

totalResidual : TwoLaneAbsorptionCell → ℚ
totalResidual cell = lowerResidual cell + highHighResidual cell

twoLaneAbsorption :
  ∀ cell →
  totalTransfer cell
  ≤ etaTotal cell * viscosity cell + totalResidual cell
twoLaneAbsorption cell =
  let
    laneSum :
      lowerTransfer cell + highHighTransfer cell
      ≤
      (etaLower cell * viscosity cell + lowerResidual cell)
      + (etaHighHigh cell * viscosity cell + highHighResidual cell)
    laneSum =
      ℚₚ.+-mono-≤
        (lowerAbsorption cell)
        (highHighAbsorption cell)

    grouped :
      (etaLower cell * viscosity cell + lowerResidual cell)
      + (etaHighHigh cell * viscosity cell + highHighResidual cell)
      ≡
      (etaLower cell + etaHighHigh cell) * viscosity cell
      + totalResidual cell
    grouped =
      solve
        ( etaLower cell
        ∷ etaHighHigh cell
        ∷ viscosity cell
        ∷ lowerResidual cell
        ∷ highHighResidual cell
        ∷ [])

    groupedBound :
      totalTransfer cell
      ≤
      (etaLower cell + etaHighHigh cell) * viscosity cell
      + totalResidual cell
    groupedBound =
      subst
        (λ right → totalTransfer cell ≤ right)
        grouped
        laneSum

    coefficientProductBound :
      (etaLower cell + etaHighHigh cell) * viscosity cell
      ≤ etaTotal cell * viscosity cell
    coefficientProductBound =
      let
        instance
          viscosityNN = nonNegative (viscosityNonnegative cell)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (viscosity cell)
        (coefficientBudget cell)

    withResidual :
      (etaLower cell + etaHighHigh cell) * viscosity cell
        + totalResidual cell
      ≤ etaTotal cell * viscosity cell + totalResidual cell
    withResidual =
      ℚₚ.+-mono-≤ coefficientProductBound ℚₚ.≤-refl
  in
  ℚₚ.≤-trans groupedBound withResidual

strictTwoLaneViscosityMargin :
  ∀ cell →
  (1ℚ - etaTotal cell) * viscosity cell
    + totalTransfer cell
  ≤ viscosity cell + totalResidual cell
strictTwoLaneViscosityMargin cell =
  let
    shifted =
      ℚₚ.+-mono-≤
        ℚₚ.≤-refl
        (twoLaneAbsorption cell)

    closed :
      (1ℚ - etaTotal cell) * viscosity cell
      + (etaTotal cell * viscosity cell + totalResidual cell)
      ≡ viscosity cell + totalResidual cell
    closed =
      solve
        ( etaTotal cell
        ∷ viscosity cell
        ∷ totalResidual cell
        ∷ [])
  in
  subst
    (λ right →
      (1ℚ - etaTotal cell) * viscosity cell
        + totalTransfer cell
      ≤ right)
    closed
    shifted

record TwoLaneProducerBoundary : Set where
  constructor twoLaneProducerBoundary
  field
    coefficientAssemblyClosed : Set
    physicalLowerLaneProduced : Set
    physicalHighHighLaneProduced : Set
    universalStrictCoefficientProduced : Set

canonicalTwoLaneProducerBoundary : TwoLaneProducerBoundary
canonicalTwoLaneProducerBoundary =
  twoLaneProducerBoundary
    ⊤
    ⊥
    ⊥
    ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
