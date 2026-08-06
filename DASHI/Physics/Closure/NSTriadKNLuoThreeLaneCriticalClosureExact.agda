module DASHI.Physics.Closure.NSTriadKNLuoThreeLaneCriticalClosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- DASHI CONTRIBUTION
--
-- This module closes the exact K13--K14 coefficient algebra for three
-- independently produced nonlinear lanes:
--
--   goodHH <= etaGood V + RGood,
--   badHH  <= etaBad  V + RBad,
--   lower  <= etaLow  V + RLow.
--
-- Their sum is controlled with the literal coefficient
--
--   etaTotal = etaGood + etaBad + etaLow,
--
-- and a finite critical energy balance
--
--   Xout + V <= Xin + totalTransfer
--
-- yields
--
--   Xout + (1-etaTotal)V <= Xin + totalResidual.
--
-- The theorem performs the signed absorption exactly.  It does not produce
-- any of the three physical lane estimates or their strict numerical margin.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

record ThreeLaneCriticalData : Set where
  constructor threeLaneCriticalData
  field
    viscosity goodTransfer badTransfer lowerTransfer : ℚ
    goodResidual badResidual lowerResidual : ℚ
    etaGood etaBad etaLower : ℚ

    goodAbsorption :
      goodTransfer ≤ etaGood * viscosity + goodResidual

    badAbsorption :
      badTransfer ≤ etaBad * viscosity + badResidual

    lowerAbsorption :
      lowerTransfer ≤ etaLower * viscosity + lowerResidual

open ThreeLaneCriticalData public

etaTotal : ThreeLaneCriticalData → ℚ
etaTotal dataSet = etaGood dataSet + etaBad dataSet + etaLower dataSet

totalTransfer : ThreeLaneCriticalData → ℚ
totalTransfer dataSet =
  goodTransfer dataSet + badTransfer dataSet + lowerTransfer dataSet

totalResidual : ThreeLaneCriticalData → ℚ
totalResidual dataSet =
  goodResidual dataSet + badResidual dataSet + lowerResidual dataSet

threeLaneAbsorption :
  ∀ dataSet →
  totalTransfer dataSet
  ≤ etaTotal dataSet * viscosity dataSet + totalResidual dataSet
threeLaneAbsorption dataSet =
  let
    summed =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (goodAbsorption dataSet)
          (badAbsorption dataSet))
        (lowerAbsorption dataSet)

    rightMeaning :
      (etaGood dataSet * viscosity dataSet + goodResidual dataSet)
      + (etaBad dataSet * viscosity dataSet + badResidual dataSet)
      + (etaLower dataSet * viscosity dataSet + lowerResidual dataSet)
      ≡
      etaTotal dataSet * viscosity dataSet + totalResidual dataSet
    rightMeaning =
      solve
        ( etaGood dataSet ∷ etaBad dataSet ∷ etaLower dataSet
        ∷ viscosity dataSet
        ∷ goodResidual dataSet ∷ badResidual dataSet
        ∷ lowerResidual dataSet ∷ [])
  in
  subst
    (λ upper → totalTransfer dataSet ≤ upper)
    rightMeaning
    summed

record FiniteCriticalEnergyBalance : Set where
  constructor finiteCriticalEnergyBalance
  field
    laneData : ThreeLaneCriticalData
    energyIn energyOut : ℚ
    balance :
      energyOut + viscosity laneData
      ≤ energyIn + totalTransfer laneData

open FiniteCriticalEnergyBalance public

remainingViscosity : FiniteCriticalEnergyBalance → ℚ
remainingViscosity balanceData =
  1ℚ - etaTotal (laneData balanceData)

strictFiniteCriticalEstimate :
  ∀ balanceData →
  energyOut balanceData
    + remainingViscosity balanceData
      * viscosity (laneData balanceData)
  ≤
  energyIn balanceData
    + totalResidual (laneData balanceData)
strictFiniteCriticalEstimate balanceData =
  let
    dataSet = laneData balanceData

    transferBound = threeLaneAbsorption dataSet

    withEnergy :
      energyIn balanceData + totalTransfer dataSet
      ≤
      energyIn balanceData
        + (etaTotal dataSet * viscosity dataSet
          + totalResidual dataSet)
    withEnergy =
      ℚₚ.+-monoʳ-≤ (energyIn balanceData) transferBound

    assembled :
      energyOut balanceData + viscosity dataSet
      ≤
      energyIn balanceData
        + (etaTotal dataSet * viscosity dataSet
          + totalResidual dataSet)
    assembled = ℚₚ.≤-trans (balance balanceData) withEnergy

    shift = - (etaTotal dataSet * viscosity dataSet)
    shifted = ℚₚ.+-monoʳ-≤ shift assembled

    leftMeaning :
      (energyOut balanceData + viscosity dataSet) + shift
      ≡
      energyOut balanceData
        + remainingViscosity balanceData * viscosity dataSet
    leftMeaning =
      solve
        ( energyOut balanceData
        ∷ viscosity dataSet
        ∷ etaTotal dataSet
        ∷ [])

    rightMeaning :
      (energyIn balanceData
        + (etaTotal dataSet * viscosity dataSet
          + totalResidual dataSet))
      + shift
      ≡ energyIn balanceData + totalResidual dataSet
    rightMeaning =
      solve
        ( energyIn balanceData
        ∷ viscosity dataSet
        ∷ etaTotal dataSet
        ∷ totalResidual dataSet
        ∷ [])
  in
  subst
    (λ left → left ≤ energyIn balanceData + totalResidual dataSet)
    leftMeaning
    (subst
      (λ right →
        (energyOut balanceData + viscosity dataSet) + shift ≤ right)
      rightMeaning
      shifted)

record StrictThreeLaneCertificate (dataSet : ThreeLaneCriticalData) : Set where
  constructor strictThreeLaneCertificate
  field
    etaTotalNonnegative : 0ℚ ≤ etaTotal dataSet
    remainingViscosityNonnegative : 0ℚ ≤ 1ℚ - etaTotal dataSet

open StrictThreeLaneCertificate public

record ThreeLaneAuthorityBoundary : Set where
  constructor threeLaneAuthorityBoundary
  field
    exactThreeLaneSummationProved : Set
    exactFiniteCriticalEstimateProved : Set
    goodLaneProducedByNavierStokes : Set
    badLaneProducedByNavierStokes : Set
    lowerLaneProducedByNavierStokes : Set
    strictTotalCoefficientProduced : Set

canonicalThreeLaneAuthorityBoundary : ThreeLaneAuthorityBoundary
canonicalThreeLaneAuthorityBoundary =
  threeLaneAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
