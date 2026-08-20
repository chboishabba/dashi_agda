module DASHI.Physics.Closure.NSTriadKNComTwoLevelSchurRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Issai Schur.
-- Classical row/column test for matrix/integral operators; no DOI is assigned
-- to the historical theorem used here.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Keep the two Com Schur problems proof-relevantly distinct.
--
-- INTERNAL: for one fixed shell block T_(q,r), Plancherel separates distinct
-- output modes k, while resonant input pairs sharing k must be controlled by a
-- genuine within-output-fibre row/column estimate.  Its preferred conclusion is
-- a WHOLE BLOCK operator norm bound.
--
-- EXTERNAL: once those whole block norms are available and support has width
-- one, the shell-level positive majorant sees only three blocks.  If the
-- internal theorem supplies
--
--   ||T_(q,q)|| <= 17/64,
--   ||T_(q,q+1)||, ||T_(q+1,q)|| <= 65/512,
--
-- the external row remains exactly 133/256.  No Fourier shell cardinality or
-- incidence multiplicity enters this second step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active
import DASHI.Physics.Closure.NSTriadKNComThreeChannelRowMassRound48Exact as Row

-- The literal internal Schur theorem should ultimately instantiate this record
-- from the physical Fourier kernel on one output fibre.  We deliberately keep
-- the squared operator conclusion division/root-free.
record WithinOutputFibreSchurCertificate : Set where
  field
    rowMass columnMass squaredBlockNorm : ℚ
    rowMassNonnegative : 0ℚ ≤ rowMass
    columnMassNonnegative : 0ℚ ≤ columnMass
    squaredBlockNormNonnegative : 0ℚ ≤ squaredBlockNorm
    squaredBlockNormBelowSchurProduct :
      squaredBlockNorm ≤ rowMass * columnMass

open WithinOutputFibreSchurCertificate public

record PhysicalWholeShellBlockBounds : Set where
  field
    sameShellBlockNorm : Nat → ℚ
    forwardAdjacentBlockNorm : Nat → ℚ
    backwardAdjacentBlockNorm : Nat → ℚ

    sameShellBlockNormNonnegative : ∀ q →
      0ℚ ≤ sameShellBlockNorm q
    forwardAdjacentBlockNormNonnegative : ∀ q →
      0ℚ ≤ forwardAdjacentBlockNorm q
    backwardAdjacentBlockNormNonnegative : ∀ q →
      0ℚ ≤ backwardAdjacentBlockNorm q

    sameShellWholeBlockBound : ∀ q →
      sameShellBlockNorm q ≤ Active.sameShellTarget
    forwardAdjacentWholeBlockBound : ∀ q →
      forwardAdjacentBlockNorm q ≤ Active.adjacentShellTarget
    backwardAdjacentWholeBlockBound : ∀ q →
      backwardAdjacentBlockNorm q ≤ Active.adjacentShellTarget

open PhysicalWholeShellBlockBounds public

externalShellRowMass : PhysicalWholeShellBlockBounds → Nat → ℚ
externalShellRowMass physical q =
  sameShellBlockNorm physical q
  + forwardAdjacentBlockNorm physical q
  + backwardAdjacentBlockNorm physical q

externalShellRowMassBelow133Over256 :
  (physical : PhysicalWholeShellBlockBounds) →
  ∀ q → externalShellRowMass physical q ≤ Row.threeChannelTarget
externalShellRowMassBelow133Over256 physical q =
  let
    summed :
      externalShellRowMass physical q
      ≤ Active.sameShellTarget
        + Active.adjacentShellTarget
        + Active.adjacentShellTarget
    summed =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (sameShellWholeBlockBound physical q)
          (forwardAdjacentWholeBlockBound physical q))
        (backwardAdjacentWholeBlockBound physical q)
  in
  subst
    (externalShellRowMass physical q ≤_)
    Row.threeChannelTargetExact
    summed

-- The external shell arithmetic is already finished.  All remaining analytic
-- alpha is therefore explicitly located in construction of the whole block
-- bounds above, ideally by a within-output-fibre Schur/Cotlar estimate.
internalFibreSchurStillPhysical : Bool
internalFibreSchurStillPhysical = true

externalBandwidthOneShellSchurFinished : Bool
externalBandwidthOneShellSchurFinished = true

rawShellCardinalityMustNotEnterExternalSchur : Bool
rawShellCardinalityMustNotEnterExternalSchur = true

externalBandwidthOneShellSchurFinishedIsTrue :
  externalBandwidthOneShellSchurFinished ≡ true
externalBandwidthOneShellSchurFinishedIsTrue = refl
