module DASHI.Core.StructuredResidualProductExact where

------------------------------------------------------------------------
-- STRUCTURED RESIDUALS BEFORE GLOBAL SCALARISATION
--
-- Cross-project lesson: curvature/fabric defects, semantic ambiguity/source
-- conflict, and environmental conservation/calibration residuals are different
-- coordinates.  A global sum can preserve total magnitude while erasing which
-- coordinate carries the burden.  Consumer-local safety therefore needs the
-- structured carrier (or a proved descent theorem), not merely a scalar total.
--
-- This is the finite two-coordinate kernel of the broader tensorising/local
-- residual principle already used elsewhere in DASHI.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel

Residual2 : Set
Residual2 = Nat × Nat

scalarTotal : Residual2 → Nat
scalarTotal residual = proj₁ residual + proj₂ residual

firstCoordinate : Residual2 → Nat
firstCoordinate = proj₁

secondCoordinate : Residual2 → Nat
secondCoordinate = proj₂

------------------------------------------------------------------------
-- Exact non-descent witness:
--
--   (1,0) and (0,1) have the same global total 1,
--   but a consumer of the first coordinate distinguishes them.
--
-- Hence no function of the scalar sum alone can recover every coordinate-local
-- claim.  This is stronger than saying the scalar is "less informative": it is
-- an explicit quotient-descent obstruction.
------------------------------------------------------------------------

one : Nat
one = suc zero

scalarTotalLosesFirstCoordinate :
  Kernel.ConsumerDescentDefect scalarTotal firstCoordinate
scalarTotalLosesFirstCoordinate =
  Kernel.consumerDescentDefect
    (one , zero)
    (zero , one)
    refl
    impossible
  where
    impossible : one ≡ zero → ⊥
    impossible ()

scalarTotalLosesSecondCoordinate :
  Kernel.ConsumerDescentDefect scalarTotal secondCoordinate
scalarTotalLosesSecondCoordinate =
  Kernel.consumerDescentDefect
    (one , zero)
    (zero , one)
    refl
    impossible
  where
    impossible : zero ≡ one → ⊥
    impossible ()

record StructuredResidualBoundary : Set where
  constructor structuredResidualBoundary
  field
    equalGlobalTotalNeedNotMeanEqualLocalResidual : Bool
    coordinateConsumersNeedStructuredCarrierOrDescentProof : Bool
    residualCoordinatesNeedNotShareScientificUnits : Bool
    globalScalarisationIsAConsumerRelativeClaim : Bool

canonicalStructuredResidualBoundary : StructuredResidualBoundary
canonicalStructuredResidualBoundary =
  structuredResidualBoundary true true true true
