module DASHI.Analysis.NonArchimedeanPrimitiveTwistedAnchorRepairExact where

------------------------------------------------------------------------
-- REPAIRED LOCAL ANCHOR
--
-- Replace the monograph's ambiguous/full-operator expression
--
--   rho(L_2) = sqrt 2
--
-- by the source-owned primitive twisted-circle statement
--
--   r_tw(2) = sqrt 2.
--
-- Defining sigma_cyc := log_2 r_tw(2), the already-owned
-- `log2_sqrt_two = 1/2` theorem gives sigma_cyc = 1/2 exactly.
--
-- This repairs the local p=2 scaling coordinate but deliberately does not
-- identify it with the Archimedean/Prolate critical-line parameter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.NonArchimedeanCyclotomicSigmaHalfCompilerExact as Sigma

record PrimitiveTwistedAnchorInput : Set₁ where
  field
    sigmaData : Sigma.CyclotomicSigmaData
    amplitudeMagnitudeIsPrimitiveTwistedRadius : Bool
    continuousTransferSpectralRadiusTwoOwned : Bool
    sourceLog2SqrtTwoOwned : Bool

open PrimitiveTwistedAnchorInput public

repairedPrimitiveTwistedSigmaHalf :
  (input : PrimitiveTwistedAnchorInput) →
  Sigma.cyclotomicSigma (sigmaData input)
  ≡ Sigma.CyclotomicSigmaData.half (sigmaData input)
repairedPrimitiveTwistedSigmaHalf input =
  Sigma.cyclotomicSigmaIsHalf (sigmaData input)

record RepairedAnchorBoundary : Set where
  constructor repairedAnchorBoundary
  field
    usesFullTransferOperatorRadius : Bool
    usesPrimitiveTwistedCircleRadius : Bool
    yieldsLocalCyclotomicHalf : Bool
    yieldsProlateCriticalLineIdentification : Bool
    crossLaneCompatibilityStillRequired : Bool

canonicalRepairedAnchorBoundary : RepairedAnchorBoundary
canonicalRepairedAnchorBoundary =
  repairedAnchorBoundary false true true false true

localRepairDoesNotCloseCriticalLineWeld :
  RepairedAnchorBoundary.yieldsProlateCriticalLineIdentification
    canonicalRepairedAnchorBoundary
  ≡ false
localRepairDoesNotCloseCriticalLineWeld = refl
