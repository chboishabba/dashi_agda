module DASHI.Moonshine.OggSSPSmallCharacteristicDworkExplicitRootDepthNoGoExact where

------------------------------------------------------------------------
-- DWORK SMALL-PRIME EXPLICIT ROOT-DEPTH NO-GO
--
-- EXTERNAL SOURCE
--
-- Bernard Dwork, "p-adic cycles", Publ. Math. IHES 37 (1969), Section 7.
-- In the explicit p=2,3 treatment near the unique supersingular invariant
-- j_0=0, Dwork records a distinguished lifted root beta' with
--
--   ord(beta') = 8  for p=2,
--   ord(beta') = 3  for p=3.
--
-- Duncan--Swisher explicitly point readers to these stronger small-prime
-- bounds in Proposition 3.1.
--
-- DASHI COMPARISON
--
-- Those numbers are already present in the exact published Hauptmodul
-- baseline:
--
--   v_2(J_1 - J_4) = 8,
--   v_3(J_1 - J_9) = 3.
--
-- They are NOT the missing Monster residuals 10 and 2.
--
-- This is a numerical/source-calibrated no-go only.  It does not identify
-- Dwork's beta' with the prime-square Hauptmodul difference as the same
-- analytic object.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulTermBaselineExact as Baseline
import DASHI.Moonshine.OggSSPSmallCharacteristicFourthTermExtensionExact as Fourth
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Sourced Dwork root depths.
------------------------------------------------------------------------

dworkP2LiftedRootDepth : Nat
dworkP2LiftedRootDepth = 8

dworkP3LiftedRootDepth : Nat
dworkP3LiftedRootDepth = 3

------------------------------------------------------------------------
-- 2. They numerically coincide with the already-paid prime-square baselines.
------------------------------------------------------------------------

p2DworkDepthMatchesPrimeSquareBaseline :
  dworkP2LiftedRootDepth
  ≡ Baseline.baselineValuation
      Baseline.pTwo
      Baseline.primeSquareLevel
p2DworkDepthMatchesPrimeSquareBaseline = refl

p3DworkDepthMatchesPrimeSquareBaseline :
  dworkP3LiftedRootDepth
  ≡ Baseline.baselineValuation
      Baseline.pThree
      Baseline.primeSquareLevel
p3DworkDepthMatchesPrimeSquareBaseline = refl

------------------------------------------------------------------------
-- 3. They do not equal the exceptional fourth term.
------------------------------------------------------------------------

p2DworkDepthIsNotExceptionalFourthTerm :
  dworkP2LiftedRootDepth
  ≡ Fourth.exceptionalFourthTerm Baseline.pTwo
  ->
  ⊥
p2DworkDepthIsNotExceptionalFourthTerm ()

p3DworkDepthIsNotExceptionalFourthTerm :
  dworkP3LiftedRootDepth
  ≡ Fourth.exceptionalFourthTerm Baseline.pThree
  ->
  ⊥
p3DworkDepthIsNotExceptionalFourthTerm ()

------------------------------------------------------------------------
-- 4. Attribution / same-object firewalls.
------------------------------------------------------------------------

data DworkRootIsPrimeSquareHauptmodulDifference : Set where
data StrongerDworkBoundsConstructExceptionalFourthTerm : Set where
data DuncanSwisherAttributedFourthTermToDworkRoot : Set where

numericalMatchDoesNotIdentifyDworkRootWithHauptmodulDifference :
  DworkRootIsPrimeSquareHauptmodulDifference -> ⊥
numericalMatchDoesNotIdentifyDworkRootWithHauptmodulDifference ()

strongerDworkBoundsDoNotConstructFourthTerm :
  StrongerDworkBoundsConstructExceptionalFourthTerm -> ⊥
strongerDworkBoundsDoNotConstructFourthTerm ()

duncanSwisherNotCreditedWithDworkRootFourthTerm :
  DuncanSwisherAttributedFourthTermToDworkRoot -> ⊥
duncanSwisherNotCreditedWithDworkRootFourthTerm ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record DworkExplicitRootDepthNoGoBoundary : Set where
  constructor dwork-explicit-root-depth-no-go-boundary
  field
    p2DworkRootDepthEightSourced : Bool
    p3DworkRootDepthThreeSourced : Bool
    p2DepthMatchesPrimeSquareBaselineNumerically : Bool
    p3DepthMatchesPrimeSquareBaselineNumerically : Bool
    p2DepthMatchesExceptionalFourthTerm : Bool
    p3DepthMatchesExceptionalFourthTerm : Bool
    sameObjectIdentityClaimed : Bool
    attributionFirewallPreserved : Bool

canonicalDworkExplicitRootDepthNoGoBoundary :
  DworkExplicitRootDepthNoGoBoundary
canonicalDworkExplicitRootDepthNoGoBoundary =
  dwork-explicit-root-depth-no-go-boundary
    true true true true false false false true
