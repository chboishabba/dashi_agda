module DASHI.Biology.IITLatticePrimePowerSourceBridgeExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Biology.IITCubeConcreteTorusImageExact as Cube
import DASHI.Biology.IITXORGridTwoStepDynamicsExact as BinaryGrid
import DASHI.Biology.IITXORGridAdversarialExact as Grid

------------------------------------------------------------------------
-- Existing-source theorem reuse, not a new finite-grid semantics:
--   * Binary 2x2 XOR grid: F² = 0 for EVERY state.
--   * Ternary 3x3 face B: B³ = -I (existing Cube.bop3Neg);
--     consequently B^6 = I and B³ is injective.
--
-- Distinct characteristic/size/dimension combinations have sharply
-- different long-time dynamics, even under the common 'sum of shifts'
-- syntax. The generic prime-power n=p^k Frobenius theorem for all n,d
-- is a mathematical result and a numerical-script target but is NOT
-- claimed to be Agda-kernel-proved by this finite cross-owner bridge.
------------------------------------------------------------------------

binary2x2Extinction :
  (state : Grid.Grid2x2) →
  Grid.gridStep (Grid.gridStep state)
  ≡ BinaryGrid.zeroGrid
binary2x2Extinction = BinaryGrid.twoStepNilpotence

ternaryFaceThreeStepsIsNegation :
  (state : Cube.Face9) →
  Cube.bop3 state ≡ Cube.negFace state
ternaryFaceThreeStepsIsNegation = Cube.bop3Neg

ternaryFaceSixStepsIsIdentity :
  (state : Cube.Face9) →
  Cube.bop3 (Cube.bop3 state) ≡ state
ternaryFaceSixStepsIsIdentity state =
  trans
    (Cube.bop3Neg (Cube.bop3 state))
    (trans
      (cong Cube.negFace (Cube.bop3Neg state))
      (Cube.negNegFace state))

ternaryFaceThreeStepsInjective :
  (a b : Cube.Face9) →
  Cube.bop3 a ≡ Cube.bop3 b →
  a ≡ b
ternaryFaceThreeStepsInjective a b equality =
  trans
    (sym (ternaryFaceSixStepsIsIdentity a))
    (trans
      (cong Cube.bop3 equality)
      (ternaryFaceSixStepsIsIdentity b))

record IITLatticePrimePowerSourceBoundary : Set where
  constructor iit-lattice-prime-power-source-boundary
  field
    binaryTwoStepNilpotenceReused : Bool
    ternaryThreeStepNegationReused : Bool
    ternarySixStepIdentityDerived : Bool
    ternaryStepInjectivityDerived : Bool
    arbitrarySideLengthNilpotenceClaimed : Bool
    historicalLargeGridIITPhiCalculatedHere : Bool
    actualBiologicalOrPhenomenalCorrespondenceClaimed : Bool
    genericPrimePowerFrobeniusTheoremKernelCertifiedHere : Bool

canonicalPrimePowerSourceBoundary : IITLatticePrimePowerSourceBoundary
canonicalPrimePowerSourceBoundary =
  iit-lattice-prime-power-source-boundary
    true true true true false false false false
