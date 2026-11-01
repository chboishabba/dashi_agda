module DASHI.Interop.P13PrimeLaneStage12ActionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.StageQuotient as StageQuotient
import DASHI.Foundations.P13UnitGroupC12Witness as P13C12
import DASHI.Foundations.PrimeLaneUnitActionQuotient as Quotient
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Interop.PrimeLaneStage12ActionAdapter as Adapter
import DASHI.Interop.PrimeSuccessorWitness as Successor
import DASHI.Physics.Closure.P13Stage12C12Regression as Regression

record P13PrimeLaneStage12ActionBridgeAuthorityBits : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    promotedStageSpine : Bool
    promotedStageSpineIsFalse : promotedStageSpine ≡ false
    promotedPrimeUniversal : Bool
    promotedPrimeUniversalIsFalse : promotedPrimeUniversal ≡ false
    promotedPhysicsAuthority : Bool
    promotedPhysicsAuthorityIsFalse : promotedPhysicsAuthority ≡ false

canonicalP13PrimeLaneStage12ActionBridgeAuthorityBits :
  P13PrimeLaneStage12ActionBridgeAuthorityBits
canonicalP13PrimeLaneStage12ActionBridgeAuthorityBits =
  record
    { candidateOnly = true
    ; candidateOnlyIsTrue = refl
    ; promotedStageSpine = false
    ; promotedStageSpineIsFalse = refl
    ; promotedPrimeUniversal = false
    ; promotedPrimeUniversalIsFalse = refl
    ; promotedPhysicsAuthority = false
    ; promotedPhysicsAuthorityIsFalse = refl
    }

record P13PrimeLaneStage12ActionBridge : Set where
  constructor mkP13PrimeLaneStage12ActionBridge
  field
    bridgeLabel : String
    stage12Adapter :
      Adapter.PrimeLaneStage12ActionAdapter
    stage12AdapterIsCanonical :
      stage12Adapter ≡ Adapter.canonicalP13PrimeLaneStage12ActionAdapter
    quotientSurfaceIsCanonical :
      Adapter.quotientSurface stage12Adapter
      ≡
      Quotient.p13C12PrimeLaneUnitActionQuotientSurface
    successorWitness :
      Successor.PrimeSuccessorWitness
    successorWitnessIsCanonical :
      successorWitness ≡ Successor.canonicalP13PrimeSuccessorWitness
    stageWindowWitness :
      Successor.StageSuccessorWitness
    stageWindowWitnessIsCanonical :
      stageWindowWitness ≡ Successor.canonicalStage12SuccessorWitness
    unitGroupWitness :
      P13C12.P13UnitGroupC12Witness
    unitGroupWitnessIsCanonical :
      unitGroupWitness ≡ P13C12.canonicalP13UnitGroupC12Witness
    p13Regression :
      Regression.P13Stage12C12Regression
    p13RegressionIsCanonical :
      p13Regression ≡ Regression.canonicalP13Stage12C12Regression
    adapterSuccessorWitness :
      Adapter.successorWitness stage12Adapter ≡ successorWitness
    adapterStageWindowWitness :
      Adapter.stageWindowWitness stage12Adapter ≡ stageWindowWitness
    regressionUnitGroupWitness :
      Regression.unitGroupWitness p13Regression ≡ unitGroupWitness
    regressionStage12Witnessed :
      Regression.stage12Witnessed p13Regression ≡ refl
    regressionStage1Identity :
      Regression.stage1Identity p13Regression ≡ refl
    regressionStage0UnitOrder :
      Regression.stage0UnitOrder p13Regression ≡ refl
    adapterStageIdentityPointIsAtlas1 :
      Adapter.stageIdentityPoint stage12Adapter ≡ Atlas.atlas-1
    adapterUnitOrderStagePointIsAtlas0 :
      Adapter.unitOrderStagePoint stage12Adapter ≡ Atlas.atlas-0
    adapterCarryDepthSeamPointIsAtlas11 :
      Adapter.carryDepthSeamPoint stage12Adapter ≡ Atlas.atlas-11
    adapterCarryDepthSeam :
      StageQuotient.Stage12FibreSurface.carry-depth
        (Adapter.stage12FibreSurface stage12Adapter)
        (Adapter.carryDepthSeamPoint stage12Adapter)
      ≡
      Atlas.rev-2
    bridgeAuthorityBits :
      P13PrimeLaneStage12ActionBridgeAuthorityBits
    bridgeNotes :
      List String

open P13PrimeLaneStage12ActionBridge public
open P13PrimeLaneStage12ActionBridgeAuthorityBits public

canonicalP13PrimeLaneStage12ActionBridge :
  P13PrimeLaneStage12ActionBridge
canonicalP13PrimeLaneStage12ActionBridge =
  mkP13PrimeLaneStage12ActionBridge
    "p13-stage12-adapter-bridge"
    Adapter.canonicalP13PrimeLaneStage12ActionAdapter
    refl
    refl
    Successor.canonicalP13PrimeSuccessorWitness
    refl
    Successor.canonicalStage12SuccessorWitness
    refl
    P13C12.canonicalP13UnitGroupC12Witness
    refl
    Regression.canonicalP13Stage12C12Regression
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalP13PrimeLaneStage12ActionBridgeAuthorityBits
    ( "The Stage12 adapter is the shared public carrier for the full 12 -> 13 closure row."
    ∷ "The p13 successor witness explains the +1 move from the Stage12 witness-space into the p13 prime lane."
    ∷ "The p13 regression remains local, while the adapter keeps the closure witness under the same global Stage12 spine used by p7 and p11."
    ∷ []
    )
