module DASHI.Interop.P11PrimeLaneStage12ActionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.StageQuotient as StageQuotient
import DASHI.Foundations.P11UnitGroupC10Witness as P11C10
import DASHI.Foundations.PrimeLaneUnitActionQuotient as Quotient
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Interop.PrimeLaneStage12ActionAdapter as Adapter
import DASHI.Interop.PrimeSuccessorWitness as Successor
import DASHI.Physics.Closure.P11Stage11C10Regression as Regression

record P11PrimeLaneStage12ActionBridgeAuthorityBits : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    promotedStageSpine : Bool
    promotedStageSpineIsFalse : promotedStageSpine ≡ false
    promotedPrimeUniversal : Bool
    promotedPrimeUniversalIsFalse : promotedPrimeUniversal ≡ false
    promotedPhysicsAuthority : Bool
    promotedPhysicsAuthorityIsFalse : promotedPhysicsAuthority ≡ false

canonicalP11PrimeLaneStage12ActionBridgeAuthorityBits :
  P11PrimeLaneStage12ActionBridgeAuthorityBits
canonicalP11PrimeLaneStage12ActionBridgeAuthorityBits =
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

record P11PrimeLaneStage12ActionBridge : Set where
  constructor mkP11PrimeLaneStage12ActionBridge
  field
    bridgeLabel : String
    stage12Adapter :
      Adapter.PrimeLaneStage12ActionAdapter
    stage12AdapterIsCanonical :
      stage12Adapter ≡ Adapter.canonicalP11PrimeLaneStage12ActionAdapter
    quotientSurfaceIsCanonical :
      Adapter.quotientSurface stage12Adapter
      ≡
      Quotient.p11C10PrimeLaneUnitActionQuotientSurface
    successorWitness :
      Successor.PrimeSuccessorWitness
    successorWitnessIsCanonical :
      successorWitness ≡ Successor.canonicalP11PrimeSuccessorWitness
    stageWindowWitness :
      Successor.StageSuccessorWitness
    stageWindowWitnessIsCanonical :
      stageWindowWitness ≡ Successor.canonicalStage10SuccessorWitness
    unitGroupWitness :
      P11C10.P11UnitGroupC10Witness
    unitGroupWitnessIsCanonical :
      unitGroupWitness ≡ P11C10.canonicalP11UnitGroupC10Witness
    p11Regression :
      Regression.P11Stage11C10Regression
    p11RegressionIsCanonical :
      p11Regression ≡ Regression.canonicalP11Stage11C10Regression
    adapterSuccessorWitness :
      Adapter.successorWitness stage12Adapter ≡ successorWitness
    adapterStageWindowWitness :
      Adapter.stageWindowWitness stage12Adapter ≡ stageWindowWitness
    regressionUnitGroupWitness :
      Regression.unitGroupWitness p11Regression ≡ unitGroupWitness
    regressionStage11Identity :
      Regression.stage11Identity p11Regression ≡ refl
    regressionStage10UnitOrder :
      Regression.stage10UnitOrder p11Regression ≡ refl
    adapterStageIdentityPointIsAtlas11 :
      Adapter.stageIdentityPoint stage12Adapter ≡ Atlas.atlas-11
    adapterUnitOrderStagePointIsAtlas10 :
      Adapter.unitOrderStagePoint stage12Adapter ≡ Atlas.atlas-10
    adapterCarryDepthSeamPointIsAtlas11 :
      Adapter.carryDepthSeamPoint stage12Adapter ≡ Atlas.atlas-11
    adapterCarryDepthSeam :
      StageQuotient.Stage12FibreSurface.carry-depth
        (Adapter.stage12FibreSurface stage12Adapter)
        (Adapter.carryDepthSeamPoint stage12Adapter)
      ≡
      Atlas.rev-2
    bridgeAuthorityBits :
      P11PrimeLaneStage12ActionBridgeAuthorityBits
    bridgeNotes :
      List String

open P11PrimeLaneStage12ActionBridge public
open P11PrimeLaneStage12ActionBridgeAuthorityBits public

canonicalP11PrimeLaneStage12ActionBridge :
  P11PrimeLaneStage12ActionBridge
canonicalP11PrimeLaneStage12ActionBridge =
  mkP11PrimeLaneStage12ActionBridge
    "p11-stage12-adapter-bridge"
    Adapter.canonicalP11PrimeLaneStage12ActionAdapter
    refl
    refl
    Successor.canonicalP11PrimeSuccessorWitness
    refl
    Successor.canonicalStage10SuccessorWitness
    refl
    P11C10.canonicalP11UnitGroupC10Witness
    refl
    Regression.canonicalP11Stage11C10Regression
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
    canonicalP11PrimeLaneStage12ActionBridgeAuthorityBits
    ( "The Stage12 adapter is the shared public carrier for the p11 lane."
    ∷ "The p11 successor witness explains the +1 move from stage 10 into the p11 prime lane."
    ∷ "The p11 regression remains local, while the adapter keeps the lane under the same global Stage12 spine used by p7."
    ∷ []
    )
