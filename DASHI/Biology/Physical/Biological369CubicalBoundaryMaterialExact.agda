module DASHI.Biology.Physical.Biological369CubicalBoundaryMaterialExact where

------------------------------------------------------------------------
-- THE SIX PHYSICAL OUTER FACES of the actual 3×3×3 ternary cube.
-- Every external material influx must prove OnFace for its voxel.
-- No interior voxel is silently a source/sink.
--
-- The laws here certify exact discrete material bookkeeping, not
-- calibrated permeability, flow, chemistry or external source data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Data.Vec.Base as V
import Data.Fin.Base as F
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.Physical.BiologicalOriginal54BondSharedVectorExact as Index
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid
import DASHI.Biology.Physical.BiologicalSharedFiniteVectorTransferExact as Transfer

originalOuterFacePoints : Cube.Face6 → List Cube.Ternary27Point
originalOuterFacePoints Cube.xNegativeFace =
  Grid.flatMap (λ y → Grid.mapList
    (λ z → Cube.ternary27Point SSP.sspNegOne y z) Grid.trits)
    Grid.trits
originalOuterFacePoints Cube.xPositiveFace =
  Grid.flatMap (λ y → Grid.mapList
    (λ z → Cube.ternary27Point SSP.sspPosOne y z) Grid.trits)
    Grid.trits
originalOuterFacePoints Cube.yNegativeFace =
  Grid.flatMap (λ x → Grid.mapList
    (λ z → Cube.ternary27Point x SSP.sspNegOne z) Grid.trits)
    Grid.trits
originalOuterFacePoints Cube.yPositiveFace =
  Grid.flatMap (λ x → Grid.mapList
    (λ z → Cube.ternary27Point x SSP.sspPosOne z) Grid.trits)
    Grid.trits
originalOuterFacePoints Cube.zNegativeFace =
  Grid.flatMap (λ x → Grid.mapList
    (λ y → Cube.ternary27Point x y SSP.sspNegOne) Grid.trits)
    Grid.trits
originalOuterFacePoints Cube.zPositiveFace =
  Grid.flatMap (λ x → Grid.mapList
    (λ y → Cube.ternary27Point x y SSP.sspPosOne) Grid.trits)
    Grid.trits

everyOriginalOuterFaceHasNineVoxels :
  (face : Cube.Face6) →
  Grid.countList (originalOuterFacePoints face) ≡ 9
everyOriginalOuterFaceHasNineVoxels Cube.xNegativeFace = refl
everyOriginalOuterFaceHasNineVoxels Cube.xPositiveFace = refl
everyOriginalOuterFaceHasNineVoxels Cube.yNegativeFace = refl
everyOriginalOuterFaceHasNineVoxels Cube.yPositiveFace = refl
everyOriginalOuterFaceHasNineVoxels Cube.zNegativeFace = refl
everyOriginalOuterFaceHasNineVoxels Cube.zPositiveFace = refl

-- Inject q units at exactly one verified original voxel.
-- The finite vector is merely the original cubical material chart.
injectAtIndex :
  ∀ {n} → F.Fin n → Nat → V.Vec Nat n → V.Vec Nat n
injectAtIndex F.zero q (V._∷_ a xs) =
  V._∷_ (q + a) xs
injectAtIndex (F.suc index) q (V._∷_ a xs) =
  V._∷_ a (injectAtIndex index q xs)

injectAtIndexAddsAmount :
  ∀ {n}
  (index : F.Fin n) (q : Nat)
  (state : V.Vec Nat n) →
  V.sum (injectAtIndex index q state) ≡ V.sum state + q
injectAtIndexAddsAmount F.zero q (V._∷_ a xs) =
  trans
    (+-assoc q a (V.sum xs))
    (+-comm q (a + V.sum xs))
injectAtIndexAddsAmount (F.suc index) q (V._∷_ a xs) =
  trans
    (cong (λ t → a + t) (injectAtIndexAddsAmount index q xs))
    (sym (+-assoc a (V.sum xs) q))

-- A true boundary-source event MUST carry the original face proof.
-- Physical flow sign must be explicit at higher layers.
record OriginalOuterFaceInjection : Set where
  constructor original-outer-face-injection
  field
    face : Cube.Face6
    physicalVoxel : Cube.Ternary27Point
    boundaryMembership : Cube.OnFace face physicalVoxel
    incomingMaterial : Nat
    originalBoundaryReference : String

open OriginalOuterFaceInjection public

applyBoundaryInjection :
  OriginalOuterFaceInjection →
  V.Vec Nat 27 → V.Vec Nat 27
applyBoundaryInjection event state =
  injectAtIndex
    (Index.originalPointIndex (physicalVoxel event))
    (incomingMaterial event) state

eachOriginalBoundaryInjectionIsPaid :
  (event : OriginalOuterFaceInjection)
  (state : V.Vec Nat 27) →
  V.sum (applyBoundaryInjection event state)
    ≡ V.sum state + incomingMaterial event
eachOriginalBoundaryInjectionIsPaid event state =
  injectAtIndexAddsAmount
    (Index.originalPointIndex (physicalVoxel event))
    (incomingMaterial event) state

runBoundaryInputs :
  List OriginalOuterFaceInjection →
  V.Vec Nat 27 → V.Vec Nat 27
runBoundaryInputs [] state = state
runBoundaryInputs (event ∷ rest) state =
  runBoundaryInputs rest (applyBoundaryInjection event state)

totalBoundaryInput :
  List OriginalOuterFaceInjection → Nat
totalBoundaryInput [] = 0
totalBoundaryInput (event ∷ rest) =
  incomingMaterial event + totalBoundaryInput rest

allOriginalFaceBoundaryInputsBalance :
  (events : List OriginalOuterFaceInjection)
  (state : V.Vec Nat 27) →
  V.sum (runBoundaryInputs events state)
    ≡ V.sum state + totalBoundaryInput events
allOriginalFaceBoundaryInputsBalance [] state =
  sym (+-identityʳ (V.sum state))
allOriginalFaceBoundaryInputsBalance (event ∷ rest) state =
  trans
    (allOriginalFaceBoundaryInputsBalance rest
      (applyBoundaryInjection event state))
    (trans
      (cong (λ n → n + totalBoundaryInput rest)
        (eachOriginalBoundaryInjectionIsPaid event state))
      (+-assoc (V.sum state)
        (incomingMaterial event)
        (totalBoundaryInput rest)))

-- Concrete, actual original x=-1 boundary point.
selectedOriginalBoundaryEvent : OriginalOuterFaceInjection
selectedOriginalBoundaryEvent =
  original-outer-face-injection
    Cube.xNegativeFace
    Cube.negativeCorner
    (Cube.onFace refl)
    1
    "selected synthetic face input; original biological rate not measured"

originalBoundaryDoesNotAutomaticallyPayPhysiology : Bool
originalBoundaryDoesNotAutomaticallyPayPhysiology = false

------------------------------------------------------------------------
-- Actual finite-volume outflow: selected boundary voxel, debit a
-- SINGLE available quantum or remain stationary if empty.
-- The external loss is the amount actually debited, not a requested
-- but impossible flux. Original rates, valences and chemical species
-- have to be supplied by the later physical model.
------------------------------------------------------------------------

record OriginalOuterFaceDischarge : Set where
  constructor original-outer-face-discharge
  field
    dischargeFace : Cube.Face6
    dischargeVoxel : Cube.Ternary27Point
    dischargeMembership : Cube.OnFace dischargeFace dischargeVoxel
    originalDischargeReference : String

open OriginalOuterFaceDischarge public

dischargeIndex :
  OriginalOuterFaceDischarge → F.Fin 27
dischargeIndex event = Index.originalPointIndex (dischargeVoxel event)

actualDischargedAmount :
  OriginalOuterFaceDischarge → V.Vec Nat 27 → Nat
actualDischargedAmount event state
  with V.lookup state (dischargeIndex event)
... | zero = 0
... | suc n = 1

applyBoundaryDischarge :
  OriginalOuterFaceDischarge →
  V.Vec Nat 27 → V.Vec Nat 27
applyBoundaryDischarge event state =
  V.updateAt state (dischargeIndex event)
    (λ n → pred n)

-- Reuse the original generic source-debit conservation proof owner.
-- pred(suc n)=n and pred(0)=0 is definitionally equal to the
-- original debitAt, at every finite vector index.
dischargeIsOriginalDebit :
  ∀ {n}
  (index : F.Fin n)
  (state : V.Vec Nat n) →
  V.updateAt state index pred ≡ Transfer.debitAt index state
dischargeIsOriginalDebit F.zero (V._∷_ zero xs) = refl
dischargeIsOriginalDebit F.zero (V._∷_ (suc a) xs) = refl
dischargeIsOriginalDebit (F.suc index) (V._∷_ a xs) =
  cong (V._∷_ a) (dischargeIsOriginalDebit index xs)

failedDebitConserves :
  ∀ {n}
  (index : F.Fin n)
  (state : V.Vec Nat n) →
  V.lookup state index ≡ zero →
  V.sum (Transfer.debitAt index state) ≡ V.sum state
failedDebitConserves F.zero (V._∷_ zero xs) refl = refl
failedDebitConserves F.zero (V._∷_ (suc a) xs) ()
failedDebitConserves (F.suc index) (V._∷_ a xs) proof =
  cong (λ n → a + n)
    (failedDebitConserves index xs proof)

rightOneIsSucc : (n : Nat) → n + 1 ≡ suc n
rightOneIsSucc n =
  trans (+-suc n zero) (cong suc (+-identityʳ n))

outflowIndexBalance :
  ∀ {n}
  (index : F.Fin n)
  (state : V.Vec Nat n) →
  V.sum (Transfer.debitAt index state)
    + (case V.lookup state index of λ where
         zero → 0
         (suc _) → 1)
    ≡ V.sum state
outflowIndexBalance index state with V.lookup state index
... | zero =
  trans
    (+-identityʳ (V.sum (Transfer.debitAt index state)))
    (failedDebitConserves index state refl)
... | suc k =
  trans
    (rightOneIsSucc (V.sum (Transfer.debitAt index state)))
    (Transfer.successfulDebitDecreasesTotalByOne index state k refl)

outflowMaterialBalance :
  (event : OriginalOuterFaceDischarge)
  (state : V.Vec Nat 27) →
  V.sum (applyBoundaryDischarge event state)
    + actualDischargedAmount event state
    ≡ V.sum state
outflowMaterialBalance event state =
  trans
    (cong
      (λ vector →
        V.sum vector + actualDischargedAmount event state)
      (dischargeIsOriginalDebit (dischargeIndex event) state))
    (outflowIndexBalance (dischargeIndex event) state)

data OriginalFaceExchange : Set where
  addAtOuterFace : OriginalOuterFaceInjection → OriginalFaceExchange
  removeAtOuterFace : OriginalOuterFaceDischarge → OriginalFaceExchange

applyOriginalFaceExchange :
  OriginalFaceExchange →
  V.Vec Nat 27 → V.Vec Nat 27
applyOriginalFaceExchange (addAtOuterFace event) state =
  applyBoundaryInjection event state
applyOriginalFaceExchange (removeAtOuterFace event) state =
  applyBoundaryDischarge event state

faceExchangeInput : OriginalFaceExchange → Nat
faceExchangeInput (addAtOuterFace event) = incomingMaterial event
faceExchangeInput (removeAtOuterFace event) = 0

faceExchangeOutput :
  OriginalFaceExchange → V.Vec Nat 27 → Nat
faceExchangeOutput (addAtOuterFace event) state = 0
faceExchangeOutput (removeAtOuterFace event) state =
  actualDischargedAmount event state

originalFaceExchangeBalance :
  (event : OriginalFaceExchange)
  (state : V.Vec Nat 27) →
  V.sum (applyOriginalFaceExchange event state)
    + faceExchangeOutput event state
    ≡ V.sum state + faceExchangeInput event
originalFaceExchangeBalance (addAtOuterFace event) state =
  trans
    (+-identityʳ (V.sum (applyBoundaryInjection event state)))
    (eachOriginalBoundaryInjectionIsPaid event state)
originalFaceExchangeBalance (removeAtOuterFace event) state =
  trans
    (outflowMaterialBalance event state)
    (sym (+-identityʳ (V.sum state)))

record BoundaryHistoryResult : Set where
  constructor boundary-history-result
  field
    finalMaterial : V.Vec Nat 27
    totalExternalInput : Nat
    totalExternalOutput : Nat

open BoundaryHistoryResult public

runOriginalBoundaryExchange :
  List OriginalFaceExchange →
  V.Vec Nat 27 → BoundaryHistoryResult
runOriginalBoundaryExchange [] state =
  boundary-history-result state 0 0
runOriginalBoundaryExchange (event ∷ rest) state
  with runOriginalBoundaryExchange rest
    (applyOriginalFaceExchange event state)
... | boundary-history-result final incoming outgoing =
  boundary-history-result
    final
    (faceExchangeInput event + incoming)
    (faceExchangeOutput event state + outgoing)

exchangeAssociative :
  (a b c : Nat) → a + (b + c) ≡ (a + c) + b
exchangeAssociative a b c =
  trans
    (cong (λ x → a + x) (+-comm b c))
    (sym (+-assoc a c b))

allOriginalBoundaryExchangeHistoriesBalance :
  (events : List OriginalFaceExchange)
  (state : V.Vec Nat 27) →
  V.sum (finalMaterial (runOriginalBoundaryExchange events state))
    + totalExternalOutput (runOriginalBoundaryExchange events state)
    ≡
  V.sum state
    + totalExternalInput (runOriginalBoundaryExchange events state)
allOriginalBoundaryExchangeHistoriesBalance [] state =
  sym (+-identityʳ (V.sum state))
allOriginalBoundaryExchangeHistoriesBalance (event ∷ rest) state
  with runOriginalBoundaryExchange rest
    (applyOriginalFaceExchange event state)
    | allOriginalBoundaryExchangeHistoriesBalance rest
        (applyOriginalFaceExchange event state)
... | boundary-history-result final incoming outgoing | induction =
  trans
    (exchangeAssociative
      (V.sum final) (faceExchangeOutput event state) outgoing)
    (trans
      (cong (λ n → n + faceExchangeOutput event state) induction)
      (trans
        (exchangeAssociative
          (V.sum (applyOriginalFaceExchange event state))
          incoming (faceExchangeOutput event state))
        (trans
          (cong (λ n → n + incoming)
            (originalFaceExchangeBalance event state))
          (+-assoc (V.sum state)
            (faceExchangeInput event) incoming))))
