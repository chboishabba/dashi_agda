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
