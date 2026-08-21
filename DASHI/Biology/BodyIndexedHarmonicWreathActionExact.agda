module DASHI.Biology.BodyIndexedHarmonicWreathActionExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

------------------------------------------------------------------------
-- BODY-INDEXED HARMONIC WREATH-STYLE ACTION
--
-- Audrey Terras, "Fourier Analysis on Finite Groups and Applications".
-- DOI: 10.1017/CBO9780511626265.
-- Volodymyr Nekrashevych, "Self-Similar Groups".
-- DOI: 10.1090/surv/117.
--
-- The existing T^2_3 translation gives the permutation/index-motion part of a
-- wreath-style action.  Here the local transform is explicitly body-indexed.
-- We construct a finite noncommutation witness between changing embodied
-- context and applying a deploy+local-computation step.  We do NOT claim the
-- full body-augmented structure is a group or semidirect product until its laws
-- are proved.
------------------------------------------------------------------------

data BodyIndex : Set where
  regulatedBody mobilisedBody : BodyIndex

data LocalGate : Set where
  gateClosed gateOpen : LocalGate

record IndexedState : Set where
  constructor indexedState
  field
    body : BodyIndex
    phase : Torus.Torus3x3
    gate : LocalGate

open IndexedState public

bodyShift : IndexedState → IndexedState
bodyShift state = indexedState mobilisedBody (phase state) (gate state)

localTransform : BodyIndex → LocalGate
localTransform regulatedBody = gateOpen
localTransform mobilisedBody = gateClosed

deployAndCompute : IndexedState → IndexedState
deployAndCompute state =
  indexedState
    (body state)
    (Torus.translateFirst (phase state))
    (localTransform (body state))

originPhase : Torus.Torus3x3
originPhase = Torus.torusPoint Torus.residueZero Torus.residueZero

initialState : IndexedState
initialState = indexedState regulatedBody originPhase gateClosed

bodyThenDeploy : IndexedState
bodyThenDeploy = deployAndCompute (bodyShift initialState)

deployThenBody : IndexedState
deployThenBody = bodyShift (deployAndCompute initialState)

bodyThenDeployGateClosed : gate bodyThenDeploy ≡ gateClosed
bodyThenDeployGateClosed = refl

deployThenBodyGateOpen : gate deployThenBody ≡ gateOpen
deployThenBodyGateOpen = refl

bodyAndDeployDoNotCommute : bodyThenDeploy ≡ deployThenBody → ⊥
bodyAndDeployDoNotCommute ()

bothAdvanceSameCoarsePhase :
  phase bodyThenDeploy ≡ phase deployThenBody
bothAdvanceSameCoarsePhase = refl

record BodyIndexedWreathBoundary : Set where
  constructor bodyIndexedWreathBoundary
  field
    torusTranslationRelocatesCoarseAddress : Bool
    localTransformDependsOnBodyIndex : Bool
    bodyShiftCommutesWithDeployComputeUniversally : Bool
    fullBodyAugmentedSemidirectProductProved : Bool
    noncommutingCountermodelExists : Bool

canonicalBodyIndexedWreathBoundary : BodyIndexedWreathBoundary
canonicalBodyIndexedWreathBoundary =
  bodyIndexedWreathBoundary true true false false true
