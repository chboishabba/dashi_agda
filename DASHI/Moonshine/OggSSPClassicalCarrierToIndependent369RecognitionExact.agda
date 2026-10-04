module DASHI.Moonshine.OggSSPClassicalCarrierToIndependent369RecognitionExact where

------------------------------------------------------------------------
-- CLASSICALLY GROUNDED SMALL-CHARACTERISTIC CARRIERS -> INDEPENDENT 369
--
-- p=3:
--   Deligne--Rapoport local incidence C2-set
--     -> canonical ternary residual
--     -> independent SSPTrit/Base369 target.
--
-- p=2:
--   orientation doublet x unoriented inertia sectors
--     -> DASHI CM-marked ten-state source
--     -> retained residual ten-state carrier
--     -> independent Base369 retained-orientation target.
--
-- These are exact finite action/orbit/stabilizer recognition chains.
-- They do NOT identify Base369 semantic labels with classical moduli labels,
-- nor do they produce a scheme/stack isomorphism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3Classical
import DASHI.Moonshine.OggSSPP3Base369RecognitionExact as P3Bridge
import DASHI.Moonshine.Base369P3ConstantTernaryActionGroupoidExact as P3Target

import DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact as P2Classical
import DASHI.Moonshine.OggSSPP2RetainedCMMarkedSourceExact as P2Source
import DASHI.Moonshine.OggSSPP2Base369RecognitionForkExact as P2Bridge
import DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact as P2Target

import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. p=3 direct classical-carrier -> independent-369 recognition.
------------------------------------------------------------------------

p3ClassicalTo369ActionRecognition =
  Recognition.composeActionRecognition
    P3Classical.p3LocalToKernelActionRecognition
    P3Bridge.p3ActionRecognition

p3ClassicalTo369FullRecognition :
  Recognition.OrbitStabilizerRecognition
    p3ClassicalTo369ActionRecognition
    P3Classical.p3LocalStrataOrbitPresentation
    P3Target.p3OrbitPresentation
p3ClassicalTo369FullRecognition =
  Recognition.composeOrbitStabilizerRecognition
    P3Classical.p3LocalFullRecognition
    P3Bridge.p3FullRecognition

------------------------------------------------------------------------
-- 2. p=2 classical-factorized carrier -> residual source recognition.
------------------------------------------------------------------------

p2OrientedInertiaToResidualActionRecognition =
  Recognition.composeActionRecognition
    P2Classical.orientedInertiaActionRecognition
    P2Source.p2CMToResidualActionRecognition

p2OrientedInertiaToResidualFullRecognition =
  Recognition.composeOrbitStabilizerRecognition
    P2Classical.orientedInertiaFullRecognition
    P2Source.p2CMToResidualFullRecognition

------------------------------------------------------------------------
-- 3. p=2 direct classical-factorized carrier -> independent-369 recognition.
------------------------------------------------------------------------

p2ClassicalTo369ActionRecognition =
  Recognition.composeActionRecognition
    p2OrientedInertiaToResidualActionRecognition
    P2Bridge.p2RetainedActionRecognition

p2ClassicalTo369FullRecognition :
  Recognition.OrbitStabilizerRecognition
    p2ClassicalTo369ActionRecognition
    P2Classical.orientedInertiaOrbits
    P2Target.p2RetainedOrbitPresentation
p2ClassicalTo369FullRecognition =
  Recognition.composeOrbitStabilizerRecognition
    p2OrientedInertiaToResidualFullRecognition
    P2Bridge.p2RetainedFullRecognition

------------------------------------------------------------------------
-- 4. Interpretation boundary.
------------------------------------------------------------------------

data FiniteRecognitionCreatesSchemeIsomorphism : Set where
data FiniteRecognitionCreatesBase369SemanticIdentity : Set where
data ClassicalFactorizationProvesMonsterResidualArithmetic : Set where

finiteRecognitionDoesNotCreateSchemeIsomorphism :
  FiniteRecognitionCreatesSchemeIsomorphism -> ⊥
finiteRecognitionDoesNotCreateSchemeIsomorphism ()

finiteRecognitionDoesNotCreateBase369SemanticIdentity :
  FiniteRecognitionCreatesBase369SemanticIdentity -> ⊥
finiteRecognitionDoesNotCreateBase369SemanticIdentity ()

classicalFactorizationDoesNotProveMonsterResidualArithmetic :
  ClassicalFactorizationProvesMonsterResidualArithmetic -> ⊥
classicalFactorizationDoesNotProveMonsterResidualArithmetic ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record ClassicalCarrierToIndependent369Boundary : Set where
  constructor classical-carrier-to-independent369-boundary
  field
    p3ClassicalLocalCarrierFullRecognitionPaid : Bool
    p2ClassicallySourcedFactorizedCarrierFullRecognitionPaid : Bool
    finiteRecognitionOnly : Bool
    schemeOrStackIsomorphismClaimed : Bool
    base369SemanticIdentityClaimed : Bool
    monsterArithmeticIdentityClaimed : Bool

canonicalClassicalCarrierToIndependent369Boundary :
  ClassicalCarrierToIndependent369Boundary
canonicalClassicalCarrierToIndependent369Boundary =
  classical-carrier-to-independent369-boundary
    true true true false false false
