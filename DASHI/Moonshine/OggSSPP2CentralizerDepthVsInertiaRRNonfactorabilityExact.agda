module DASHI.Moonshine.OggSSPP2CentralizerDepthVsInertiaRRNonfactorabilityExact where

------------------------------------------------------------------------
-- p=2 CENTRALIZER-DEPTH VS INERTIA-RR NONFACTORABILITY
--
-- SOTA / SOURCE INPUT
--
-- Dadhwal--Pankaj give the binary tetrahedral conjugacy classes and character
-- table.  For the faithful degree-2 character, size-4 classes with the SAME
-- centralizer order 6 occur with trace -1 and +1.
--
-- Standard inertia/orbifold Riemann--Roch local terms depend on more than the
-- centralizer order: they also depend on the tangent/normal character through
-- a denominator such as det(1-g).  In the determinant-one 2D model,
--
--     det(1-g) = 2 - chi(g).
--
-- Thus trace -1 and trace +1 give denominator magnitudes 3 and 1 even though
-- both classes have centralizer order 6 and v2-centralizer depth 1.
--
-- DASHI CONSEQUENCE
--
-- The currently useful p=2 statistic
--
--     v2(|C_G(g)|)
--
-- cannot by itself determine the sourced inertia-RR local denominator.
-- Therefore centralizer depth is a PROXY/CANDIDATE statistic, not analytic
-- authority for the exceptional Hauptmodul valuation.
--
-- WILD FIREWALL
--
-- The actual characteristic-2 modular stack is wild, so the tame/orbifold
-- determinant formula is used here only as a dependency witness showing that
-- character data matters.  We do NOT apply tame RR as the final small-prime
-- valuation theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as Centralizer
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Two size-4 classes with equal centralizer data but different degree-2
--    character traces.
--
-- The +/- assignment is the sourced character-table pattern up to naming of
-- the two inversion-stable order families.  Only the collision property is
-- consumed below.
------------------------------------------------------------------------

data DegreeTwoTrace : Set where
  traceMinusOne : DegreeTwoTrace
  tracePlusOne : DegreeTwoTrace

degreeTwoTrace :
  Inertia.BinaryTetrahedralConjugacyClass ->
  DegreeTwoTrace
degreeTwoTrace Inertia.identityClass = tracePlusOne
degreeTwoTrace Inertia.centralMinusOneClass = traceMinusOne
degreeTwoTrace Inertia.orderFourClass = tracePlusOne
degreeTwoTrace Inertia.orderThreePositiveClass = traceMinusOne
degreeTwoTrace Inertia.orderThreeNegativeClass = traceMinusOne
degreeTwoTrace Inertia.orderSixPositiveClass = tracePlusOne
degreeTwoTrace Inertia.orderSixNegativeClass = tracePlusOne

orderThreeRepresentative :
  Inertia.BinaryTetrahedralConjugacyClass
orderThreeRepresentative =
  Inertia.orderThreePositiveClass

orderSixRepresentative :
  Inertia.BinaryTetrahedralConjugacyClass
orderSixRepresentative =
  Inertia.orderSixPositiveClass

sameCentralizerOrder :
  Centralizer.centralizerOrder orderThreeRepresentative
  ≡
  Centralizer.centralizerOrder orderSixRepresentative
sameCentralizerOrder = refl

sameCentralizerTwoAdicDepth :
  Centralizer.centralizerTwoAdicDepth orderThreeRepresentative
  ≡
  Centralizer.centralizerTwoAdicDepth orderSixRepresentative
sameCentralizerTwoAdicDepth = refl

differentDegreeTwoTrace :
  degreeTwoTrace orderThreeRepresentative
  ≡
  degreeTwoTrace orderSixRepresentative
  ->
  ⊥
differentDegreeTwoTrace ()

------------------------------------------------------------------------
-- 2. Determinant-one tame RR denominator proxy.
--
-- chi=-1 -> 2-chi = 3
-- chi=+1 -> 2-chi = 1
------------------------------------------------------------------------

tameDetOneDenominatorMagnitude :
  Inertia.BinaryTetrahedralConjugacyClass ->
  Nat
tameDetOneDenominatorMagnitude class with degreeTwoTrace class
... | traceMinusOne = 3
... | tracePlusOne = 1

orderThreeDenominatorIsThree :
  tameDetOneDenominatorMagnitude orderThreeRepresentative ≡ 3
orderThreeDenominatorIsThree = refl

orderSixDenominatorIsOne :
  tameDetOneDenominatorMagnitude orderSixRepresentative ≡ 1
orderSixDenominatorIsOne = refl

differentTameDenominator :
  tameDetOneDenominatorMagnitude orderThreeRepresentative
  ≡
  tameDetOneDenominatorMagnitude orderSixRepresentative
  ->
  ⊥
differentTameDenominator ()

------------------------------------------------------------------------
-- 3. Exact nonfactorability through centralizer order.
------------------------------------------------------------------------

denominatorNotDeterminedByCentralizerOrderWitness :
  NF.NonFactorabilityWitness
    Centralizer.centralizerOrder
    tameDetOneDenominatorMagnitude
denominatorNotDeterminedByCentralizerOrderWitness =
  NF.nonFactorabilityWitness
    orderThreeRepresentative
    orderSixRepresentative
    sameCentralizerOrder
    differentTameDenominator

tameDenominatorDoesNotFactorThroughCentralizerOrder :
  NF.FactorsThrough
    Centralizer.centralizerOrder
    tameDetOneDenominatorMagnitude
  ->
  ⊥
tameDenominatorDoesNotFactorThroughCentralizerOrder =
  NF.witnessRulesOutEveryFlatFactorisation
    denominatorNotDeterminedByCentralizerOrderWitness

------------------------------------------------------------------------
-- 4. Stronger nonfactorability through p-adic centralizer depth.
------------------------------------------------------------------------

denominatorNotDeterminedByCentralizerDepthWitness :
  NF.NonFactorabilityWitness
    Centralizer.centralizerTwoAdicDepth
    tameDetOneDenominatorMagnitude
denominatorNotDeterminedByCentralizerDepthWitness =
  NF.nonFactorabilityWitness
    orderThreeRepresentative
    orderSixRepresentative
    sameCentralizerTwoAdicDepth
    differentTameDenominator

tameDenominatorDoesNotFactorThroughCentralizerDepth :
  NF.FactorsThrough
    Centralizer.centralizerTwoAdicDepth
    tameDetOneDenominatorMagnitude
  ->
  ⊥
tameDenominatorDoesNotFactorThroughCentralizerDepth =
  NF.witnessRulesOutEveryFlatFactorisation
    denominatorNotDeterminedByCentralizerDepthWitness

------------------------------------------------------------------------
-- 5. Wild small-prime authority must contain at least the missing character
--    coordinate and an additional wild correction/ramification coordinate.
------------------------------------------------------------------------

record P2WildInertiaLocalDatum : Set where
  constructor p2-wild-inertia-local-datum
  field
    conjugacyClass :
      Inertia.BinaryTetrahedralConjugacyClass

    centralizerOrder :
      Nat

    centralizerTwoAdicDepth :
      Nat

    degreeTwoCharacterTrace :
      DegreeTwoTrace

    tameDeterminantDenominatorMagnitude :
      Nat

    wildCorrectionDepth :
      Nat

open P2WildInertiaLocalDatum public

canonicalLocalDatum :
  Inertia.BinaryTetrahedralConjugacyClass ->
  Nat ->
  P2WildInertiaLocalDatum
canonicalLocalDatum class wildDepth =
  p2-wild-inertia-local-datum
    class
    (Centralizer.centralizerOrder class)
    (Centralizer.centralizerTwoAdicDepth class)
    (degreeTwoTrace class)
    (tameDetOneDenominatorMagnitude class)
    wildDepth

data CentralizerDepthAloneIsFullWildRRDatum : Set where
data TameCharacterDenominatorAloneIsWildRRTheorem : Set where
data ComplexCharacterTableIsCharacteristicTwoTangentTheorem : Set where

centralizerDepthAloneIsNotFullWildRRDatum :
  CentralizerDepthAloneIsFullWildRRDatum -> ⊥
centralizerDepthAloneIsNotFullWildRRDatum ()

tameCharacterDenominatorAloneIsNotWildRRTheorem :
  TameCharacterDenominatorAloneIsWildRRTheorem -> ⊥
tameCharacterDenominatorAloneIsNotWildRRTheorem ()

complexCharacterTableNotPromotedToCharacteristicTwoTangentTheorem :
  ComplexCharacterTableIsCharacteristicTwoTangentTheorem -> ⊥
complexCharacterTableNotPromotedToCharacteristicTwoTangentTheorem ()

------------------------------------------------------------------------
-- 6. Sourcing / promotion boundary.
------------------------------------------------------------------------

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P2CentralizerDepthVsInertiaRRBoundary : Set where
  constructor p2-centralizer-depth-vs-inertia-rr-boundary
  field
    degreeTwoCharacterTableExternallySourced : Bool
    equalCentralizerOrderCollisionConstructed : Bool
    equalCentralizerDepthCollisionConstructed : Bool
    differentCharacterTraceWitnessed : Bool
    differentTameDeterminantDenominatorWitnessed : Bool
    denominatorFactorsThroughCentralizerOrder : Bool
    denominatorFactorsThroughCentralizerDepth : Bool
    centralizerDepthStillUsefulAsArithmeticProxy : Bool
    tameRRPromotedToWildCharacteristicTheorem : Bool
    fullWildLocalDatumRequiresMoreThanCentralizerDepth : Bool

canonicalP2CentralizerDepthVsInertiaRRBoundary :
  P2CentralizerDepthVsInertiaRRBoundary
canonicalP2CentralizerDepthVsInertiaRRBoundary =
  p2-centralizer-depth-vs-inertia-rr-boundary
    true true true true true
    false false true false true
