module DASHI.Moonshine.OggSSPArithmeticResidualGroupoidRecognitionFunctorExact where

------------------------------------------------------------------------
-- ARITHMETIC RESIDUAL GROUPOID -> BASE369 RECOGNITION CONTRACT
--
-- ATTRIBUTION BOUNDARY
--
-- External arithmetic residual counts are consumed from the attributed
-- Duncan--Swisher owner through OggSSPMonstrousExponent369GluingExact.
--
-- The recognition-functor contract, the p=2/p=3 target tests, and the
-- Fricke/residual cross-pollination below are DASHI repository extensions.
-- No external source is credited with the Base369 recognition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Interop.SourceAttributionShapePolicyExact as AttributionPolicy
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Generic
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Symmetry
import DASHI.Moonshine.OggSSPMonstrousExponent369GluingExact as Exponent369
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Small
import DASHI.Moonshine.JInvariantJCoarseFineFrickeBoundaryTransportBidiExact as Fricke
import DASHI.Moonshine.P11MarkedFrobeniusResidualReceiptExact as P11Residual

recognitionFunctorClaimOrigin : Source.ClaimOrigin
recognitionFunctorClaimOrigin = Source.repositoryNewExtension

thisModuleAttributionShape :
  AttributionPolicy.RequiredAttributionShape
thisModuleAttributionShape =
  AttributionPolicy.requiredAttributionShape
    AttributionPolicy.internalDerivedTheorem

------------------------------------------------------------------------
-- 1. Generic action-groupoid recognition functor.
--
-- This is deliberately stronger than a map of object sets.  A lawful
-- recognition must map arrows, intertwine the action, descend to orbit
-- components, preserve chosen representatives, and preserve/reflect the
-- stabilizer equivalence relation.
------------------------------------------------------------------------

record ActionGroupoidRecognitionFunctor
    {SourceState SourceGroup TargetState TargetGroup : Set}
    (sourceAction :
      Symmetry.InvertibleSymmetryAction SourceState SourceGroup)
    (sourcePresentation :
      Generic.OrbitPresentation sourceAction)
    (targetAction :
      Symmetry.InvertibleSymmetryAction TargetState TargetGroup)
    (targetPresentation :
      Generic.OrbitPresentation targetAction) : Set₁ where
  constructor action-groupoid-recognition-functor
  field
    objectMap : SourceState → TargetState
    arrowMap : SourceGroup → TargetGroup

    actionIntertwining :
      (g : SourceGroup) (state : SourceState) →
      objectMap (Symmetry.act sourceAction g state)
      ≡
      Symmetry.act targetAction (arrowMap g) (objectMap state)

    orbitMap :
      Generic.Orbit sourcePresentation →
      Generic.Orbit targetPresentation

    orbitMapCommutes :
      (state : SourceState) →
      orbitMap (Generic.orbitOf sourcePresentation state)
      ≡ Generic.orbitOf targetPresentation (objectMap state)

    representativesAgree :
      (orbit : Generic.Orbit sourcePresentation) →
      objectMap (Generic.representative sourcePresentation orbit)
      ≡
      Generic.representative targetPresentation (orbitMap orbit)

    stabilizerPreserved :
      (orbit : Generic.Orbit sourcePresentation)
      (g h : SourceGroup) →
      Generic.StabilizerEquivalent sourcePresentation orbit g h →
      Generic.StabilizerEquivalent targetPresentation
        (orbitMap orbit) (arrowMap g) (arrowMap h)

    stabilizerReflected :
      (orbit : Generic.Orbit sourcePresentation)
      (g h : SourceGroup) →
      Generic.StabilizerEquivalent targetPresentation
        (orbitMap orbit) (arrowMap g) (arrowMap h) →
      Generic.StabilizerEquivalent sourcePresentation orbit g h

open ActionGroupoidRecognitionFunctor public

------------------------------------------------------------------------
-- 2. Finite pi0 recognition gate.
--
-- Orbit/stabilizer preservation is structural.  For the finite residual
-- carriers here we additionally require preservation of the number of
-- connected components.  This cheap gate already decides one side of p=2.
------------------------------------------------------------------------

record Pi0RecognitionGate (sourcePi0 targetPi0 : Nat) : Set where
  constructor pi0-recognition-gate
  field
    pi0CountPreserved : sourcePi0 ≡ targetPi0

open Pi0RecognitionGate public

------------------------------------------------------------------------
-- 3. p=3 target: the constant-ternary C2 groupoid passes the pi0 gate.
--
-- This is only a target-side compatibility theorem.  It does NOT construct the
-- arithmetic source groupoid or the full recognition functor.
------------------------------------------------------------------------

p3Pi0RecognitionGate :
  Pi0RecognitionGate
    Exponent369.p3ExceptionalResidual
    Small.constantTernaryPi0Count
p3Pi0RecognitionGate = pi0-recognition-gate refl

p3TargetZeroStabilizerSize :
  Small.constantStabilizerSize Small.zeroConstantOrbit ≡ 2
p3TargetZeroStabilizerSize = refl

p3TargetNonzeroStabilizerSize :
  Small.constantStabilizerSize Small.nonzeroConstantOrbit ≡ 1
p3TargetNonzeroStabilizerSize = refl

data P3ArithmeticStabilizerProfileRecognized : Set where

p3ArithmeticStabilizerRecognitionStillOpen :
  P3ArithmeticStabilizerProfileRecognized → ⊥
p3ArithmeticStabilizerRecognitionStillOpen ()

------------------------------------------------------------------------
-- 4. p=2 target discriminator.
--
-- Arithmetic residual count is ten.  Therefore a recognition functor required
-- to preserve pi0 cannot land in the binary-flip quotient, whose pi0 is five.
-- The retained-orientation target has pi0 ten and survives this gate, but that
-- cardinal compatibility is not promoted to semantic recognition.
------------------------------------------------------------------------

data P2FlipQuotientPassesPi0RecognitionGate : Set where

p2FlipQuotientFailsPi0RecognitionGate :
  Pi0RecognitionGate
    Exponent369.p2ExceptionalResidual
    Small.p2ResidualPi0Count
  → ⊥
p2FlipQuotientFailsPi0RecognitionGate ()

p2RetainedOrientationPassesPi0RecognitionGate :
  Pi0RecognitionGate
    Exponent369.p2ExceptionalResidual
    Small.p2RetainedOrientationPi0Count
p2RetainedOrientationPassesPi0RecognitionGate =
  pi0-recognition-gate refl

data P2RetainedOrientationArithmeticRecognitionConstructed : Set where

p2RetainedOrientationRecognitionStillOpen :
  P2RetainedOrientationArithmeticRecognitionConstructed → ⊥
p2RetainedOrientationRecognitionStillOpen ()


------------------------------------------------------------------------
-- 4b. Executable p=2 target-semantics selector.
------------------------------------------------------------------------

data P2TargetSemantics : Set where
  binaryFlipAsGauge : P2TargetSemantics
  orientationRetainedAsGluingData : P2TargetSemantics

p2TargetPi0Count : P2TargetSemantics → Nat
p2TargetPi0Count binaryFlipAsGauge = Small.p2ResidualPi0Count
p2TargetPi0Count orientationRetainedAsGluingData =
  Small.p2RetainedOrientationPi0Count

data P2TargetPassesArithmeticPi0 : P2TargetSemantics → Set where
  retainedOrientationPasses :
    P2TargetPassesArithmeticPi0 orientationRetainedAsGluingData

p2FlipTargetCannotPassArithmeticPi0 :
  P2TargetPassesArithmeticPi0 binaryFlipAsGauge → ⊥
p2FlipTargetCannotPassArithmeticPi0 ()

p2RetainedTargetPassesArithmeticPi0 :
  P2TargetPassesArithmeticPi0 orientationRetainedAsGluingData
p2RetainedTargetPassesArithmeticPi0 = retainedOrientationPasses

p2PassingTargetMustRetainOrientation :
  (target : P2TargetSemantics) →
  P2TargetPassesArithmeticPi0 target →
  target ≡ orientationRetainedAsGluingData
p2PassingTargetMustRetainOrientation
  binaryFlipAsGauge ()
p2PassingTargetMustRetainOrientation
  orientationRetainedAsGluingData retainedOrientationPasses = refl

------------------------------------------------------------------------
-- 5. Fricke cross-pollination.
--
-- Existing finite Fricke transport exchanges a coarse coordinate with a fine
-- coordinate.  The p=11 arithmetic Frobenius example independently proves the
-- generic discipline: a hidden involutive motion can preserve the coarse
-- surface while forcing the reopening residual to move.
--
-- Together these rule out the inference
--
--   involution => gauge identification
--
-- as a repository principle.  They do not by themselves choose the p=2
-- retained-orientation semantics.
------------------------------------------------------------------------

finiteFrickeBoundaryFrontier :
  Fricke.FrickeBoundaryTransportFrontier
finiteFrickeBoundaryFrontier =
  Fricke.canonicalFrickeBoundaryTransportFrontier

finiteFrickeCrossesCoarseFineBoundary :
  Fricke.coarseFineBoundaryExchangeExact finiteFrickeBoundaryFrontier ≡ true
finiteFrickeCrossesCoarseFineBoundary = refl

finiteFrickeIsNotPureFinePermutation :
  Fricke.pureFinePermutationModelRejectedForFiniteTransport
    finiteFrickeBoundaryFrontier
  ≡ true
finiteFrickeIsNotPureFinePermutation = refl

p11ResidualDynamicsBoundary :
  P11Residual.P11MarkedFrobeniusResidualBoundary
p11ResidualDynamicsBoundary =
  P11Residual.canonicalP11MarkedFrobeniusResidualBoundary

p11HiddenFrobeniusForcesResidualMotion :
  P11Residual.exactReopeningResidualMustMove
    p11ResidualDynamicsBoundary
  ≡ true
p11HiddenFrobeniusForcesResidualMotion = refl

data FrickeInvolutionForcesGaugeQuotient : Set where

frickeInvolutionDoesNotForceGaugeQuotient :
  FrickeInvolutionForcesGaugeQuotient → ⊥
frickeInvolutionDoesNotForceGaugeQuotient ()

------------------------------------------------------------------------
-- 6. Recognition frontier.
------------------------------------------------------------------------

data SmallCharacteristicRecognitionResidual : Set where
  missingArithmeticSourceGroupoidP3 : SmallCharacteristicRecognitionResidual
  missingP3StabilizerProfileComparison : SmallCharacteristicRecognitionResidual
  missingArithmeticSourceGroupoidP2 : SmallCharacteristicRecognitionResidual
  missingP2RetainedOrientationActionIntertwiner : SmallCharacteristicRecognitionResidual
  missingP2OrbitStabilizerPreservation : SmallCharacteristicRecognitionResidual

record SmallCharacteristicRecognitionFunctorBoundary : Set where
  constructor small-characteristic-recognition-functor-boundary
  field
    genericActionGroupoidFunctorContractOwned : Bool
    actionIntertwiningRequired : Bool
    orbitPreservationRequired : Bool
    stabilizerPreservationAndReflectionRequired : Bool

    p3TargetPassesPi0Gate : Bool
    p3TargetStabilizerProfileExplicit : Bool
    p3ArithmeticRecognitionConstructed : Bool

    p2FlipTargetPi0 : Nat
    p2FlipTargetFailsArithmeticPi0Gate : Bool
    p2RetainedOrientationTargetPi0 : Nat
    p2RetainedOrientationPassesArithmeticPi0Gate : Bool
    p2RetainedOrientationArithmeticRecognitionConstructed : Bool
    p2Pi0GateSelectsRetainedOrientationUniquely : Bool

    finiteFrickeCrossBoundaryTransportOwned : Bool
    p11HiddenInvolutionForcesResidualMotionOwned : Bool
    involutionImpliesGaugeIdentification : Bool

    firstResidual : SmallCharacteristicRecognitionResidual

canonicalSmallCharacteristicRecognitionFunctorBoundary :
  SmallCharacteristicRecognitionFunctorBoundary
canonicalSmallCharacteristicRecognitionFunctorBoundary =
  small-characteristic-recognition-functor-boundary
    true true true true
    true true false
    5 true
    10 true false true
    true true false
    missingArithmeticSourceGroupoidP2
