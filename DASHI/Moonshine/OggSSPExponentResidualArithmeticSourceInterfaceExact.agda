module DASHI.Moonshine.OggSSPExponentResidualArithmeticSourceInterfaceExact where

------------------------------------------------------------------------
-- EXPONENT-RESIDUAL ARITHMETIC SOURCE -> BASE369 RECOGNITION SOCKET
--
-- ATTRIBUTION / AUTHORITY BOUNDARY
--
-- Duncan--Swisher supply the monstrous-exponent arithmetic used upstream.
-- They do NOT supply the action-groupoid structure introduced here.
--
-- This module is a DASHI acquisition interface for the missing object.  It
-- does not manufacture an arithmetic source groupoid from the residual counts.
-- A future source/derivation must inhabit ArithmeticResidualSource with an
-- actual state carrier, symmetry action, orbit presentation, and exact pi0
-- receipt.  Only then can FullResidualRecognition be inhabited.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)

import DASHI.Interop.SourceAttributionShapePolicyExact as AttributionPolicy
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Small
import DASHI.Moonshine.OggSSPMonstrousExponent369GluingExact as Exponent369
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2Bridge

------------------------------------------------------------------------
-- 1. Only the two exceptional residual lanes are in scope here.
------------------------------------------------------------------------

data ExceptionalResidualPrime : Set where
  residualP2 : ExceptionalResidualPrime
  residualP3 : ExceptionalResidualPrime

expectedResidualCount : ExceptionalResidualPrime → Nat
expectedResidualCount residualP2 = Exponent369.p2ExceptionalResidual
expectedResidualCount residualP3 = Exponent369.p3ExceptionalResidual

p2ExpectedResidualIsTen :
  expectedResidualCount residualP2 ≡ 10
p2ExpectedResidualIsTen = refl

p3ExpectedResidualIsTwo :
  expectedResidualCount residualP3 ≡ 2
p3ExpectedResidualIsTwo = refl

------------------------------------------------------------------------
-- 2. The target action groupoids are already concrete.
--
-- p2 uses retained orientation as gluing data, hence the trivial symmetry
-- group and ten discrete components.
--
-- p3 uses the literal C2 inversion action on the three constant ternary
-- sections, hence two connected components with nonuniform stabilizers.
------------------------------------------------------------------------

TargetState : ExceptionalResidualPrime → Set
TargetState residualP2 = Small.P2ResidualObject
TargetState residualP3 = Small.ConstantTernaryState

TargetSymmetry : ExceptionalResidualPrime → Set
TargetSymmetry residualP2 = ⊤
TargetSymmetry residualP3 = C2Bridge.C2

targetAction :
  (prime : ExceptionalResidualPrime) →
  Action.InvertibleSymmetryAction
    (TargetState prime)
    (TargetSymmetry prime)
targetAction residualP2 = Small.p2DiscreteAction
targetAction residualP3 = Small.constantC2Action

targetOrbits :
  (prime : ExceptionalResidualPrime) →
  Orbit.OrbitPresentation (targetAction prime)
targetOrbits residualP2 = Small.p2DiscreteOrbitPresentation
targetOrbits residualP3 = Small.constantTernaryOrbitPresentation

targetPi0Count : ExceptionalResidualPrime → Nat
targetPi0Count residualP2 = Small.p2RetainedOrientationPi0Count
targetPi0Count residualP3 = Small.constantTernaryPi0Count

targetPi0MatchesExpectedResidual :
  (prime : ExceptionalResidualPrime) →
  targetPi0Count prime ≡ expectedResidualCount prime
targetPi0MatchesExpectedResidual residualP2 = refl
targetPi0MatchesExpectedResidual residualP3 = refl

------------------------------------------------------------------------
-- 3. Missing arithmetic source groupoid interface.
--
-- pi0Count is not derived merely from the State cardinality.  The source
-- implementation must provide its orbit presentation and separately certify
-- that the connected-component count is the Duncan--Swisher residual count.
------------------------------------------------------------------------

record ArithmeticResidualSource
    (prime : ExceptionalResidualPrime) : Set₁ where
  constructor arithmetic-residual-source
  field
    State : Set
    Symmetry : Set
    action :
      Action.InvertibleSymmetryAction State Symmetry
    orbits :
      Orbit.OrbitPresentation action

    pi0Count : Nat
    pi0CountExact :
      pi0Count ≡ expectedResidualCount prime

    provenance : String
    arithmeticConstructionReference : String
    actionGroupoidIsExternallySourcedClaim : Bool

open ArithmeticResidualSource public

------------------------------------------------------------------------
-- 4. Full recognition must use the stronger generic repository contract.
--
-- In particular, the symmetry map is a homomorphism, the action intertwines,
-- pi0 is bijectively recognized, and stabilizers are preserved/reflected.
------------------------------------------------------------------------

record FullResidualRecognition
    (prime : ExceptionalResidualPrime)
    (source : ArithmeticResidualSource prime) : Set₁ where
  constructor full-residual-recognition
  field
    functor :
      Recognition.ActionRecognitionFunctor
        (action source)
        (targetAction prime)

    recognition :
      Recognition.OrbitStabilizerRecognition
        functor
        (orbits source)
        (targetOrbits prime)

    pi0CountPreserved :
      pi0Count source ≡ targetPi0Count prime

open FullResidualRecognition public

recognitionCountClosesAgainstArithmeticResidual :
  (prime : ExceptionalResidualPrime) →
  (source : ArithmeticResidualSource prime) →
  FullResidualRecognition prime source →
  pi0Count source ≡ expectedResidualCount prime
recognitionCountClosesAgainstArithmeticResidual prime source recognized =
  trans
    (pi0CountPreserved recognized)
    (targetPi0MatchesExpectedResidual prime)


------------------------------------------------------------------------
-- 4b. Strong same-presentation recognition grade.
--
-- This is optional and strictly stronger than FullResidualRecognition.
-- It requires literal two-sided recovery of both target objects and symmetry
-- labels, not merely orbit/stabilizer recognition.
------------------------------------------------------------------------

record ResidualPresentationSameObject
    (prime : ExceptionalResidualPrime)
    (source : ArithmeticResidualSource prime) : Set₁ where
  constructor residual-presentation-same-object
  field
    functor :
      Recognition.ActionRecognitionFunctor
        (action source)
        (targetAction prime)

    presentationIsomorphism :
      Recognition.ActionGroupoidPresentationIsomorphism
        functor
        (orbits source)
        (targetOrbits prime)

open ResidualPresentationSameObject public

------------------------------------------------------------------------
-- 5. The acquisition wall remains explicit.
------------------------------------------------------------------------

data ConstructedArithmeticResidualSourceP2 : Set where
data ConstructedArithmeticResidualSourceP3 : Set where

noArithmeticResidualSourceP2ConstructedHere :
  ConstructedArithmeticResidualSourceP2 → ⊥
noArithmeticResidualSourceP2ConstructedHere ()

noArithmeticResidualSourceP3ConstructedHere :
  ConstructedArithmeticResidualSourceP3 → ⊥
noArithmeticResidualSourceP3ConstructedHere ()

claimOrigin : Source.ClaimOrigin
claimOrigin = Source.repositoryNewExtension

attributionShape :
  AttributionPolicy.RequiredAttributionShape
attributionShape =
  AttributionPolicy.requiredAttributionShape
    AttributionPolicy.internalDerivedTheorem

attributionUsesProofLineage :
  attributionShape ≡ AttributionPolicy.proofLineageNoNewExternalCitation
attributionUsesProofLineage = refl

data ResidualCountAloneConstructsArithmeticSourceGroupoid : Set where
data TargetGroupoidAloneConstructsArithmeticRecognition : Set where

residualCountDoesNotConstructArithmeticSourceGroupoid :
  ResidualCountAloneConstructsArithmeticSourceGroupoid → ⊥
residualCountDoesNotConstructArithmeticSourceGroupoid ()

targetGroupoidDoesNotConstructArithmeticRecognition :
  TargetGroupoidAloneConstructsArithmeticRecognition → ⊥
targetGroupoidDoesNotConstructArithmeticRecognition ()

------------------------------------------------------------------------
-- 6. Frontier.
------------------------------------------------------------------------

record ExponentResidualArithmeticSourceBoundary : Set where
  constructor exponent-residual-arithmetic-source-boundary
  field
    p2TargetActionGroupoidConcrete : Bool
    p3TargetActionGroupoidConcrete : Bool
    p2TargetPi0MatchesResidual : Bool
    p3TargetPi0MatchesResidual : Bool
    sourceRequiresActionAndOrbitPresentation : Bool
    sourceRequiresIndependentPi0Receipt : Bool
    fullRecognitionUsesGenericActionFunctor : Bool
    fullRecognitionUsesOrbitStabilizerRecognition : Bool
    samePresentationRequiresObjectAndSymmetryBijections : Bool
    p2ArithmeticSourceConstructed : Bool
    p3ArithmeticSourceConstructed : Bool
    countAloneConstructsSource : Bool

canonicalExponentResidualArithmeticSourceBoundary :
  ExponentResidualArithmeticSourceBoundary
canonicalExponentResidualArithmeticSourceBoundary =
  exponent-residual-arithmetic-source-boundary
    true true true true
    true true true true true
    false false false
