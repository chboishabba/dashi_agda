module DASHI.Moonshine.OggSSPSmallCharacteristicAcquisitionDirectionExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC ACQUISITION DIRECTION
--
-- The p=2 and p=3 raw finite-field Frobenius candidates fail in opposite ways.
--
-- p=3:
--   raw F9/F3 Frobenius has six orbit components, while the residual target
--   has two.  A concrete equivariant extension-coordinate quotient exists.
--
-- p=2:
--   raw F4/F2 Frobenius has only three orbit components, while the retained
--   residual target requires ten.  Moreover no UNIFORM marked lift of the
--   three raw F4 orbits can produce ten components.
--
-- Therefore the two arithmetic acquisition searches have opposite shape:
--
--   p=3 : quotient/compression of raw extension-field geometry is plausible;
--   p=2 : enrichment/marked cover beyond the raw field carrier is required
--          if the raw F4 orbit semantics are retained.
--
-- This is a repository cross-module theorem.  It does not identify either
-- missing arithmetic residual source.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPP3F9FrobeniusCandidateNoGoExact as F9
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source

data AcquisitionDirection : Set where
  quotientOrCompression : AcquisitionDirection
  markedEnrichmentOrCover : AcquisitionDirection

p3AcquisitionDirection : AcquisitionDirection
p3AcquisitionDirection = quotientOrCompression

p2AcquisitionDirection : AcquisitionDirection
p2AcquisitionDirection = markedEnrichmentOrCover

p3RawOrbitCount : Nat
p3RawOrbitCount = 6

p3ResidualOrbitCount : Nat
p3ResidualOrbitCount = 2

p2RawOrbitCount : Nat
p2RawOrbitCount = F4.rawF4Pi0Count

p2ResidualOrbitCount : Nat
p2ResidualOrbitCount = F4.requiredRetainedP2Pi0Count

p3RawIsThreeCopiesOfResidualCount :
  p3RawOrbitCount ≡ 3 * p3ResidualOrbitCount
p3RawIsThreeCopiesOfResidualCount = refl

p2RawCountIsThree :
  p2RawOrbitCount ≡ 3
p2RawCountIsThree = refl

p2ResidualCountIsTen :
  p2ResidualOrbitCount ≡ 10
p2ResidualCountIsTen = refl

p3ConcreteQuotientExists :
  (target : DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact.ConstantTernaryState) ->
  Σ F9.F9Point
    (λ source ->
      F9.extensionCoordinate source ≡ target)
p3ConcreteQuotientExists target =
  F9.extensionCoordinateSurjective target ,
  F9.extensionCoordinateSurjectiveCorrect target

p3QuotientIsEquivariant :
  (g : DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact.C2)
  (x : F9.F9Point) ->
  F9.extensionCoordinate (F9.actF9 g x)
  ≡
  DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact.actConstantC2
    g
    (F9.extensionCoordinate x)
p3QuotientIsEquivariant =
  F9.extensionCoordinateEquivariant

p3QuotientIsNotFullRecognition :
  DASHI.Core.ActionOrbitRecognitionFunctorExact.Pi0Embedding
    F9.f9ExtensionCoordinateOrbitRecognition
  ->
  ⊥
p3QuotientIsNotFullRecognition =
  F9.f9ExtensionCoordinateNotPi0Embedding

p2NoUniformMarkedLift :
  (k : Nat) ->
  F4.uniformMarkedOrbitCount k ≡ 10 ->
  ⊥
p2NoUniformMarkedLift =
  F4.noUniformThreeOrbitLiftToTen

data P2RawFieldQuotientCanCreateTenComponents : Set where
data P3WholeRawFieldIsAlreadyResidualSource : Set where

p2RawFieldQuotientDoesNotCreateTenComponentClaim :
  P2RawFieldQuotientCanCreateTenComponents -> ⊥
p2RawFieldQuotientDoesNotCreateTenComponentClaim ()

p3WholeRawFieldDoesNotBecomeResidualSourceClaim :
  P3WholeRawFieldIsAlreadyResidualSource -> ⊥
p3WholeRawFieldDoesNotBecomeResidualSourceClaim ()

claimOrigin : Source.ClaimOrigin
claimOrigin = Source.repositoryCrossModuleInference

record SmallCharacteristicAcquisitionDirectionBoundary : Set where
  constructor small-characteristic-acquisition-direction-boundary
  field
    p3RawF9HasSixOrbitPresentation : Bool
    p3ResidualTargetHasTwoComponents : Bool
    p3ConcreteEquivariantQuotientExists : Bool
    p3WholeF9IsFullRecognition : Bool
    p2RawF4HasThreeOrbitPresentation : Bool
    p2ResidualTargetRequiresTenComponents : Bool
    p2UniformMarkedLiftRuledOut : Bool
    p2MarkedEnrichmentRequiredIfRetainingRawF4OrbitSemantics : Bool
    eitherDirectionIdentifiesArithmeticResidualSource : Bool

canonicalSmallCharacteristicAcquisitionDirectionBoundary :
  SmallCharacteristicAcquisitionDirectionBoundary
canonicalSmallCharacteristicAcquisitionDirectionBoundary =
  small-characteristic-acquisition-direction-boundary
    true true true false
    true true true true
    false
