module DASHI.Visualisation.FiniteAnisotropicKernelExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exact finite arithmetic shadow of the Mahalanobis/event-kernel construction.
-- Distances are represented by a common denominator so no hidden division or
-- floating-point square root enters the promoted theorem surface.

record Point2 : Set where
  constructor point2
  field
    pointX : Nat
    pointY : Nat

open Point2 public

absoluteDifference : Nat → Nat → Nat
absoluteDifference a b = (a ∸ b) + (b ∸ a)

square : Nat → Nat
square n = n * n

record DiagonalScale2 : Set where
  constructor diagonalScale2
  field
    scaleXSquared : Nat
    scaleYSquared : Nat

open DiagonalScale2 public

record EllipticEvent2 : Set where
  constructor ellipticEvent2
  field
    eventCentre : Point2
    eventScale : DiagonalScale2
    eventWeight : Nat

open EllipticEvent2 public

mahalanobisNumerator : EllipticEvent2 → Point2 → Nat
mahalanobisNumerator event query =
  square
    (absoluteDifference
      (pointX query)
      (pointX (eventCentre event)))
  * scaleYSquared (eventScale event)
  +
  square
    (absoluteDifference
      (pointY query)
      (pointY (eventCentre event)))
  * scaleXSquared (eventScale event)

mahalanobisDenominator : EllipticEvent2 → Nat
mahalanobisDenominator event =
  scaleXSquared (eventScale event)
  * scaleYSquared (eventScale event)

canonicalEllipticEvent : EllipticEvent2
canonicalEllipticEvent =
  ellipticEvent2
    (point2 2 3)
    (diagonalScale2 4 1)
    5

canonicalQuery : Point2
canonicalQuery = point2 4 4

canonicalMahalanobisNumeratorIsEight :
  mahalanobisNumerator canonicalEllipticEvent canonicalQuery ≡ 8
canonicalMahalanobisNumeratorIsEight = refl

canonicalMahalanobisDenominatorIsFour :
  mahalanobisDenominator canonicalEllipticEvent ≡ 4
canonicalMahalanobisDenominatorIsFour = refl

canonicalSquaredRadiusIsTwo :
  mahalanobisNumerator canonicalEllipticEvent canonicalQuery
  ≡
  2 * mahalanobisDenominator canonicalEllipticEvent
canonicalSquaredRadiusIsTwo = refl

------------------------------------------------------------------------
-- Sharpness and geometric scale remain separate.  Two events can share one
-- centre while having different ellipsoidal radius numerators.

narrowXEvent : EllipticEvent2
narrowXEvent =
  ellipticEvent2 (point2 2 3) (diagonalScale2 1 1) 5

wideXEvent : EllipticEvent2
wideXEvent =
  ellipticEvent2 (point2 2 3) (diagonalScale2 4 1) 5

scaleChangesRadiusAtFixedQuery :
  mahalanobisNumerator narrowXEvent canonicalQuery
  ≡
  mahalanobisNumerator wideXEvent canonicalQuery
  →
  ⊥
scaleChangesRadiusAtFixedQuery ()

data BoundarySharpness : Set where
  softBoundary : BoundarySharpness
  mediumBoundary : BoundarySharpness
  hardBoundary : BoundarySharpness

sharpnessCode : BoundarySharpness → Nat
sharpnessCode softBoundary = 1
sharpnessCode mediumBoundary = 2
sharpnessCode hardBoundary = 4

------------------------------------------------------------------------
-- Positive compact finite kernel.  The support test is represented by an
-- explicit radius class rather than treating signed GELU as mass.

data RadiusClass : Set where
  insideEllipsoid : RadiusClass
  boundaryEllipsoid : RadiusClass
  outsideEllipsoid : RadiusClass

positiveKernelValue : BoundarySharpness → RadiusClass → Nat
positiveKernelValue softBoundary insideEllipsoid = 2
positiveKernelValue softBoundary boundaryEllipsoid = 1
positiveKernelValue softBoundary outsideEllipsoid = 0
positiveKernelValue mediumBoundary insideEllipsoid = 3
positiveKernelValue mediumBoundary boundaryEllipsoid = 1
positiveKernelValue mediumBoundary outsideEllipsoid = 0
positiveKernelValue hardBoundary insideEllipsoid = 4
positiveKernelValue hardBoundary boundaryEllipsoid = 1
positiveKernelValue hardBoundary outsideEllipsoid = 0

outsideContributesZero :
  (sharpness : BoundarySharpness) →
  positiveKernelValue sharpness outsideEllipsoid ≡ 0
outsideContributesZero softBoundary = refl
outsideContributesZero mediumBoundary = refl
outsideContributesZero hardBoundary = refl

record EventSample : Set where
  constructor eventSample
  field
    sampleEvent : EllipticEvent2
    sampleSharpness : BoundarySharpness
    sampleRadiusClass : RadiusClass

open EventSample public

sampleContribution : EventSample → Nat
sampleContribution sample =
  eventWeight (sampleEvent sample)
  * positiveKernelValue
      (sampleSharpness sample)
      (sampleRadiusClass sample)

sampleA : EventSample
sampleA = eventSample canonicalEllipticEvent mediumBoundary insideEllipsoid

sampleB : EventSample
sampleB =
  eventSample
    (ellipticEvent2 (point2 6 5) (diagonalScale2 1 4) 2)
    softBoundary
    boundaryEllipsoid

sampleOutside : EventSample
sampleOutside = eventSample canonicalEllipticEvent hardBoundary outsideEllipsoid

finiteEventField : Nat
finiteEventField =
  sampleContribution sampleA
  + sampleContribution sampleB
  + sampleContribution sampleOutside

finiteEventFieldIsSeventeen : finiteEventField ≡ 17
finiteEventFieldIsSeventeen = refl

------------------------------------------------------------------------
-- Class-valued kernel contributions and mass-before-normalisation.

record ClassContribution3 : Set where
  constructor classContribution3
  field
    contributionA : Nat
    contributionB : Nat
    contributionC : Nat

open ClassContribution3 public

scaleClassContribution : Nat → ClassContribution3 → ClassContribution3
scaleClassContribution scalar contribution =
  classContribution3
    (scalar * contributionA contribution)
    (scalar * contributionB contribution)
    (scalar * contributionC contribution)

addClassContribution :
  ClassContribution3 → ClassContribution3 → ClassContribution3
addClassContribution left right =
  classContribution3
    (contributionA left + contributionA right)
    (contributionB left + contributionB right)
    (contributionC left + contributionC right)

classContributionTotal : ClassContribution3 → Nat
classContributionTotal contribution =
  contributionA contribution
  + contributionB contribution
  + contributionC contribution

sampleAClasses : ClassContribution3
sampleAClasses =
  scaleClassContribution
    (sampleContribution sampleA)
    (classContribution3 1 1 0)

sampleBClasses : ClassContribution3
sampleBClasses =
  scaleClassContribution
    (sampleContribution sampleB)
    (classContribution3 0 1 1)

finiteClassField : ClassContribution3
finiteClassField = addClassContribution sampleAClasses sampleBClasses

finiteClassFieldIsFifteenSeventeenTwo :
  finiteClassField ≡ classContribution3 15 17 2
finiteClassFieldIsFifteenSeventeenTwo = refl

finiteClassFieldTotalIsThirtyFour :
  classContributionTotal finiteClassField ≡ 34
finiteClassFieldTotalIsThirtyFour = refl

------------------------------------------------------------------------
-- A finite quadrature tube: event beads at three ordered samples are thickened
-- with tangent-aligned kernel masses.  This is an explicit trajectory source,
-- not a conclusion drawn from timestamps alone.

record TubeQuadrature3 : Set where
  constructor tubeQuadrature3
  field
    tubeStartMass : Nat
    tubeMiddleMass : Nat
    tubeEndMass : Nat
    tangentScale : Nat
    normalScale : Nat

open TubeQuadrature3 public

tubeMass : TubeQuadrature3 → Nat
tubeMass tube =
  tubeStartMass tube
  + tubeMiddleMass tube
  + tubeEndMass tube

canonicalTubeQuadrature : TubeQuadrature3
canonicalTubeQuadrature = tubeQuadrature3 2 5 3 6 1

canonicalTubeMassIsTen : tubeMass canonicalTubeQuadrature ≡ 10
canonicalTubeMassIsTen = refl

canonicalTubeIsTangentElongated :
  tangentScale canonicalTubeQuadrature ≡ 6
  ×
  normalScale canonicalTubeQuadrature ≡ 1
canonicalTubeIsTangentElongated = refl , refl

------------------------------------------------------------------------
-- Discrete normalisation certificate.  A kernel row normalised to denominator
-- six redistributes one event's mass without creating it.

record NormalisedKernelRow3 : Set where
  constructor normalisedKernelRow3
  field
    kernelCell0 : Nat
    kernelCell1 : Nat
    kernelCell2 : Nat
    kernelDenominator : Nat
    kernelRowCloses :
      kernelCell0 + kernelCell1 + kernelCell2 ≡ kernelDenominator

open NormalisedKernelRow3 public

canonicalKernelRow : NormalisedKernelRow3
canonicalKernelRow = normalisedKernelRow3 1 4 1 6 refl

scaledKernelRowMass : Nat → NormalisedKernelRow3 → Nat
scaledKernelRowMass sourceMass row =
  sourceMass
  * (kernelCell0 row + kernelCell1 row + kernelCell2 row)

normalisedRowPreservesScaledMass :
  scaledKernelRowMass 5 canonicalKernelRow
  ≡
  5 * kernelDenominator canonicalKernelRow
normalisedRowPreservesScaledMass = refl

record FiniteAnisotropicKernelBoundary : Set where
  constructor finiteAnisotropicKernelBoundary
  field
    finiteDiagonalWitnessProvesFullSPDCovarianceTheory : Bool
    finiteDiagonalWitnessProvesFullSPDCovarianceTheoryIsFalse :
      finiteDiagonalWitnessProvesFullSPDCovarianceTheory ≡ false

    positiveKernelTableIsRawGELU : Bool
    positiveKernelTableIsRawGELUIsFalse :
      positiveKernelTableIsRawGELU ≡ false

    quadratureTubeIsContinuumLineIntegral : Bool
    quadratureTubeIsContinuumLineIntegralIsFalse :
      quadratureTubeIsContinuumLineIntegral ≡ false

open FiniteAnisotropicKernelBoundary public

canonicalFiniteAnisotropicKernelBoundary :
  FiniteAnisotropicKernelBoundary
canonicalFiniteAnisotropicKernelBoundary =
  finiteAnisotropicKernelBoundary false refl false refl false refl
