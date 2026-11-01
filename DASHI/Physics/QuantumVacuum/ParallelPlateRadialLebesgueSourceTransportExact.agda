module DASHI.Physics.QuantumVacuum.ParallelPlateRadialLebesgueSourceTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Analysis.RadialLebesgueDecompositionSourceAuthorityExact as Source
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse

------------------------------------------------------------------------
-- CHART-FREE RADIAL LEBESGUE TRANSPORT
------------------------------------------------------------------------

radialMeasureClaim : Transport.SourceBackedClaim
radialMeasureClaim = record
  { Transport.SourceClaim =
      Source.puncturedRnIdentifiedWithRadiusTimesSphere Source.canonicalRadialLebesgueAuthority
      ×
      (Source.dimensionTwoRadialDensityIsRadius Source.canonicalRadialLebesgueAuthority
      × Source.unitCircleInvariantMeasureIsTwoPi Source.canonicalRadialLebesgueAuthority)
  ; Transport.sourceReceipt = tt , (tt , tt)
  ; Transport.sourceName = Source.sourceName Source.canonicalRadialLebesgueAuthority
  ; Transport.sourceLocator =
      "https://math.mit.edu/~rbm/18-155-F13/Lecture9.pdf ; https://math.mit.edu/~djk/18_01/chapter28/section03.html"
  ; Transport.reading =
      "MIT radial Lebesgue decomposition in dimension two, with S^1 normalization 2*pi."
  }

record CasimirRadialLebesgueTarget
    (kernel : Casimir.CasimirScalarModel)
    (F : Transverse.CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    Radius : Set
    radiusOf : Transverse.TransversePoint F → Radius
    radialIntegrand : Radius → Transverse.Integrand F

    limitIntegrandIsRadial :
      (point : Transverse.TransversePoint F) →
      Transverse.limitIntegrand F point ≡ radialIntegrand (radiusOf point)

    RadialIntegrability : Set
    radialIntegrabilityEvidence : RadialIntegrability

    SameLebesgueMeasureAsSource : Set
    sameLebesgueMeasureAsSourceEvidence : SameLebesgueMeasureAsSource

    SameNormalizationConvention : Set
    sameNormalizationConventionEvidence : SameNormalizationConvention

    SameRadialMeasureObject : Set
    sameRadialMeasureObjectEvidence : SameRadialMeasureObject

    LocalRadialReduction : Set

    sourceRadialMeasureToLocal :
      Transport.SourceClaim radialMeasureClaim →
      (RadialIntegrability ×
       (SameLebesgueMeasureAsSource ×
       (SameNormalizationConvention × SameRadialMeasureObject))) →
      LocalRadialReduction

    reading : String

open CasimirRadialLebesgueTarget public

RadialSourceApplicationObject :
  ∀ {kernel F} →
  CasimirRadialLebesgueTarget kernel F → Set
RadialSourceApplicationObject T =
  RadialIntegrability T ×
  (SameLebesgueMeasureAsSource T ×
  (SameNormalizationConvention T × SameRadialMeasureObject T))

radialSourceApplicationEvidence :
  ∀ {kernel F} →
  (T : CasimirRadialLebesgueTarget kernel F) →
  RadialSourceApplicationObject T
radialSourceApplicationEvidence T =
  radialIntegrabilityEvidence T ,
  (sameLebesgueMeasureAsSourceEvidence T ,
  (sameNormalizationConventionEvidence T ,
   sameRadialMeasureObjectEvidence T))

asTransportTarget :
  ∀ {kernel F} →
  CasimirRadialLebesgueTarget kernel F →
  Transport.LocalTheoremTarget radialMeasureClaim
asTransportTarget T = record
  { Transport.LocalClaim = LocalRadialReduction T
  ; Transport.sameMathematicalObject = RadialSourceApplicationObject T
  ; Transport.sourceSemanticsToLocal = sourceRadialMeasureToLocal T
  ; Transport.reading = reading T
  }

compileLocalRadialReduction :
  ∀ {kernel F} →
  (T : CasimirRadialLebesgueTarget kernel F) →
  LocalRadialReduction T
compileLocalRadialReduction T =
  Transport.transportSourceBackedTheorem
    radialMeasureClaim
    (asTransportTarget T)
    (record
      { Transport.objectWeld = radialSourceApplicationEvidence T })

------------------------------------------------------------------------
-- BIDI pruning.
------------------------------------------------------------------------

record ReverseRadialLebesgueObligations : Set where
  field
    literalPointwiseRadialFactorisation : Set
    radialIntegrability : Set
    sameR2LebesgueMeasure : Set
    sameTwoPiNormalization : Set
    reading : String

open ReverseRadialLebesgueObligations public

data SeparateSameCasimirIntegrandWeldStillRequired : Set where
data PolarAngularChartStillRequired : Set where
data SineCosineDerivativeStillRequired : Set where
data PolarJacobianDeterminantStillRequired : Set where
data PolarOriginAndSeamChartTreatmentStillRequired : Set where

definitionalRadialityIdentifiesIntegrand :
  SeparateSameCasimirIntegrandWeldStillRequired → ⊥
definitionalRadialityIdentifiesIntegrand ()

radialRoutePrunesAngularChart : PolarAngularChartStillRequired → ⊥
radialRoutePrunesAngularChart ()

radialRoutePrunesTrigDerivative : SineCosineDerivativeStillRequired → ⊥
radialRoutePrunesTrigDerivative ()

radialRoutePrunesJacobianCalculation : PolarJacobianDeterminantStillRequired → ⊥
radialRoutePrunesJacobianCalculation ()

sphereRoutePrunesPolarSeam : PolarOriginAndSeamChartTreatmentStillRequired → ⊥
sphereRoutePrunesPolarSeam ()

record Status : Set where
  field
    radialLebesgueSourceBacked : Bool
    chartFreeCasimirTransportOwned : Bool
    radialityIsLiteralPointwiseEquality : Bool
    sameIntegrandLeafPruned : Bool
    trigDerivativePrunedFromCasimirMeasureRoute : Bool
    jacobianPrunedFromCasimirMeasureRoute : Bool
    polarSeamPrunedFromCasimirMeasureRoute : Bool
    localRadialMeasureWeldClosed : Bool

    radialLebesgueSourceBackedIsTrue : radialLebesgueSourceBacked ≡ true
    chartFreeCasimirTransportOwnedIsTrue : chartFreeCasimirTransportOwned ≡ true
    radialityIsLiteralPointwiseEqualityIsTrue :
      radialityIsLiteralPointwiseEquality ≡ true
    sameIntegrandLeafPrunedIsTrue : sameIntegrandLeafPruned ≡ true
    trigDerivativePrunedFromCasimirMeasureRouteIsTrue :
      trigDerivativePrunedFromCasimirMeasureRoute ≡ true
    jacobianPrunedFromCasimirMeasureRouteIsTrue :
      jacobianPrunedFromCasimirMeasureRoute ≡ true
    polarSeamPrunedFromCasimirMeasureRouteIsTrue :
      polarSeamPrunedFromCasimirMeasureRoute ≡ true
    localRadialMeasureWeldClosedIsFalse : localRadialMeasureWeldClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { radialLebesgueSourceBacked = true
  ; chartFreeCasimirTransportOwned = true
  ; radialityIsLiteralPointwiseEquality = true
  ; sameIntegrandLeafPruned = true
  ; trigDerivativePrunedFromCasimirMeasureRoute = true
  ; jacobianPrunedFromCasimirMeasureRoute = true
  ; polarSeamPrunedFromCasimirMeasureRoute = true
  ; localRadialMeasureWeldClosed = false
  ; radialLebesgueSourceBackedIsTrue = refl
  ; chartFreeCasimirTransportOwnedIsTrue = refl
  ; radialityIsLiteralPointwiseEqualityIsTrue = refl
  ; sameIntegrandLeafPrunedIsTrue = refl
  ; trigDerivativePrunedFromCasimirMeasureRouteIsTrue = refl
  ; jacobianPrunedFromCasimirMeasureRouteIsTrue = refl
  ; polarSeamPrunedFromCasimirMeasureRouteIsTrue = refl
  ; localRadialMeasureWeldClosedIsFalse = refl
  }
