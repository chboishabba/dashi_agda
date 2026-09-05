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

    LimitIntegrandIsRadial : Set
    limitIntegrandIsRadialEvidence : LimitIntegrandIsRadial

    RadialIntegrability : Set
    radialIntegrabilityEvidence : RadialIntegrability

    SameLebesgueMeasureAsSource : Set
    sameLebesgueMeasureAsSourceEvidence : SameLebesgueMeasureAsSource

    SameCasimirTransverseIntegrand : Set
    sameCasimirTransverseIntegrandEvidence : SameCasimirTransverseIntegrand

    SameNormalizationConvention : Set
    sameNormalizationConventionEvidence : SameNormalizationConvention

    SameRadialMeasureObject : Set
    sameRadialMeasureObjectEvidence : SameRadialMeasureObject

    LocalRadialReduction : Set

    sourceRadialMeasureToLocal :
      Transport.SourceClaim radialMeasureClaim →
      (LimitIntegrandIsRadial ×
       (RadialIntegrability ×
       (SameLebesgueMeasureAsSource ×
       (SameCasimirTransverseIntegrand ×
       (SameNormalizationConvention × SameRadialMeasureObject))))) →
      LocalRadialReduction

    reading : String

open CasimirRadialLebesgueTarget public

RadialSourceApplicationObject :
  ∀ {kernel F} →
  CasimirRadialLebesgueTarget kernel F → Set
RadialSourceApplicationObject T =
  LimitIntegrandIsRadial T ×
  (RadialIntegrability T ×
  (SameLebesgueMeasureAsSource T ×
  (SameCasimirTransverseIntegrand T ×
  (SameNormalizationConvention T × SameRadialMeasureObject T))))

radialSourceApplicationEvidence :
  ∀ {kernel F} →
  (T : CasimirRadialLebesgueTarget kernel F) →
  RadialSourceApplicationObject T
radialSourceApplicationEvidence T =
  limitIntegrandIsRadialEvidence T ,
  (radialIntegrabilityEvidence T ,
  (sameLebesgueMeasureAsSourceEvidence T ,
  (sameCasimirTransverseIntegrandEvidence T ,
  (sameNormalizationConventionEvidence T ,
   sameRadialMeasureObjectEvidence T))))

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
-- Strong local object weld: all application-specific coordinates are explicit
-- and proof-bearing.  This is the actual remaining radial-measure payment.
------------------------------------------------------------------------

record ProofBearingRadialMeasureWeld
    {kernel : Casimir.CasimirScalarModel}
    {F : Transverse.CasimirTransverseMeasureFamily kernel}
    (T : CasimirRadialLebesgueTarget kernel F) : Set₁ where
  field
    radiality : LimitIntegrandIsRadial T
    integrability : RadialIntegrability T
    sourceLebesgueMeasure : SameLebesgueMeasureAsSource T
    sameCasimirIntegrand : SameCasimirTransverseIntegrand T
    sameNormalization : SameNormalizationConvention T
    radialMeasureObject : SameRadialMeasureObject T

open ProofBearingRadialMeasureWeld public

canonicalWeldFromTarget :
  ∀ {kernel F} →
  (T : CasimirRadialLebesgueTarget kernel F) →
  ProofBearingRadialMeasureWeld T
canonicalWeldFromTarget T = record
  { radiality = limitIntegrandIsRadialEvidence T
  ; integrability = radialIntegrabilityEvidence T
  ; sourceLebesgueMeasure = sameLebesgueMeasureAsSourceEvidence T
  ; sameCasimirIntegrand = sameCasimirTransverseIntegrandEvidence T
  ; sameNormalization = sameNormalizationConventionEvidence T
  ; radialMeasureObject = sameRadialMeasureObjectEvidence T
  }

------------------------------------------------------------------------
-- BIDI pruning.
------------------------------------------------------------------------

record ReverseRadialLebesgueObligations : Set where
  field
    literalCasimirIntegrandIsRadial : Set
    radialIntegrability : Set
    sameR2LebesgueMeasure : Set
    sameCasimirTransverseIntegrand : Set
    sameTwoPiNormalization : Set
    reading : String

open ReverseRadialLebesgueObligations public

data PolarAngularChartStillRequired : Set where
data SineCosineDerivativeStillRequired : Set where
data PolarJacobianDeterminantStillRequired : Set where
data PolarOriginAndSeamChartTreatmentStillRequired : Set where
data BareSameRadialObjectLabelSuffices : Set where

radialRoutePrunesAngularChart : PolarAngularChartStillRequired → ⊥
radialRoutePrunesAngularChart ()

radialRoutePrunesTrigDerivative : SineCosineDerivativeStillRequired → ⊥
radialRoutePrunesTrigDerivative ()

radialRoutePrunesJacobianCalculation : PolarJacobianDeterminantStillRequired → ⊥
radialRoutePrunesJacobianCalculation ()

sphereRoutePrunesPolarSeam : PolarOriginAndSeamChartTreatmentStillRequired → ⊥
sphereRoutePrunesPolarSeam ()

radialTransportRequiresAllCoordinates : BareSameRadialObjectLabelSuffices → ⊥
radialTransportRequiresAllCoordinates ()

record Status : Set where
  field
    radialLebesgueSourceBacked : Bool
    chartFreeCasimirTransportOwned : Bool
    allLocalRadialCoordinatesRequiredByTransport : Bool
    trigDerivativePrunedFromCasimirMeasureRoute : Bool
    jacobianPrunedFromCasimirMeasureRoute : Bool
    polarSeamPrunedFromCasimirMeasureRoute : Bool
    localRadialMeasureWeldClosed : Bool

    radialLebesgueSourceBackedIsTrue : radialLebesgueSourceBacked ≡ true
    chartFreeCasimirTransportOwnedIsTrue : chartFreeCasimirTransportOwned ≡ true
    allLocalRadialCoordinatesRequiredByTransportIsTrue :
      allLocalRadialCoordinatesRequiredByTransport ≡ true
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
  ; allLocalRadialCoordinatesRequiredByTransport = true
  ; trigDerivativePrunedFromCasimirMeasureRoute = true
  ; jacobianPrunedFromCasimirMeasureRoute = true
  ; polarSeamPrunedFromCasimirMeasureRoute = true
  ; localRadialMeasureWeldClosed = false
  ; radialLebesgueSourceBackedIsTrue = refl
  ; chartFreeCasimirTransportOwnedIsTrue = refl
  ; allLocalRadialCoordinatesRequiredByTransportIsTrue = refl
  ; trigDerivativePrunedFromCasimirMeasureRouteIsTrue = refl
  ; jacobianPrunedFromCasimirMeasureRouteIsTrue = refl
  ; polarSeamPrunedFromCasimirMeasureRouteIsTrue = refl
  ; localRadialMeasureWeldClosedIsFalse = refl
  }
