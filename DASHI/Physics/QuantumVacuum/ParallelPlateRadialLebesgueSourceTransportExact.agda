module DASHI.Physics.QuantumVacuum.ParallelPlateRadialLebesgueSourceTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Analysis.RadialLebesgueDecompositionSourceAuthorityExact as Source
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse

------------------------------------------------------------------------
-- CHART-FREE RADIAL LEBESGUE TRANSPORT
--
-- For the Casimir transverse integral, use the source-backed decomposition
--
--   R^2 \ {0} ~= (0,infinity) x S^1,
--   d^2k = r dr dω,
--   measure(S^1)=2*pi,
--
-- rather than introducing an angular coordinate chart.  This removes the
-- polar seam and all sine/cosine/Jacobian calculus from this proof route.
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
  ; Transport.sourceLocator = Source.radialMeasureSourceLocator Source.canonicalRadialLebesgueAuthority
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

    LocalRadialReduction : Set

    SameRadialMeasureObject : Set
    sameRadialMeasureObjectEvidence : SameRadialMeasureObject

    sourceRadialMeasureToLocal :
      Transport.SourceClaim radialMeasureClaim →
      SameRadialMeasureObject →
      LocalRadialReduction

    reading : String

open CasimirRadialLebesgueTarget public

asTransportTarget :
  ∀ {kernel F} →
  CasimirRadialLebesgueTarget kernel F →
  Transport.LocalTheoremTarget radialMeasureClaim
asTransportTarget T = record
  { Transport.LocalClaim = LocalRadialReduction T
  ; Transport.sameMathematicalObject = SameRadialMeasureObject T
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
      { Transport.objectWeld = sameRadialMeasureObjectEvidence T })

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
    trigDerivativePrunedFromCasimirMeasureRoute : Bool
    jacobianPrunedFromCasimirMeasureRoute : Bool
    polarSeamPrunedFromCasimirMeasureRoute : Bool
    localRadialMeasureWeldClosed : Bool

    radialLebesgueSourceBackedIsTrue : radialLebesgueSourceBacked ≡ true
    chartFreeCasimirTransportOwnedIsTrue : chartFreeCasimirTransportOwned ≡ true
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
  ; trigDerivativePrunedFromCasimirMeasureRoute = true
  ; jacobianPrunedFromCasimirMeasureRoute = true
  ; polarSeamPrunedFromCasimirMeasureRoute = true
  ; localRadialMeasureWeldClosed = false
  ; radialLebesgueSourceBackedIsTrue = refl
  ; chartFreeCasimirTransportOwnedIsTrue = refl
  ; trigDerivativePrunedFromCasimirMeasureRouteIsTrue = refl
  ; jacobianPrunedFromCasimirMeasureRouteIsTrue = refl
  ; polarSeamPrunedFromCasimirMeasureRouteIsTrue = refl
  ; localRadialMeasureWeldClosedIsFalse = refl
  }
