module DASHI.Physics.QuantumVacuum.BishopPolarMeasureSourceWeldReducedExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import Real as Bishop

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Analysis.ChangeOfVariablesMeasureSourceAuthorityExact as Source
import DASHI.Analysis.BishopRound11ClassicalTrigObjectWeldExact as TrigWeld
import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Trig
import DASHI.Physics.QuantumVacuum.BishopPolarJacobianSameTrigWeldCompilerExact as Jacobian

------------------------------------------------------------------------
-- REDUCED POLAR MEASURE WELD
--
-- The local calculus no longer belongs in the change-of-variables obligation:
-- one trig-object weld already compiles pointwise derivative entries and
-- det(D Phi)=r on the Bishop carrier.  What remains is genuinely measure
-- theoretic: domain, singular set, measurability/integrability, measure
-- normalization, and same Casimir integrand.
------------------------------------------------------------------------

sourceClaim : Transport.SourceBackedClaim
sourceClaim = record
  { Transport.SourceClaim =
      Source.transformedIntegralFormulaStated
        Source.canonicalChangeOfVariablesAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName =
      Source.sourceName Source.canonicalChangeOfVariablesAuthority
  ; Transport.sourceLocator =
      Source.sourceLocator Source.canonicalChangeOfVariablesAuthority
  ; Transport.reading =
      "Classical multidimensional change-of-variables theorem with absolute Jacobian determinant."
  }

record ReducedBishopPolarMeasureTarget
    (P : Trig.Round11FactorInterchangeProblem)
    (W : TrigWeld.Round11ClassicalTrigObjectWeld P) : Set₁ where
  field
    LocalPolarMeasureChange : Set

    radiusDomainAndAngularDomain : Set
    radiusDomainAndAngularDomainEvidence : radiusDomainAndAngularDomain

    originOrPolarSingularSetTreatment : Set
    originOrPolarSingularSetTreatmentEvidence : originOrPolarSingularSetTreatment

    cartesianAndPolarMeasuresIdentified : Set
    cartesianAndPolarMeasuresIdentifiedEvidence : cartesianAndPolarMeasuresIdentified

    casimirIntegrandMeasurableAndTransportable : Set
    casimirIntegrandMeasurableAndTransportableEvidence :
      casimirIntegrandMeasurableAndTransportable

    sameCasimirTransverseIntegrand : Set
    sameCasimirTransverseIntegrandEvidence : sameCasimirTransverseIntegrand

    measureNormalizationAndAngularRange : Set
    measureNormalizationAndAngularRangeEvidence :
      measureNormalizationAndAngularRange

    SameMeasureTheoreticObject : Set
    sameMeasureTheoreticObjectEvidence : SameMeasureTheoreticObject

    sourceChangeOfVariablesToLocal :
      Transport.SourceClaim sourceClaim →
      SameMeasureTheoreticObject →
      LocalPolarMeasureChange

    reading : String

open ReducedBishopPolarMeasureTarget public

pointwiseBishopJacobian :
  ∀ {P W} →
  (radius theta : Bishop.ℝ) →
  Jacobian.BishopPolarJacobianReceipt P radius theta
pointwiseBishopJacobian {W = W} =
  Jacobian.compileBishopPolarJacobian W

asLocalTarget :
  ∀ {P W} →
  ReducedBishopPolarMeasureTarget P W →
  Transport.LocalTheoremTarget sourceClaim
asLocalTarget T = record
  { Transport.LocalClaim = LocalPolarMeasureChange T
  ; Transport.sameMathematicalObject = SameMeasureTheoreticObject T
  ; Transport.sourceSemanticsToLocal = sourceChangeOfVariablesToLocal T
  ; Transport.reading = reading T
  }

compileLocalPolarMeasureChange :
  ∀ {P W} →
  (T : ReducedBishopPolarMeasureTarget P W) →
  LocalPolarMeasureChange T
compileLocalPolarMeasureChange T =
  Transport.transportSourceBackedTheorem
    sourceClaim
    (asLocalTarget T)
    (record
      { Transport.objectWeld = sameMeasureTheoreticObjectEvidence T
      })

record ReverseReducedPolarMeasureObligations : Set where
  field
    radiusAndAngleDomain : Set
    polarOriginNullOrSingularSetTreatment : Set
    cartesianPolarMeasureIdentification : Set
    integrandMeasurabilityAndTransport : Set
    sameCasimirIntegrand : Set
    normalizationAndAngularRange : Set

open ReverseReducedPolarMeasureObligations public

data TrigDerivativeReceiptStillRequiredAsIndependentMeasureLeaf : Set where
data DeterminantAlgebraStillRequiredAsIndependentMeasureLeaf : Set where

trigDerivativeAlreadyUpstream :
  TrigDerivativeReceiptStillRequiredAsIndependentMeasureLeaf → ⊥
trigDerivativeAlreadyUpstream ()

determinantAlreadyUpstream :
  DeterminantAlgebraStillRequiredAsIndependentMeasureLeaf → ⊥
determinantAlreadyUpstream ()

record Status : Set where
  field
    changeOfVariablesSourceBacked : Bool
    bishopPointwiseJacobianCompilerOwned : Bool
    derivativeLeafPrunedFromMeasureCutset : Bool
    determinantLeafPrunedFromMeasureCutset : Bool
    measureTheoreticWeldClosed : Bool

    changeOfVariablesSourceBackedIsTrue : changeOfVariablesSourceBacked ≡ true
    bishopPointwiseJacobianCompilerOwnedIsTrue :
      bishopPointwiseJacobianCompilerOwned ≡ true
    derivativeLeafPrunedFromMeasureCutsetIsTrue :
      derivativeLeafPrunedFromMeasureCutset ≡ true
    determinantLeafPrunedFromMeasureCutsetIsTrue :
      determinantLeafPrunedFromMeasureCutset ≡ true
    measureTheoreticWeldClosedIsFalse : measureTheoreticWeldClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { changeOfVariablesSourceBacked = true
  ; bishopPointwiseJacobianCompilerOwned = true
  ; derivativeLeafPrunedFromMeasureCutset = true
  ; determinantLeafPrunedFromMeasureCutset = true
  ; measureTheoreticWeldClosed = false
  ; changeOfVariablesSourceBackedIsTrue = refl
  ; bishopPointwiseJacobianCompilerOwnedIsTrue = refl
  ; derivativeLeafPrunedFromMeasureCutsetIsTrue = refl
  ; determinantLeafPrunedFromMeasureCutsetIsTrue = refl
  ; measureTheoreticWeldClosedIsFalse = refl
  }
