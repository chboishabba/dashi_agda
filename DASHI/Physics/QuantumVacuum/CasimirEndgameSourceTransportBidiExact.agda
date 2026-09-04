module DASHI.Physics.QuantumVacuum.CasimirEndgameSourceTransportBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Analysis.FourierTrigonometricCompletenessSourceAuthorityExact as Fourier
import DASHI.Analysis.ChangeOfVariablesMeasureSourceAuthorityExact as Change
import DASHI.Analysis.ZetaEulerMaclaurinContinuationSourceAuthorityExact as ZetaEM

------------------------------------------------------------------------
-- COMMON BIDI SOURCE-TRANSPORT GEOMETRY FOR THE THREE CLASSICAL ENDGAME
-- THEOREMS.  Only theorem shape is shared; application receipts remain local.
------------------------------------------------------------------------

fourierSourceClaim : Transport.SourceBackedClaim
fourierSourceClaim = record
  { Transport.SourceClaim =
      Fourier.orthogonalCompletenessAvailable
        Fourier.canonicalFourierCompletenessAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName =
      Fourier.sourceName Fourier.canonicalFourierCompletenessAuthority
  ; Transport.sourceLocator =
      Fourier.sourceLocator Fourier.canonicalFourierCompletenessAuthority
  ; Transport.reading =
      "Classical trigonometric L2 completeness as bounded source authority."
  }

changeOfVariablesSourceClaim : Transport.SourceBackedClaim
changeOfVariablesSourceClaim = record
  { Transport.SourceClaim =
      Change.transformedIntegralFormulaStated
        Change.canonicalChangeOfVariablesAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName =
      Change.sourceName Change.canonicalChangeOfVariablesAuthority
  ; Transport.sourceLocator =
      Change.sourceLocator Change.canonicalChangeOfVariablesAuthority
  ; Transport.reading =
      "Multidimensional change-of-variables theorem as bounded source authority."
  }

zetaEulerMaclaurinSourceClaim : Transport.SourceBackedClaim
zetaEulerMaclaurinSourceClaim = record
  { Transport.SourceClaim =
      ZetaEM.eulerMaclaurinRepresentationStated
        ZetaEM.canonicalZetaEulerMaclaurinAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName =
      ZetaEM.sourceName ZetaEM.canonicalZetaEulerMaclaurinAuthority
  ; Transport.sourceLocator =
      ZetaEM.sourceLocator ZetaEM.canonicalZetaEulerMaclaurinAuthority
  ; Transport.reading =
      "Euler--Maclaurin continuation representation as bounded source authority."
  }

record MaxwellCompletenessLocalTarget : Set₁ where
  field
    LocalTETMCompleteness : Set
    samePlateHilbertCarrierAndBoundaryDomain : Set
    transportClassicalCompletenessToTETM :
      Fourier.orthogonalCompletenessAvailable
        Fourier.canonicalFourierCompletenessAuthority →
      samePlateHilbertCarrierAndBoundaryDomain →
      LocalTETMCompleteness
    reading : String

open MaxwellCompletenessLocalTarget public

asMaxwellCompletenessTarget :
  MaxwellCompletenessLocalTarget →
  Transport.LocalTheoremTarget fourierSourceClaim
asMaxwellCompletenessTarget T = record
  { Transport.LocalClaim = LocalTETMCompleteness T
  ; Transport.sameMathematicalObject = samePlateHilbertCarrierAndBoundaryDomain T
  ; Transport.sourceSemanticsToLocal = transportClassicalCompletenessToTETM T
  ; Transport.reading = reading T
  }

record PolarMeasureLocalTarget : Set₁ where
  field
    LocalPolarChangeOfVariables : Set
    sameEuclideanMapMeasureJacobianAndIntegrand : Set
    transportChangeOfVariablesToPolarCasimir :
      Change.transformedIntegralFormulaStated
        Change.canonicalChangeOfVariablesAuthority →
      sameEuclideanMapMeasureJacobianAndIntegrand →
      LocalPolarChangeOfVariables
    reading : String

open PolarMeasureLocalTarget public

asPolarMeasureTarget :
  PolarMeasureLocalTarget →
  Transport.LocalTheoremTarget changeOfVariablesSourceClaim
asPolarMeasureTarget T = record
  { Transport.LocalClaim = LocalPolarChangeOfVariables T
  ; Transport.sameMathematicalObject = sameEuclideanMapMeasureJacobianAndIntegrand T
  ; Transport.sourceSemanticsToLocal = transportChangeOfVariablesToPolarCasimir T
  ; Transport.reading = reading T
  }

record ZetaContinuationLocalTarget : Set₁ where
  field
    LocalContinuationAtMinusThree : Set
    sameZetaFunctionBernoulliNormalisationAndRemainderIntegral : Set
    transportEulerMaclaurinToLocalZeta :
      ZetaEM.eulerMaclaurinRepresentationStated
        ZetaEM.canonicalZetaEulerMaclaurinAuthority →
      sameZetaFunctionBernoulliNormalisationAndRemainderIntegral →
      LocalContinuationAtMinusThree
    reading : String

open ZetaContinuationLocalTarget public

asZetaContinuationTarget :
  ZetaContinuationLocalTarget →
  Transport.LocalTheoremTarget zetaEulerMaclaurinSourceClaim
asZetaContinuationTarget T = record
  { Transport.LocalClaim = LocalContinuationAtMinusThree T
  ; Transport.sameMathematicalObject =
      sameZetaFunctionBernoulliNormalisationAndRemainderIntegral T
  ; Transport.sourceSemanticsToLocal = transportEulerMaclaurinToLocalZeta T
  ; Transport.reading = reading T
  }

data FourierReceiptAutomaticallyClosesPolarMeasure : Set where
data PolarMeasureReceiptAutomaticallyClosesZetaContinuation : Set where
data ZetaContinuationReceiptAutomaticallyClosesTETMCompleteness : Set where

noFourierToMeasureLeak : FourierReceiptAutomaticallyClosesPolarMeasure → ⊥
noFourierToMeasureLeak ()

noMeasureToZetaLeak : PolarMeasureReceiptAutomaticallyClosesZetaContinuation → ⊥
noMeasureToZetaLeak ()

noZetaToMaxwellLeak : ZetaContinuationReceiptAutomaticallyClosesTETMCompleteness → ⊥
noZetaToMaxwellLeak ()
