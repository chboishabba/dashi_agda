module DASHI.Analysis.BishopRound11PowerSeriesDifferentiationSourceTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Analysis.PowerSeriesTermwiseDifferentiationSourceAuthorityExact as Source
import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Round11

------------------------------------------------------------------------
-- DLMF POWER-SERIES DIFFERENTIATION -> ROUND11 BISHOP FACTOR DERIVATIVE
--
-- The source theorem is classical and application-neutral.  The local target
-- is the concrete Round11 sine/cosine factor-derivative authority.  Therefore
-- the only legal bridge is an explicit same-object/semantics weld.
------------------------------------------------------------------------

sourceClaim : Transport.SourceBackedClaim
sourceClaim = record
  { Transport.SourceClaim =
      Source.termwiseDifferentiationInsideRadius
        Source.canonicalPowerSeriesDifferentiationAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName =
      Source.sourceName Source.canonicalPowerSeriesDifferentiationAuthority
  ; Transport.sourceLocator =
      Source.sourceLocator Source.canonicalPowerSeriesDifferentiationAuthority
  ; Transport.reading =
      "DLMF §1.9(vi) termwise power-series differentiation authority."
  }

record Round11PowerSeriesSourceWeld
    (P : Round11.Round11FactorInterchangeProblem) : Set₁ where
  field
    samePowerSeriesCoefficientsAndCentre : Set
    sameRadiusOrInteriorDomain : Set
    sameLimitFunctions : Set
    classicalDerivativeMatchesBishopFactorDerivative : Set
    cosineZeroModeAndShiftMatchSourceIndexing : Set

    sameMathematicalObject : Set

    sourceToRound11Authority :
      Transport.SourceClaim sourceClaim →
      sameMathematicalObject →
      Round11.Round11FactorInterchangeAuthority P

    reading : String

open Round11PowerSeriesSourceWeld public

asLocalTarget :
  (P : Round11.Round11FactorInterchangeProblem) →
  Round11PowerSeriesSourceWeld P →
  Transport.LocalTheoremTarget sourceClaim
asLocalTarget P W = record
  { Transport.LocalClaim = Round11.Round11FactorInterchangeAuthority P
  ; Transport.sameMathematicalObject = sameMathematicalObject W
  ; Transport.sourceSemanticsToLocal = sourceToRound11Authority W
  ; Transport.reading = reading W
  }

compileRound11FactorInterchangeAuthority :
  (P : Round11.Round11FactorInterchangeProblem) →
  (W : Round11PowerSeriesSourceWeld P) →
  sameMathematicalObject W →
  Round11.Round11FactorInterchangeAuthority P
compileRound11FactorInterchangeAuthority P W weld =
  Transport.transportSourceBackedTheorem
    sourceClaim
    (asLocalTarget P W)
    (record { Transport.objectWeld = weld })

record ReverseSourceWeldObligations : Set where
  field
    literalRound11CoefficientsIdentified : Set
    centreAndIndexingIdentified : Set
    sourceInteriorContainsRequestedBishopPoints : Set
    sourceDerivativeSemanticsMatchesFactorDerivative : Set
    sameLimitFunctions : Set

open ReverseSourceWeldObligations public

data DLMFCitationAutomaticallyClosesRound11Derivative : Set where

data MatchingCoefficientFormulaAutomaticallyIdentifiesDerivativeSemantics : Set where

citationNeedsLocalWeld :
  DLMFCitationAutomaticallyClosesRound11Derivative → ⊥
citationNeedsLocalWeld ()

coefficientMatchNeedsDerivativeWeld :
  MatchingCoefficientFormulaAutomaticallyIdentifiesDerivativeSemantics → ⊥
coefficientMatchNeedsDerivativeWeld ()

record Status : Set where
  field
    dlmfPowerSeriesDifferentiationSourceBacked : Bool
    genericSourceTransportCompilerOwned : Bool
    round11LocalTargetOwned : Bool
    round11SameObjectWeldClosed : Bool

    dlmfPowerSeriesDifferentiationSourceBackedIsTrue :
      dlmfPowerSeriesDifferentiationSourceBacked ≡ true
    genericSourceTransportCompilerOwnedIsTrue :
      genericSourceTransportCompilerOwned ≡ true
    round11LocalTargetOwnedIsTrue : round11LocalTargetOwned ≡ true
    round11SameObjectWeldClosedIsFalse : round11SameObjectWeldClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { dlmfPowerSeriesDifferentiationSourceBacked = true
  ; genericSourceTransportCompilerOwned = true
  ; round11LocalTargetOwned = true
  ; round11SameObjectWeldClosed = false
  ; dlmfPowerSeriesDifferentiationSourceBackedIsTrue = refl
  ; genericSourceTransportCompilerOwnedIsTrue = refl
  ; round11LocalTargetOwnedIsTrue = refl
  ; round11SameObjectWeldClosedIsFalse = refl
  }
