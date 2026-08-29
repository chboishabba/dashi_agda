module DASHI.Analysis.RiemannAristotleSharedWindowCertificateExact where

------------------------------------------------------------------------
-- SHARED NORMALIZED-WINDOW CERTIFICATE
--
-- Cross-pollination returned from the Erdos factor-pair and Wette 9.1.5 lanes:
-- construct the exact shared object once, then let every residual/margin consumer
-- depend on that same certificate rather than reassembling loosely related facts.
--
-- This is an Agda architecture owner.  It does not claim that Lean theorem terms
-- have been transported into Agda, nor does it close Aristotle's analytic endpoint
-- comparison by itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record NormalizedWindowTaperCertificate : Set₁ where
  field
    Taper Scalar : Set
    taper : Taper
    lowerEndpoint upperEndpoint : Scalar
    continuous compactSupport nonnegative supportContained positiveMass unitMass : Set
    boundedReading : String

open NormalizedWindowTaperCertificate public

record NormalizedNarrowWindowTripleCertificate : Set₁ where
  field
    Scalar Taper : Set
    p q0 q1 : Taper
    al0 be0 al1 be1 al2 be2 : Scalar
    pNormalized q0Normalized q1Normalized : NormalizedWindowTaperCertificate
    lowPositive lowOrdered lowMiddleSeparated middleOrdered middleTopSeparated : Set
    sameObjectReading : String

open NormalizedNarrowWindowTripleCertificate public

------------------------------------------------------------------------
-- Every endpoint response bound consumed downstream is indexed by the same exact
-- triple certificate.  The fields are theorem sockets, not manufactured truths.
------------------------------------------------------------------------

record SharedResponseEnvelope
    (w : NormalizedNarrowWindowTripleCertificate) : Set₁ where
  field
    ResponseBound : Set
    pAtLow pAtHigh q0AtLow q0AtHigh q1AtLow q1AtHigh : ResponseBound
    cross0AtLow cross0AtHigh cross1AtLow cross1AtHigh : ResponseBound
    allBoundsReferToSameWindowTriple : Set
    boundedReading : String

open SharedResponseEnvelope public

record SharedWindowBudgetCutset : Set where
  constructor shared-window-budget-cutset
  field
    windowConstructionSharedOnce : Bool
    windowConstructionSharedOnceIsTrue : windowConstructionSharedOnce ≡ true
    responseEnvelopeSharedOnce : Bool
    responseEnvelopeSharedOnceIsTrue : responseEnvelopeSharedOnce ≡ true
    endpointPolynomialTransportMechanical : Bool
    endpointPolynomialTransportMechanicalIsTrue : endpointPolynomialTransportMechanical ≡ true
    oneSymbolicBudgetComparisonRemains : Bool
    oneSymbolicBudgetComparisonRemainsIsTrue : oneSymbolicBudgetComparisonRemains ≡ true
    endpointComparisonDerivedHere : Bool
    endpointComparisonDerivedHereIsFalse : endpointComparisonDerivedHere ≡ false
    leanProofTransportedIntoAgda : Bool
    leanProofTransportedIntoAgdaIsFalse : leanProofTransportedIntoAgda ≡ false

canonicalSharedWindowBudgetCutset : SharedWindowBudgetCutset
canonicalSharedWindowBudgetCutset =
  shared-window-budget-cutset
    true refl true refl true refl true refl false refl false refl
