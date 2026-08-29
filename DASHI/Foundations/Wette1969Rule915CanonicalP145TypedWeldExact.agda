module DASHI.Foundations.Wette1969Rule915CanonicalP145TypedWeldExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: CANONICAL p.145 -> EXISTING TYPED ARCHITECTURE
--
-- The canonical p.145 premise vector is not a parallel semantics. This module
-- instantiates the repository's existing Rule915FirstSevenParameters and
-- Rule915LaterParameters with exactly the nineteen source metavariables and the
-- dense p.145 words, then proves pointwise identity at every one of the 27 slots.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915CanonicalP145PremisesExact as P145

canonicalFirstSeven : Rule915.Rule915FirstSevenParameters
canonicalFirstSeven =
  Rule915.rule915FirstSevenParameters
    P145.V P145.W P145.W2 P145.V2 P145.V1 P145.W1 P145.U P145.U1

canonicalLater : Later.Rule915LaterParameters
canonicalLater =
  Later.rule915LaterParameters
    P145.V
    P145.U1
    P145.U
    P145.W2
    P145.W3
    P145.W4
    P145.W5
    P145.V2
    P145.V3
    P145.V4
    P145.V1
    P145.W1
    P145.contextU1V1W1
    P145.V3
    P145.contextV4V1W1
    P145.contextW4W5
    P145.contextU1V1W1
    P145.V5
    P145.abbreviation16Word
    P145.U2
    P145.abbreviation17Word
    P145.U3
    P145.abbreviation26Word
    P145.U6
    P145.U4
    P145.U5
    P145.premise18ConsequentWord
    P145.premise27ConsequentWord

canonicalExistingTypedTranscription : Rule915.Rule915PremiseTranscription
canonicalExistingTypedTranscription =
  Later.completeTypedTranscription canonicalFirstSeven canonicalLater

canonicalExistingTypedPremiseMatchesP145 :
  (slot : Critical.Premise915) →
  Rule915.premiseAt canonicalExistingTypedTranscription slot
    ≡ P145.p145Premise slot
canonicalExistingTypedPremiseMatchesP145 Critical.p01 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p02 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p03 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p04 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p05 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p06 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p07 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p08 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p09 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p10 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p11 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p12 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p13 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p14 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p15 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p16 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p17 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p18 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p19 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p20 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p21 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p22 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p23 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p24 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p25 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p26 = refl
canonicalExistingTypedPremiseMatchesP145 Critical.p27 = refl

canonicalTypedPremise18IsExactP145 :
  Rule915.premiseAt canonicalExistingTypedTranscription Critical.p18
    ≡ P145.p145Premise Critical.p18
canonicalTypedPremise18IsExactP145 = refl

canonicalTypedPremise27IsExactP145 :
  Rule915.premiseAt canonicalExistingTypedTranscription Critical.p27
    ≡ P145.p145Premise Critical.p27
canonicalTypedPremise27IsExactP145 = refl

record Wette1969Rule915CanonicalP145TypedWeldBoundary : Set where
  constructor wette1969Rule915CanonicalP145TypedWeldBoundary
  field
    canonicalP145ObjectUsesExistingFirstSevenOwner : Bool
    canonicalP145ObjectUsesExistingFirstSevenOwnerIsTrue :
      canonicalP145ObjectUsesExistingFirstSevenOwner ≡ true
    canonicalP145ObjectUsesExistingLaterPremiseOwner : Bool
    canonicalP145ObjectUsesExistingLaterPremiseOwnerIsTrue :
      canonicalP145ObjectUsesExistingLaterPremiseOwner ≡ true
    allTwentySevenExistingTypedSlotsPointwiseMatchP145 : Bool
    allTwentySevenExistingTypedSlotsPointwiseMatchP145IsTrue :
      allTwentySevenExistingTypedSlotsPointwiseMatchP145 ≡ true
    premise18And27NoLongerNeedOpaqueWordParametersForCanonicalP145Instance : Bool
    premise18And27NoLongerNeedOpaqueWordParametersForCanonicalP145InstanceIsTrue :
      premise18And27NoLongerNeedOpaqueWordParametersForCanonicalP145Instance ≡ true
    criterion1All27SourceExactPremisesTiedToActualP145Rule : Bool
    criterion1All27SourceExactPremisesTiedToActualP145RuleIsTrue :
      criterion1All27SourceExactPremisesTiedToActualP145Rule ≡ true
    bridgeIntroducesParallelRule915Semantics : Bool
    bridgeIntroducesParallelRule915SemanticsIsFalse :
      bridgeIntroducesParallelRule915Semantics ≡ false

canonicalWette1969Rule915CanonicalP145TypedWeldBoundary :
  Wette1969Rule915CanonicalP145TypedWeldBoundary
canonicalWette1969Rule915CanonicalP145TypedWeldBoundary =
  wette1969Rule915CanonicalP145TypedWeldBoundary
    true refl true refl true refl true refl true refl false refl
