module DASHI.Reasoning.SemanticLogicalSelectiveReopeningExact where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Dependency

------------------------------------------------------------------------
-- SEMANTIC / LOGICAL SELECTIVE REOPENING
--
-- A changed semantic resolution invalidates exactly the certificates that
-- depend on that interpretation.  The dependency closure is the canonical
-- repo-wide reopening calculus: transitive downstream consequences reopen,
-- while a downstream semantic revision is not treated as a new parser/source
-- observation.
------------------------------------------------------------------------

data ReasoningCertificate : Set where
  parserObservationCertificate
  semanticResolutionCertificate
  evidentialPNFCertificate
  logicalInterpretationCertificate
  logicalDerivationCertificate
  implicationConeCertificate
  designDischargeCertificate
  : ReasoningCertificate

data Depends : ReasoningCertificate → ReasoningCertificate → Set where
  parserFeedsSemantic :
    Depends parserObservationCertificate semanticResolutionCertificate
  semanticFeedsPNF :
    Depends semanticResolutionCertificate evidentialPNFCertificate
  pnfFeedsLogicalInterpretation :
    Depends evidentialPNFCertificate logicalInterpretationCertificate
  interpretationFeedsDerivation :
    Depends logicalInterpretationCertificate logicalDerivationCertificate
  derivationFeedsCone :
    Depends logicalDerivationCertificate implicationConeCertificate
  designFeedsCone :
    Depends designDischargeCertificate implicationConeCertificate

semanticToPNFReopening :
  Dependency.ReopeningObligation
    Depends semanticResolutionCertificate evidentialPNFCertificate
semanticToPNFReopening =
  Dependency.oneEdgeCreatesReopeningObligation semanticFeedsPNF

pnfToInterpretationReopening :
  Dependency.ReopeningObligation
    Depends evidentialPNFCertificate logicalInterpretationCertificate
pnfToInterpretationReopening =
  Dependency.oneEdgeCreatesReopeningObligation pnfFeedsLogicalInterpretation

interpretationToDerivationReopening :
  Dependency.ReopeningObligation
    Depends logicalInterpretationCertificate logicalDerivationCertificate
interpretationToDerivationReopening =
  Dependency.oneEdgeCreatesReopeningObligation interpretationFeedsDerivation

derivationToConeReopening :
  Dependency.ReopeningObligation
    Depends logicalDerivationCertificate implicationConeCertificate
derivationToConeReopening =
  Dependency.oneEdgeCreatesReopeningObligation derivationFeedsCone

semanticChangeReopensLogicalInterpretation :
  Dependency.ReopeningObligation
    Depends semanticResolutionCertificate logicalInterpretationCertificate
semanticChangeReopensLogicalInterpretation =
  Dependency.obligationsCompose
    semanticToPNFReopening
    pnfToInterpretationReopening

semanticChangeReopensLogicalDerivation :
  Dependency.ReopeningObligation
    Depends semanticResolutionCertificate logicalDerivationCertificate
semanticChangeReopensLogicalDerivation =
  Dependency.obligationsCompose
    semanticChangeReopensLogicalInterpretation
    interpretationToDerivationReopening

semanticChangeReopensImplicationCone :
  Dependency.ReopeningObligation
    Depends semanticResolutionCertificate implicationConeCertificate
semanticChangeReopensImplicationCone =
  Dependency.obligationsCompose
    semanticChangeReopensLogicalDerivation
    derivationToConeReopening

designChangeReopensImplicationCone :
  Dependency.ReopeningObligation
    Depends designDischargeCertificate implicationConeCertificate
designChangeReopensImplicationCone =
  Dependency.oneEdgeCreatesReopeningObligation designFeedsCone

------------------------------------------------------------------------
-- Directionality boundary.
------------------------------------------------------------------------

semanticRevisionIsNotNewParserObservation :
  Depends semanticResolutionCertificate parserObservationCertificate → ⊥
semanticRevisionIsNotNewParserObservation ()

coneRevisionIsNotNewLogicalDerivation :
  Depends implicationConeCertificate logicalDerivationCertificate → ⊥
coneRevisionIsNotNewLogicalDerivation ()

record SemanticLogicalSelectiveReopeningBoundary : Set where
  constructor semanticLogicalSelectiveReopeningBoundary
  field
    semanticChangeReopensPNF : Bool
    semanticChangeReopensPNFIsTrue : semanticChangeReopensPNF ≡ true
    semanticChangeReopensDerivationTransitively : Bool
    semanticChangeReopensDerivationTransitivelyIsTrue :
      semanticChangeReopensDerivationTransitively ≡ true
    semanticChangeReopensConeTransitively : Bool
    semanticChangeReopensConeTransitivelyIsTrue :
      semanticChangeReopensConeTransitively ≡ true
    semanticRevisionManufacturesParserObservation : Bool
    semanticRevisionManufacturesParserObservationIsFalse :
      semanticRevisionManufacturesParserObservation ≡ false
    designChangeMayReopenConeIndependently : Bool
    designChangeMayReopenConeIndependentlyIsTrue :
      designChangeMayReopenConeIndependently ≡ true

canonicalSemanticLogicalSelectiveReopeningBoundary :
  SemanticLogicalSelectiveReopeningBoundary
canonicalSemanticLogicalSelectiveReopeningBoundary =
  semanticLogicalSelectiveReopeningBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
