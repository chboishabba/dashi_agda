module DASHI.Analysis.NonArchimedeanSpectralHypothesisSemanticCorrectionExact where

------------------------------------------------------------------------
-- SOURCE-EXACT CORRECTION OF `TwistedBlockHypothesis`
--
-- The paper prose describes `TwistedBlockHypothesis` as if it were the
-- spatial/character Fourier-monomial bridge.  The actual Lean declaration in
-- `Formalization/Spectral/SchreierSpectralGap.lean` is stronger and later:
-- it directly assumes the eigenvalue-magnitude conclusion for the concrete
-- mapped `twistedDirMatrix`.
--
-- Separately, `Formalization/Analysis/DFT.lean` already constructs the concrete
-- reindexing, the DFT tensor identity basis, its unitary inverse relation, and
-- the Fourier-conjugated twisted matrix.  What is not supplied there is the
-- concrete equality of that conjugated matrix with the claimed monomial/block
-- operator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record TwistedHypothesisSourceSemantics : Set where
  constructor twistedHypothesisSourceSemantics
  field
    concreteTwistedMatrixAppearsInHypothesis : Bool
    hypothesisAssumesEigenvalueMagnitudeDirectly : Bool
    hypothesisStoresFourierRechart : Bool
    hypothesisStoresMonomialMatrixEquality : Bool
    paperDescribesHypothesisAsFourierMonomialBridge : Bool
    paperDescriptionMatchesLeanDeclarationLiterally : Bool

canonicalTwistedHypothesisSourceSemantics :
  TwistedHypothesisSourceSemantics
canonicalTwistedHypothesisSourceSemantics =
  twistedHypothesisSourceSemantics
    true
    true
    false
    false
    true
    false

record ConcreteDFTSourceStatus : Set where
  constructor concreteDFTSourceStatus
  field
    concreteIndexEquivalenceOwned : Bool
    concreteComplexTwistedMatrixOwned : Bool
    concreteReindexedTwistedMatrixOwned : Bool
    dftTensorIdentityBasisOwned : Bool
    dftTensorIdentityInverseOwned : Bool
    unitaryProductIdentityOwned : Bool
    concreteFourierConjugatedMatrixOwned : Bool
    conjugatedMatrixEqualsClaimedMonomialOperatorOwned : Bool

canonicalConcreteDFTSourceStatus : ConcreteDFTSourceStatus
canonicalConcreteDFTSourceStatus =
  concreteDFTSourceStatus
    true true true true true true true false

record HypothesisPromotionFirewall : Set where
  constructor hypothesisPromotionFirewall
  field
    assumingFinalMagnitudeCountsAsDerivingMagnitude : Bool
    proseBridgeDescriptionCreatesMissingMatrixIdentity : Bool
    unitaryBasisDefinitionCreatesMonomialization : Bool
    concreteDFTInfrastructureMayBeReopenedAsMissing : Bool

canonicalHypothesisPromotionFirewall : HypothesisPromotionFirewall
canonicalHypothesisPromotionFirewall =
  hypothesisPromotionFirewall false false false false

sourceDFTInfrastructureAlreadyOwned :
  ConcreteDFTSourceStatus.concreteFourierConjugatedMatrixOwned
    canonicalConcreteDFTSourceStatus
  ≡ true
sourceDFTInfrastructureAlreadyOwned = refl

monomialIdentityStillLive :
  ConcreteDFTSourceStatus.conjugatedMatrixEqualsClaimedMonomialOperatorOwned
    canonicalConcreteDFTSourceStatus
  ≡ false
monomialIdentityStillLive = refl

hypothesisIsNotTheBridgeDeclaration :
  TwistedHypothesisSourceSemantics.hypothesisStoresMonomialMatrixEquality
    canonicalTwistedHypothesisSourceSemantics
  ≡ false
hypothesisIsNotTheBridgeDeclaration = refl
