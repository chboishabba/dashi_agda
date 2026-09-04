module DASHI.Analysis.NonArchimedeanSpectralSourceTheoremMatrixExact where

------------------------------------------------------------------------
-- Source theorem / advertised claim matrix.
--
-- The point is not to judge names, but to force every promoted claim to carry
-- exactly the source strength actually present in the external Lean repo.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record SourceTheoremMatrix : Set where
  constructor sourceTheoremMatrix
  field
    characterMonomialActionOwned : Bool
    orderThreeOwned : Bool
    cyclotomicOddProductOwned : Bool
    orbitPartitionNeedsSeparateReceipt : Bool
    intermediateOddTraceVanishesOwned : Bool

    concreteDFTReindexOwned : Bool
    concreteDFTBasisOwned : Bool
    concreteDFTUnitarityOwned : Bool
    concreteFourierConjugatedTwistedMatrixOwned : Bool
    concreteFourierConjugatedEqualsMonomialOwned : Bool

    twistedBlockHypothesisStoresFinalMagnitude : Bool
    twistedBlockHypothesisStoresFourierMonomialWeld : Bool
    finalSpectralCircleUsesFinalMagnitudeHypothesis : Bool
    finalSpectralCircleDerivesMagnitudeFromOrbitKernel : Bool

    hadamardBlockDiagonalizationOwned : Bool
    determinantCoverFactorizationOwned : Bool
    namedSpectralTowerConclusionIsSpectrumUnion : Bool
    namedSpectralTowerConclusionIsTrueOnly : Bool

    dyadicDirectLimitInjectiveOwned : Bool
    ropeRelativeInvarianceOwned : Bool
    ropeModelOptimalityOwned : Bool
    dagCoverConsumesEdgeCoveredReceipt : Bool
    depthDecaySparsityOwned : Bool
    existentialEntropyScalarOwned : Bool
    contractedBoundaryEntropySameObjectOwned : Bool

canonicalSourceTheoremMatrix : SourceTheoremMatrix
canonicalSourceTheoremMatrix =
  sourceTheoremMatrix
    true true true true true
    true true true true false
    true false true false
    true true false true
    true true false true false true false

record PromotionMatrix : Set where
  constructor promotionMatrix
  field
    finiteCharacterOrbitKernel : Bool
    signedTraceKernel : Bool
    concreteDFTInfrastructure : Bool
    concreteDFTMonomialSameObject : Bool
    spatialSpectralConsumer : Bool
    determinantTowerFactorization : Bool
    literalSpectrumTower : Bool
    directLimitArchitecture : Bool
    ropeGeometry : Bool
    transformerCompressionOptimality : Bool
    arbitraryDagAdelicUniversality : Bool
    advertisedDepthSparsity : Bool
    boundaryStateAreaLaw : Bool

canonicalPromotionMatrix : PromotionMatrix
canonicalPromotionMatrix =
  promotionMatrix
    true true true false false true false
    true true false false false false

spatialRemainsBlocked :
  PromotionMatrix.spatialSpectralConsumer canonicalPromotionMatrix ≡ false
spatialRemainsBlocked = refl

finiteKernelPromotes :
  PromotionMatrix.finiteCharacterOrbitKernel canonicalPromotionMatrix ≡ true
finiteKernelPromotes = refl

signedTracePromotes :
  PromotionMatrix.signedTraceKernel canonicalPromotionMatrix ≡ true
signedTracePromotes = refl

sourceDFTInfrastructurePromotes :
  PromotionMatrix.concreteDFTInfrastructure canonicalPromotionMatrix ≡ true
sourceDFTInfrastructurePromotes = refl

literalSpectrumTowerStillBlocked :
  PromotionMatrix.literalSpectrumTower canonicalPromotionMatrix ≡ false
literalSpectrumTowerStillBlocked = refl
