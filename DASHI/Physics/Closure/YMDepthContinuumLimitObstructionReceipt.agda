module DASHI.Physics.Closure.YMDepthContinuumLimitObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Obstruction to using depth alone as the Yang-Mills continuum limit.

data YMDepthContinuumLimitObstructionStatus : Set where
  depthContinuumLimitAuditedAndBlocked :
    YMDepthContinuumLimitObstructionStatus

data YMDepthContinuumLimitObstruction : Set where
  fixedThreeSiteSpatialGeometry :
    YMDepthContinuumLimitObstruction

  sparseDiscreteSpatialMomenta :
    YMDepthContinuumLimitObstruction

  continuumQFTRequiresSpatialModeFamily :
    YMDepthContinuumLimitObstruction

  depthOnlyRaisesUVFrequencyCutoff :
    YMDepthContinuumLimitObstruction

  depthLimitProducesFiniteSpatialQuantumMechanics :
    YMDepthContinuumLimitObstruction

canonicalYMDepthContinuumLimitObstructions :
  List YMDepthContinuumLimitObstruction
canonicalYMDepthContinuumLimitObstructions =
  fixedThreeSiteSpatialGeometry
  ∷ sparseDiscreteSpatialMomenta
  ∷ continuumQFTRequiresSpatialModeFamily
  ∷ depthOnlyRaisesUVFrequencyCutoff
  ∷ depthLimitProducesFiniteSpatialQuantumMechanics
  ∷ []

data YMDepthContinuumLimitObstructionPromotion : Set where

ymDepthContinuumLimitObstructionPromotionImpossibleHere :
  YMDepthContinuumLimitObstructionPromotion →
  ⊥
ymDepthContinuumLimitObstructionPromotionImpossibleHere ()

ymDepthContinuumLimitObstructionStatement : String
ymDepthContinuumLimitObstructionStatement =
  "The depth limit raises the UV cutoff at fixed three-site spatial geometry; it therefore gives finite-spatial-mode quantum mechanics, not a continuum 3+1-dimensional Yang-Mills QFT."

record YMDepthContinuumLimitObstructionReceipt : Setω where
  field
    status :
      YMDepthContinuumLimitObstructionStatus

    fixedSpatialGeometryThreeSites :
      Bool

    fixedSpatialGeometryThreeSitesIsTrue :
      fixedSpatialGeometryThreeSites ≡ true

    depthSendsUVCutoffToInfinity :
      Bool

    depthSendsUVCutoffToInfinityIsTrue :
      depthSendsUVCutoffToInfinity ≡ true

    spatialMomentaDiscreteAndSparse :
      Bool

    spatialMomentaDiscreteAndSparseIsTrue :
      spatialMomentaDiscreteAndSparse ≡ true

    continuumSpatialModeFamilyConstructed :
      Bool

    continuumSpatialModeFamilyConstructedIsFalse :
      continuumSpatialModeFamilyConstructed ≡ false

    depthLimitGivesQMNotQFT :
      Bool

    depthLimitGivesQMNotQFTIsTrue :
      depthLimitGivesQMNotQFT ≡ true

    discreteSpatialMomentaPreventQFT :
      Bool

    discreteSpatialMomentaPreventQFTIsTrue :
      discreteSpatialMomentaPreventQFT ≡ true

    ymDepthContinuumLimitObstructed :
      Bool

    ymDepthContinuumLimitObstructedIsTrue :
      ymDepthContinuumLimitObstructed ≡ true

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    obstructions :
      List YMDepthContinuumLimitObstruction

    obstructionsAreCanonical :
      obstructions ≡ canonicalYMDepthContinuumLimitObstructions

    statement :
      String

    statementIsCanonical :
      statement ≡ ymDepthContinuumLimitObstructionStatement

    promotionFlags :
      List YMDepthContinuumLimitObstructionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMDepthContinuumLimitObstructionReceipt public

canonicalYMDepthContinuumLimitObstructionReceipt :
  YMDepthContinuumLimitObstructionReceipt
canonicalYMDepthContinuumLimitObstructionReceipt =
  record
    { status =
        depthContinuumLimitAuditedAndBlocked
    ; fixedSpatialGeometryThreeSites =
        true
    ; fixedSpatialGeometryThreeSitesIsTrue =
        refl
    ; depthSendsUVCutoffToInfinity =
        true
    ; depthSendsUVCutoffToInfinityIsTrue =
        refl
    ; spatialMomentaDiscreteAndSparse =
        true
    ; spatialMomentaDiscreteAndSparseIsTrue =
        refl
    ; continuumSpatialModeFamilyConstructed =
        false
    ; continuumSpatialModeFamilyConstructedIsFalse =
        refl
    ; depthLimitGivesQMNotQFT =
        true
    ; depthLimitGivesQMNotQFTIsTrue =
        refl
    ; discreteSpatialMomentaPreventQFT =
        true
    ; discreteSpatialMomentaPreventQFTIsTrue =
        refl
    ; ymDepthContinuumLimitObstructed =
        true
    ; ymDepthContinuumLimitObstructedIsTrue =
        refl
    ; continuumYangMillsConstructed =
        false
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; obstructions =
        canonicalYMDepthContinuumLimitObstructions
    ; obstructionsAreCanonical =
        refl
    ; statement =
        ymDepthContinuumLimitObstructionStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The depth limit gives arbitrarily fine UV frequency resolution"
        ∷ "It does not add spatial sites or a continuum family of spatial momenta"
        ∷ "The resulting object has finite spatial degrees of freedom and is not a 3+1-dimensional Yang-Mills QFT"
        ∷ "No Clay Yang-Mills or terminal Clay claim is promoted"
        ∷ []
    }

ymDepthContinuumLimitObstructionKeepsClayFalse :
  clayYangMillsPromoted canonicalYMDepthContinuumLimitObstructionReceipt
  ≡
  false
ymDepthContinuumLimitObstructionKeepsClayFalse =
  refl

ymDepthContinuumLimitObstructionKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYMDepthContinuumLimitObstructionReceipt
  ≡
  false
ymDepthContinuumLimitObstructionKeepsTerminalFalse =
  refl
