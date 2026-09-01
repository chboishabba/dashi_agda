module DASHI.Base369StabiliserReceptionGraphValidation where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27StabiliserOperatorHolonomyExact as H
import DASHI.Foundations.Base369Ternary27StratumStabiliserFibreAdmissibilityExact as S
import DASHI.Governance.ReceptionRelationEvidenceTemporalGraphExact as R
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Base369 operator-bearing stabiliser checks.
------------------------------------------------------------------------

nativeTransitionExists : Geometry.HypervoxelAdjacent S.oppositeSignEdge H.positiveXFace
nativeTransitionExists = H.oppositeEdgeToFaceAdjacent

swapUnavailableBefore : H.OperatorAdmitted S.oppositeSignEdge H.swapXYOperator -> ⊥
swapUnavailableBefore = H.oppositeSignEdgeSwapNotAdmitted

swapAvailableAfter : H.OperatorAdmitted H.positiveXFace H.swapXYOperator
swapAvailableAfter = H.positiveXFaceSwapAdmitted

s3HolonomyPairAvailable : H.AdmissibleHolonomyPair Geometry.positiveCorner
s3HolonomyPairAvailable = H.positiveCornerSwapRotateHolonomy

operatorOrderReallyDiffers : H.swapThenRotate ≡ H.rotateThenSwap -> ⊥
operatorOrderReallyDiffers = H.operatorOrderDefect

------------------------------------------------------------------------
-- Reception graph checks.
------------------------------------------------------------------------

directCitationDistinctFromBorrowing : R.directCitation ≡ R.lexicalBorrowing -> ⊥
directCitationDistinctFromBorrowing = R.directCitationNotLexicalBorrowing

reinterpretationDistinctFromRediscovery :
  R.explicitReinterpretation ≡ R.independentRediscovery -> ⊥
reinterpretationDistinctFromRediscovery = R.reinterpretationNotIndependentRediscovery

sameVocabularyDoesNotRecoverPath :
  INF.FactorsThrough R.presentVocabulary R.pathRelation -> ⊥
sameVocabularyDoesNotRecoverPath = R.presentVocabularyCannotRecoverReceptionPath

citationReinterpretationComposable : R.ComposableReceptionPair
citationReinterpretationComposable = R.citationThenReinterpretation

------------------------------------------------------------------------
-- Cross-domain structural analogy boundary.
------------------------------------------------------------------------

record StabiliserReceptionAnalogyBoundary : Set where
  constructor stabiliser-reception-analogy-boundary
  field
    coarseSurfaceMayLoseFinePathInformation : Bool
    sameCoarseSurfaceDeterminesFineStructure : Bool
    intellectualReceptionIsLiterallyBase369Geometry : Bool
    operatorAdmissionEqualsHistoricalAuthority : Bool

canonicalStabiliserReceptionAnalogyBoundary : StabiliserReceptionAnalogyBoundary
canonicalStabiliserReceptionAnalogyBoundary =
  stabiliser-reception-analogy-boundary true false false false
