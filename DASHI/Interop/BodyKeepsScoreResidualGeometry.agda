module DASHI.Interop.BodyKeepsScoreResidualGeometry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Interop.BodyKeepsScoreCandidateBoundary as BodyScore
import DASHI.Interop.BodyKeepsScoreParityCompiledInverseAdapter as ParityAdapter

------------------------------------------------------------------------
-- Candidate-only PNF-style residual geometry for the body-score lane.
--
-- The graph below records typed residual relations among public surfaces,
-- hidden body-state fibres, old inverse charts, safety/agency seeds, and
-- j+1 re-charting obligations.  It is diagnostic geometry only: adjacency,
-- sign, weight labels, or proximity never become diagnosis or truth.


data BodyScoreResidualNode : Set where
  publicSurfaceNode : BodyScoreResidualNode
  hiddenBodyFibreNode : BodyScoreResidualNode
  oldInverseChartNode : BodyScoreResidualNode
  currentWorldChartNode : BodyScoreResidualNode
  safetyAgencySeedNode : BodyScoreResidualNode
  localIntegrationNode : BodyScoreResidualNode
  jPlusOneChartNode : BodyScoreResidualNode


data BodyScoreResidualEdgeKind : Set where
  projectionEdge : BodyScoreResidualEdgeKind
  triggerEdge : BodyScoreResidualEdgeKind
  mismatchEdge : BodyScoreResidualEdgeKind
  avoidanceEdge : BodyScoreResidualEdgeKind
  groundingEdge : BodyScoreResidualEdgeKind
  agencyEdge : BodyScoreResidualEdgeKind
  integrationEdge : BodyScoreResidualEdgeKind
  rechartingEdge : BodyScoreResidualEdgeKind


data ResidualSign : Set where
  coherenceSign : ResidualSign
  ruptureSign : ResidualSign

record BodyScoreResidualEdge : Set where
  constructor mkBodyScoreResidualEdge
  field
    source : BodyScoreResidualNode
    target : BodyScoreResidualNode
    edgeKind : BodyScoreResidualEdgeKind
    sign : ResidualSign
    weightLabel : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open BodyScoreResidualEdge public

canonicalBodyScoreResidualEdges : List BodyScoreResidualEdge
canonicalBodyScoreResidualEdges =
  mkBodyScoreResidualEdge
    publicSurfaceNode hiddenBodyFibreNode projectionEdge ruptureSign
    "public surface underdetermines hidden body-state fibres"
    true refl
  ∷ mkBodyScoreResidualEdge
    oldInverseChartNode currentWorldChartNode mismatchEdge ruptureSign
    "world_now * world_old^-1 does not reduce to identity"
    true refl
  ∷ mkBodyScoreResidualEdge
    safetyAgencySeedNode hiddenBodyFibreNode groundingEdge coherenceSign
    "safe +1 identity handle over selected fibres"
    true refl
  ∷ mkBodyScoreResidualEdge
    hiddenBodyFibreNode localIntegrationNode integrationEdge coherenceSign
    "local receipt without total factorisation"
    true refl
  ∷ mkBodyScoreResidualEdge
    localIntegrationNode jPlusOneChartNode rechartingEdge coherenceSign
    "j+1 candidate carry into a new chart"
    true refl
  ∷ []

record BodyScoreResidualGeometry : Set₁ where
  constructor mkBodyScoreResidualGeometry
  field
    bodyScoreBoundary :
      BodyScore.BodyKeepsScoreCandidateBoundary

    parityCompiledInverseAdapter :
      ParityAdapter.BodyScoreParityCompiledInverseAdapter

    residualEdges :
      List BodyScoreResidualEdge

    residualEdgesAreCanonical :
      residualEdges ≡ canonicalBodyScoreResidualEdges

    spectralProximityImpliesTruth :
      Bool

    spectralProximityImpliesTruthIsFalse :
      spectralProximityImpliesTruth ≡ false

    publicSurfaceRecoversAllFibres :
      Bool

    publicSurfaceRecoversAllFibresIsFalse :
      publicSurfaceRecoversAllFibres ≡ false

    residualGeometryIsDiagnosis :
      Bool

    residualGeometryIsDiagnosisIsFalse :
      residualGeometryIsDiagnosis ≡ false

    authorityBundle :
      Authority.AuthorityNonPromotionBundle

    clinicalAuthorityIsFalse :
      Authority.authorityFlag Authority.clinicalAuthority authorityBundle ≡ false

    empiricalAuthorityIsFalse :
      Authority.authorityFlag Authority.empiricalAuthority authorityBundle ≡ false

open BodyScoreResidualGeometry public

bodyScoreResidualGeometryAuthority : Authority.AuthorityNonPromotionBundle
bodyScoreResidualGeometryAuthority =
  Authority.mkClosedAuthorityNonPromotionBundle
    "body-score residual geometry: no clinical or empirical promotion"

canonicalBodyScoreResidualGeometry : BodyScoreResidualGeometry
canonicalBodyScoreResidualGeometry =
  mkBodyScoreResidualGeometry
    BodyScore.canonicalBodyKeepsScoreCandidateBoundary
    ParityAdapter.canonicalBodyScoreParityCompiledInverseAdapter
    canonicalBodyScoreResidualEdges
    refl
    false
    refl
    false
    refl
    false
    refl
    bodyScoreResidualGeometryAuthority
    (Authority.authorityFlagIsFalse Authority.clinicalAuthority bodyScoreResidualGeometryAuthority)
    (Authority.authorityFlagIsFalse Authority.empiricalAuthority bodyScoreResidualGeometryAuthority)

canonicalResidualGeometryDoesNotDiagnose :
  residualGeometryIsDiagnosis canonicalBodyScoreResidualGeometry ≡ false
canonicalResidualGeometryDoesNotDiagnose =
  residualGeometryIsDiagnosisIsFalse canonicalBodyScoreResidualGeometry
