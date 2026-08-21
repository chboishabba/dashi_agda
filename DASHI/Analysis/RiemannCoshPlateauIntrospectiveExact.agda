module DASHI.Analysis.RiemannCoshPlateauIntrospectiveExact where

------------------------------------------------------------------------
-- INTROSPECTIVE ROUND-TRIP: PLATEAU AREA
--
-- Starting theory (already present in the Hermitian route):
--
--   Phi(-2 i alpha) - Phi(0)
--     = integral phi(u)^2 (cosh(2 alpha u)-1) du,
--
-- with source taper plateau phi(u)=1 on |u| <= L/2-w and w <= L/8.
--
-- The deterministic visual observer plotted the actual integrand and shaded
-- the plateau contribution.  Inspection revealed that the quadratic lower
-- bound is only the tangent-floor of a stronger source-native hyperbolic
-- amplifier:
--
--   integral_{-a}^{a} (cosh(2 alpha u)-1) du
--     = sinh(2 a |alpha|)/|alpha| - 2a,                 (alpha != 0)
--
-- where a = L/2-w >= 3L/8.
--
-- This module does NOT promote the rendering to proof authority.  It records
-- the recovered theorem shape and proves the subtraction-free algebraic
-- consequences once the standard real-analysis identity/inequalities are
-- instantiated.  The exact integral identity itself remains a source-facing
-- analytic bridge.
--
-- Calibration:
-- Levent Alpoege and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI 10.48550/arXiv.2608.13637.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

------------------------------------------------------------------------
-- PURE RECOVERED ORDER LEDGER
--
-- quadraticFloor <= hyperbolicPlateauFloor <= full Phi excess.
-- We encode <= constructively as addition of explicit nonnegative slack.
------------------------------------------------------------------------

record PlateauHyperbolicAmplificationLedger : Set where
  constructor plateauHyperbolicAmplificationLedger
  field
    quadraticFloor : Nat
    hyperbolicPlateauFloor : Nat
    phiExcess : Nat

    hyperbolicBeyondQuadraticSlack : Nat
    outsidePlateauSlack : Nat

    quadraticPlusHyperbolicSlackIsPlateauFloor :
      quadraticFloor + hyperbolicBeyondQuadraticSlack
        ≡ hyperbolicPlateauFloor

    plateauFloorPlusOutsideSlackIsPhiExcess :
      hyperbolicPlateauFloor + outsidePlateauSlack
        ≡ phiExcess

open PlateauHyperbolicAmplificationLedger public

------------------------------------------------------------------------
-- Exact composition: the old quadratic coercivity ledger factors through the
-- stronger hyperbolic plateau floor.
------------------------------------------------------------------------

quadraticFloorFactorsThroughHyperbolicPlateau :
  (l : PlateauHyperbolicAmplificationLedger) →
  quadraticFloor l
    + (hyperbolicBeyondQuadraticSlack l + outsidePlateauSlack l)
    ≡ phiExcess l
quadraticFloorFactorsThroughHyperbolicPlateau l
  rewrite quadraticPlusHyperbolicSlackIsPlateauFloor l
        | plateauFloorPlusOutsideSlackIsPhiExcess l = refl

------------------------------------------------------------------------
-- ERROR-FLOOR ADAPTER
--
-- If the plateau hyperbolic floor already beats an arithmetic error budget,
-- then the actual Phi excess beats that budget as well.  This is the direct G4
-- significance of the visual finding: sufficiently transverse zeros may be
-- detectable before any higher-moment amplification is needed.
------------------------------------------------------------------------

record HyperbolicPlateauBeatsError
  (l : PlateauHyperbolicAmplificationLedger) : Set where
  constructor hyperbolicPlateauBeatsError
  field
    arithmeticErrorBudget : Nat
    plateauGapPredecessor : Nat
    errorPlusStrictGapIsPlateauFloor :
      arithmeticErrorBudget + suc plateauGapPredecessor
        ≡ hyperbolicPlateauFloor l

open HyperbolicPlateauBeatsError public

record PhiExcessBeatsError
  (l : PlateauHyperbolicAmplificationLedger) : Set where
  constructor phiExcessBeatsError
  field
    arithmeticErrorBudget : Nat
    phiGapPredecessor : Nat
    errorPlusStrictGapIsPhiExcess :
      arithmeticErrorBudget + suc phiGapPredecessor
        ≡ phiExcess l

open PhiExcessBeatsError public

hyperbolicPlateauDetectabilityLiftsToPhiExcess :
  (l : PlateauHyperbolicAmplificationLedger) →
  HyperbolicPlateauBeatsError l →
  PhiExcessBeatsError l
hyperbolicPlateauDetectabilityLiftsToPhiExcess l h =
  phiExcessBeatsError
    (HyperbolicPlateauBeatsError.arithmeticErrorBudget h)
    (HyperbolicPlateauBeatsError.plateauGapPredecessor h + outsidePlateauSlack l)
    proof
  where
  proof :
    HyperbolicPlateauBeatsError.arithmeticErrorBudget h
      + suc (HyperbolicPlateauBeatsError.plateauGapPredecessor h + outsidePlateauSlack l)
      ≡ phiExcess l
  proof
    rewrite errorPlusStrictGapIsPlateauFloor h
          | plateauFloorPlusOutsideSlackIsPhiExcess l = refl

------------------------------------------------------------------------
-- SOURCE-FACING ANALYTIC BRIDGE
--
-- These are the exact real-analysis statements still to instantiate against
-- the source taper / Bishop-real or translated Lean analytic backend.
------------------------------------------------------------------------

record PlateauHyperbolicAnalyticProducer : Set₁ where
  field
    Parameter : Set

    AlphaMagnitude : Parameter → Set
    PlateauRadius : Parameter → Set
    PhiExcessValue : Parameter → Set
    PlateauFloorValue : Parameter → Set

    sourcePhiEqualsOneOnPlateau :
      (p : Parameter) → Set

    sourcePlateauRadiusAtLeastThreeEighthsL :
      (p : Parameter) → Set

    imaginaryAxisPhiIsCoshIntegral :
      (p : Parameter) → Set

    symmetricPlateauIntegralExact :
      (p : Parameter) → Set
      -- target formula for alpha != 0:
      -- sinh(2 a |alpha|)/|alpha| - 2a

    plateauHyperbolicFloorInsidePhiExcess :
      (p : Parameter) → Set

    hyperbolicFloorRefinesQuadraticFloor :
      (p : Parameter) → Set

    amplificationLedger :
      (p : Parameter) → PlateauHyperbolicAmplificationLedger

------------------------------------------------------------------------
-- INTROSPECTIVE FINDING / AUTHORITY BOUNDARY
------------------------------------------------------------------------

record CoshPlateauIntrospectiveBoundary : Set where
  field
    visualizationUsedAsObserverOnly : Bool
    actualKernelCurveRendered : Bool
    actualPlateauRegionRendered : Bool
    quadraticFloorVisibleAsTangentSubarea : Bool
    exactHyperbolicPlateauAmplifierIdentified : Bool
    quadraticCoercivityRecognizedAsSmallDisplacementShadow : Bool
    directG4DetectabilityAdapterProved : Bool

    exactSinhIntegralInstantiatedInAgdaHere : Bool
    sourceSpecificNumericalErrorFloorBeatenHere : Bool
    riemannHypothesisClaimedHere : Bool

coshPlateauIntrospectiveBoundary : CoshPlateauIntrospectiveBoundary
coshPlateauIntrospectiveBoundary = record
  { visualizationUsedAsObserverOnly = true
  ; actualKernelCurveRendered = true
  ; actualPlateauRegionRendered = true
  ; quadraticFloorVisibleAsTangentSubarea = true
  ; exactHyperbolicPlateauAmplifierIdentified = true
  ; quadraticCoercivityRecognizedAsSmallDisplacementShadow = true
  ; directG4DetectabilityAdapterProved = true

  ; exactSinhIntegralInstantiatedInAgdaHere = false
  ; sourceSpecificNumericalErrorFloorBeatenHere = false
  ; riemannHypothesisClaimedHere = false
  }
