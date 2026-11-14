module DASHI.Physics.Plasma.Phase243Core54ParetoCoilExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54
import DASHI.Physics.Plasma.Phase243PeriodicConsumerQuotientExact as Periodic
import DASHI.Physics.Plasma.ToroidalConstantMagnitudeHybridABCExact as ABC
import DASHI.Physics.Plasma.ToroidalZeroBounceCoilInverseMaxCutExact as Coil

------------------------------------------------------------------------
-- CORE54 -> CONTINUOUS ABC FIBRE -> PARETO -> COIL-INVERSE MAX-CUT
--
-- The finite phase/incidence search is already quotiented to 54 states for
-- consumers carrying the required periodic torus-equivariance receipt.
-- This owner keeps the next stage deliberately multi-objective:
--
--   relative |B| spread
--   geodesic-curvature residual
--   flow/M^2 burden
--   anisotropy burden
--   route-C geometry burden
--   coefficient/description complexity
--
-- No one scalar objective is allowed to pay another missing consumer.  Only
-- non-dominated proxy fibres are routed into the more expensive winding-
-- surface current-potential inverse.
--
-- The executable receipt is local numerical/search evidence only.  It is not
-- an experimental source, a best-known stellarator benchmark, a free-boundary
-- equilibrium, or a full-orbit confinement result.
------------------------------------------------------------------------

representativeCount : Nat
representativeCount = 54

deltaContinuationLevelCount : Nat
deltaContinuationLevelCount = 5

flowAnisotropyAllocationCount : Nat
flowAnisotropyAllocationCount = 3

abcGridRecordCount : Nat
abcGridRecordCount = 810

abcGridAccounting :
  representativeCount * deltaContinuationLevelCount * flowAnisotropyAllocationCount
  ≡ abcGridRecordCount
abcGridAccounting = refl

record Core54ContinuousFibre : Set₁ where
  constructor core54-continuous-fibre
  field
    quotientState : Q54.Core54

    nonAxisymmetricAmplitudeReceipt : Set
    geometryCoefficientReceipt : Set
    streamCurrentCoefficientReceipt : Set

    alfvenMachReceipt : Set
    anisotropyFractionReceipt : Set
    routeCGeometryFractionReceipt : Set
    abcFractionSumToOneReceipt : Set

    relativeBSpreadObservation : Set
    geodesicCurvatureObservation : Set
    divergenceObservation : Set
    flowBurdenObservation : Set
    anisotropyBurdenObservation : Set
    geometryBurdenObservation : Set
    complexityObservation : Set

    samePeriodicConsumerReceipt : Set
    fibreReference : String

open Core54ContinuousFibre public

record ParetoFibreReceipt : Set₁ where
  constructor pareto-fibre-receipt
  field
    candidate : Core54ContinuousFibre
    physicallyHardGatesPaidBeforePareto : Set
    nonDominatedOnDeclaredAxesReceipt : Set
    paretoDoesNotPayMissingPhysicsReceipt : Set
    receiptReference : String

open ParetoFibreReceipt public

record CoilRoutedFibreReceipt : Set₁ where
  constructor coil-routed-fibre-receipt
  field
    paretoFibre : ParetoFibreReceipt
    windingSurfaceReceipt : Set
    currentPotentialInverseReceipt : Set
    normalFieldResidualReceipt : Set
    currentRegularizationReceipt : Set
    producedCoilFieldReplayedReceipt : Set
    freeBoundaryNotYetPaidReceipt : Set
    routingReference : String

open CoilRoutedFibreReceipt public

record Core54ParetoCoilNumericalReceipt : Set where
  constructor core54-pareto-coil-numerical-receipt
  field
    rawRepresentativeCount : Nat
    rawRepresentativeCountIs54 : rawRepresentativeCount ≡ representativeCount

    evaluatedABCGridRecords : Nat
    evaluatedABCGridRecordsIs810 : evaluatedABCGridRecords ≡ abcGridRecordCount

    retainedParetoRecords : Nat
    coilShortlistRecords : Nat

    paretoFrontierNonEmpty : Bool
    paretoFrontierNonEmptyIsTrue : paretoFrontierNonEmpty ≡ true

    hardNonAxisymmetricFloorEnforced : Bool
    hardNonAxisymmetricFloorEnforcedIsTrue : hardNonAxisymmetricFloorEnforced ≡ true

    exactABCAccountingCheckedNumerically : Bool
    exactABCAccountingCheckedNumericallyIsTrue : exactABCAccountingCheckedNumerically ≡ true

    sixShortlistNormalResidualsBelowUncorrectedBaseline : Bool
    sixShortlistNormalResidualsBelowUncorrectedBaselineIsTrue :
      sixShortlistNormalResidualsBelowUncorrectedBaseline ≡ true

    numericalReceiptReference : String

canonicalCore54ParetoCoilReceipt : Core54ParetoCoilNumericalReceipt
canonicalCore54ParetoCoilReceipt =
  core54-pareto-coil-numerical-receipt
    54 refl
    810 refl
    168
    6
    true refl
    true refl
    true refl
    true refl
    "scripts/phase243_core54_pareto_coil.py: deterministic coarse Core54 x ABC scan; 810 records, 168 declared-axis Pareto records, six compromise-routed current-potential inversions. Search evidence only."

record Core54ParetoCoilBoundary : Set where
  constructor core54-pareto-coil-boundary
  field
    algebraicAndPeriodicConsumerQuotientPaid : Bool
    algebraicAndPeriodicConsumerQuotientPaidIsTrue :
      algebraicAndPeriodicConsumerQuotientPaid ≡ true

    paretoRankingCanRepairMissingZeroBounce : Bool
    paretoRankingCanRepairMissingZeroBounceIsFalse :
      paretoRankingCanRepairMissingZeroBounce ≡ false

    coilInverseResidualProvesFreeBoundaryEquilibrium : Bool
    coilInverseResidualProvesFreeBoundaryEquilibriumIsFalse :
      coilInverseResidualProvesFreeBoundaryEquilibrium ≡ false

    sameObjectCoilPlasmaFreeBoundaryPaid : Bool
    sameObjectCoilPlasmaFreeBoundaryPaidIsFalse :
      sameObjectCoilPlasmaFreeBoundaryPaid ≡ false

    fullOrbitFOWEnergeticParticlePaid : Bool
    fullOrbitFOWEnergeticParticlePaidIsFalse :
      fullOrbitFOWEnergeticParticlePaid ≡ false

    bestKnownReferenceComparisonPaid : Bool
    bestKnownReferenceComparisonPaidIsFalse :
      bestKnownReferenceComparisonPaid ≡ false

    localNumericalReceiptIsExperimentalAuthority : Bool
    localNumericalReceiptIsExperimentalAuthorityIsFalse :
      localNumericalReceiptIsExperimentalAuthority ≡ false

canonicalCore54ParetoCoilBoundary : Core54ParetoCoilBoundary
canonicalCore54ParetoCoilBoundary =
  core54-pareto-coil-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

nextSameObjectFrontier : String
nextSameObjectFrontier =
  "For each coil-routed Pareto survivor solve one same-object finite-beta free-boundary equilibrium with B_total = B_coil + B_plasma and the declared ABC flow/anisotropy allocation; only on that produced field evaluate zero-bounce, trapped fraction, J_parallel, FOW, energetic-particle loss and same-normalization best-known-reference comparison."

attributionBoundary : String
attributionBoundary =
  "This tranche adds no external experimental/source authority. Numerical counts and residuals are script-produced artifact receipts. Any later acquired paper, device, company, experimental or benchmark claim must retain its own citation/source role and cannot inherit artifact authority from this search."
