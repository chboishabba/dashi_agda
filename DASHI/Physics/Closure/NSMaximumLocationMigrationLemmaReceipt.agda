module DASHI.Physics.Closure.NSMaximumLocationMigrationLemmaReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint136HouLuoSymmetricSourceSignReceipt as S136
import DASHI.Physics.Closure.NSSprint145ComparisonEnvelopeObstructionReceipt as S145

------------------------------------------------------------------------
-- MaximumLocationMigrationLemma gate.
--
-- This receipt records the next NS closure gate after the Sprint 136
-- symmetric source-sign receipt and the Sprint 145 comparison-envelope
-- obstruction receipt.
--
-- The exact fork is:
--
--   * if the omega1 maximum is pinned at the symmetry plane z=0, then
--     z-reflection gives partial_z u1=0 and the source
--     S = 2 u1 partial_z u1 vanishes at the maximum;
--   * if the maximum can migrate to a symmetric off-center pair
--     z_omega>0, and there u1>0 and partial_z u1>0, then the same source is
--     positive and creates a feedback obstruction;
--   * Sprint 145 does not provide the missing comparison envelope needed to
--     exclude or dominate this off-center branch.
--
-- The module is intentionally fail-closed: it records the lemma target and
-- its prerequisites, alternatives, blockers, counts, and false-promotion
-- guards, but it does not prove MaximumLocationMigrationLemma and does not
-- promote Clay Navier-Stokes regularity.

maximumLocationMigrationGateRecorded : Bool
maximumLocationMigrationGateRecorded = true

omega1MaximumPinnedAtZ0 : Bool
omega1MaximumPinnedAtZ0 = false

omega1MaximumMayMigrateOffCenter : Bool
omega1MaximumMayMigrateOffCenter = true

symmetricOffCenterMaximaScenarioRecorded : Bool
symmetricOffCenterMaximaScenarioRecorded = true

zOmegaPositiveBranchRecorded : Bool
zOmegaPositiveBranchRecorded = true

partialZU1PositiveAtOffCenterMaxRecorded : Bool
partialZU1PositiveAtOffCenterMaxRecorded = true

u1PositiveAtOffCenterMaxRequired : Bool
u1PositiveAtOffCenterMaxRequired = true

sourceFormulaRecorded : Bool
sourceFormulaRecorded = true

centerPinnedSourceVanishes : Bool
centerPinnedSourceVanishes = true

offCenterPositiveFeedbackScenarioRecorded : Bool
offCenterPositiveFeedbackScenarioRecorded = true

offCenterPositiveFeedbackExcluded : Bool
offCenterPositiveFeedbackExcluded = false

regularityRouteMayPartiallyRecoverIfPinned : Bool
regularityRouteMayPartiallyRecoverIfPinned = true

regularityRouteRecoveredUnconditionally : Bool
regularityRouteRecoveredUnconditionally = false

MaximumLocationMigrationLemma : Bool
MaximumLocationMigrationLemma = false

MaximumLocationMigrationLemmaProved : Bool
MaximumLocationMigrationLemmaProved = false

MaximumLocationMigrationLemmaOpen : Bool
MaximumLocationMigrationLemmaOpen = true

MaximumLocationMigrationLemmaIsNextGate : Bool
MaximumLocationMigrationLemmaIsNextGate = true

sprint136ReceiptAnchored : Bool
sprint136ReceiptAnchored = true

sprint145ReceiptAnchored : Bool
sprint145ReceiptAnchored = true

comparisonEnvelopeStillAbsent : Bool
comparisonEnvelopeStillAbsent =
  S145.ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsAbsent

sprint145EnvelopeStillObstructed : Bool
sprint145EnvelopeStillObstructed =
  S145.ComparisonEnvelopeForNonlocalPsi1AndRadialCommutatorsStillObstructed

globalAxialMonotonicityStillFalse : Bool
globalAxialMonotonicityStillFalse = S145.globalAxialMonotonicity

full_clay_ns_solved : Bool
full_clay_ns_solved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

maximumLocationMigrationKeepsLemmaFalse :
  MaximumLocationMigrationLemma ≡ false
maximumLocationMigrationKeepsLemmaFalse = refl

maximumLocationMigrationKeepsLemmaOpen :
  MaximumLocationMigrationLemmaOpen ≡ true
maximumLocationMigrationKeepsLemmaOpen = refl

offCenterBranchNotExcludedHere :
  offCenterPositiveFeedbackExcluded ≡ false
offCenterBranchNotExcludedHere = refl

pinnedBranchHasZeroSourceHere :
  centerPinnedSourceVanishes ≡ true
pinnedBranchHasZeroSourceHere = refl

partialRegularityRecoveryOnlyConditional :
  regularityRouteRecoveredUnconditionally ≡ false
partialRegularityRecoveryOnlyConditional = refl

maximumLocationMigrationKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
maximumLocationMigrationKeepsClayFalse = refl

sprint145EnvelopeAbsentAnchored :
  comparisonEnvelopeStillAbsent ≡ true
sprint145EnvelopeAbsentAnchored = refl

sprint145EnvelopeObstructionAnchored :
  sprint145EnvelopeStillObstructed ≡ true
sprint145EnvelopeObstructionAnchored = refl

sprint145GlobalAxialMonotonicityStillFalse :
  globalAxialMonotonicityStillFalse ≡ false
sprint145GlobalAxialMonotonicityStillFalse = refl

data MaximumLocationPrerequisite : Set where
  sprint136SymmetricSourceSignReceipt :
    MaximumLocationPrerequisite

  sprint145ComparisonEnvelopeObstructionReceipt :
    MaximumLocationPrerequisite

  zReflectionSymmetryForU1 :
    MaximumLocationPrerequisite

  interiorOmega1MaximumPrinciple :
    MaximumLocationPrerequisite

  signAccountingForU1AndPartialZU1 :
    MaximumLocationPrerequisite

  nonlocalPsi1EnvelopeOrReplacement :
    MaximumLocationPrerequisite

canonicalMaximumLocationPrerequisites :
  List MaximumLocationPrerequisite
canonicalMaximumLocationPrerequisites =
  sprint136SymmetricSourceSignReceipt
  ∷ sprint145ComparisonEnvelopeObstructionReceipt
  ∷ zReflectionSymmetryForU1
  ∷ interiorOmega1MaximumPrinciple
  ∷ signAccountingForU1AndPartialZU1
  ∷ nonlocalPsi1EnvelopeOrReplacement
  ∷ []

maximumLocationPrerequisiteCount : Nat
maximumLocationPrerequisiteCount = 6

data MaximumLocationAlternative : Set where
  pinnedCenterMaximum :
    MaximumLocationAlternative

  symmetricOffCenterPositiveFeedbackMaximum :
    MaximumLocationAlternative

  unresolvedMixedOrSecondaryPeakGeometry :
    MaximumLocationAlternative

canonicalMaximumLocationAlternatives :
  List MaximumLocationAlternative
canonicalMaximumLocationAlternatives =
  pinnedCenterMaximum
  ∷ symmetricOffCenterPositiveFeedbackMaximum
  ∷ unresolvedMixedOrSecondaryPeakGeometry
  ∷ []

maximumLocationAlternativeCount : Nat
maximumLocationAlternativeCount = 3

data MaximumLocationBlocker : Set where
  maximumLocationLemmaMissing :
    MaximumLocationBlocker

  offCenterMaximaNotExcluded :
    MaximumLocationBlocker

  positiveSourceFeedbackNotDominated :
    MaximumLocationBlocker

  comparisonEnvelopeAbsentBySprint145 :
    MaximumLocationBlocker

  secondaryPeakAndMixedGeometryOpen :
    MaximumLocationBlocker

  noUnconditionalRegularityRoute :
    MaximumLocationBlocker

canonicalMaximumLocationBlockers :
  List MaximumLocationBlocker
canonicalMaximumLocationBlockers =
  maximumLocationLemmaMissing
  ∷ offCenterMaximaNotExcluded
  ∷ positiveSourceFeedbackNotDominated
  ∷ comparisonEnvelopeAbsentBySprint145
  ∷ secondaryPeakAndMixedGeometryOpen
  ∷ noUnconditionalRegularityRoute
  ∷ []

maximumLocationBlockerCount : Nat
maximumLocationBlockerCount = 6

data MaximumLocationFalsePromotionGuard : Set where
  doNotPromoteSprint136PinnedRouteWithoutLocationLemma :
    MaximumLocationFalsePromotionGuard

  doNotTreatSZeroAtZ0AsGlobalSourceControl :
    MaximumLocationFalsePromotionGuard

  doNotIgnoreOffCenterPositiveFeedback :
    MaximumLocationFalsePromotionGuard

  doNotUseSprint145LocalSupportAsComparisonEnvelope :
    MaximumLocationFalsePromotionGuard

  doNotPromotePartialRegularityRecoveryToClayRegularity :
    MaximumLocationFalsePromotionGuard

canonicalMaximumLocationFalsePromotionGuards :
  List MaximumLocationFalsePromotionGuard
canonicalMaximumLocationFalsePromotionGuards =
  doNotPromoteSprint136PinnedRouteWithoutLocationLemma
  ∷ doNotTreatSZeroAtZ0AsGlobalSourceControl
  ∷ doNotIgnoreOffCenterPositiveFeedback
  ∷ doNotUseSprint145LocalSupportAsComparisonEnvelope
  ∷ doNotPromotePartialRegularityRecoveryToClayRegularity
  ∷ []

maximumLocationFalsePromotionGuardCount : Nat
maximumLocationFalsePromotionGuardCount = 5

centerPinnedStatement : String
centerPinnedStatement =
  "If the omega1 maximum is pinned at z=0, z-reflection gives partial_z u1=0 and S=2 u1 partial_z u1=0 at the maximum"

offCenterMigrationStatement : String
offCenterMigrationStatement =
  "If the omega1 maximum migrates to symmetric off-center maxima z_omega>0 with u1>0 and partial_z u1>0, then S=2 u1 partial_z u1 is positive feedback"

gateStatement : String
gateStatement =
  "MaximumLocationMigrationLemma must decide or exclude migration from z=0 to symmetric off-center positive-feedback maxima"

partialRecoveryStatement : String
partialRecoveryStatement =
  "The regularity route may partially recover only on the pinned-center branch; it is not an unconditional regularity theorem"

failClosedStatement : String
failClosedStatement =
  "Sprint136 supplies the centered S=0 branch and Sprint145 keeps the comparison envelope absent; MaximumLocationMigrationLemma, full_clay_ns_solved, and clayNavierStokesPromoted remain false"

record MaximumLocationMigrationGateSurface : Set where
  constructor maximumLocationMigrationGateSurfaceReceipt
  field
    gateName :
      String
    gateNameIsRequested :
      gateName ≡ "MaximumLocationMigrationLemma"
    centeredBranch :
      String
    centeredBranchIsCanonical :
      centeredBranch ≡ centerPinnedStatement
    offCenterBranch :
      String
    offCenterBranchIsCanonical :
      offCenterBranch ≡ offCenterMigrationStatement
    gateBoundary :
      String
    gateBoundaryIsCanonical :
      gateBoundary ≡ gateStatement
    partialRecoveryBoundary :
      String
    partialRecoveryBoundaryIsCanonical :
      partialRecoveryBoundary ≡ partialRecoveryStatement
    failClosedBoundary :
      String
    failClosedBoundaryIsCanonical :
      failClosedBoundary ≡ failClosedStatement
    sprint136Anchor :
      S136.NSSprint136HouLuoSymmetricSourceSignReceipt
    sprint136AnchorIsCanonical :
      sprint136Anchor ≡ S136.canonicalNSSprint136HouLuoSymmetricSourceSignReceipt
    sprint145Anchor :
      S145.NSSprint145ComparisonEnvelopeObstructionReceipt
    sprint145AnchorIsCanonical :
      sprint145Anchor ≡ S145.canonicalNSSprint145ComparisonEnvelopeObstructionReceipt
    prerequisiteCountField :
      maximumLocationPrerequisiteCount ≡ 6
    alternativeCountField :
      maximumLocationAlternativeCount ≡ 3
    blockerCountField :
      maximumLocationBlockerCount ≡ 6
    falsePromotionGuardCountField :
      maximumLocationFalsePromotionGuardCount ≡ 5
    lemmaStillOpenField :
      MaximumLocationMigrationLemmaOpen ≡ true
    noOffCenterExclusionField :
      offCenterPositiveFeedbackExcluded ≡ false
    noClayPromotionField :
      clayNavierStokesPromoted ≡ false

open MaximumLocationMigrationGateSurface public

canonicalMaximumLocationMigrationGateSurface :
  MaximumLocationMigrationGateSurface
canonicalMaximumLocationMigrationGateSurface =
  maximumLocationMigrationGateSurfaceReceipt
    "MaximumLocationMigrationLemma"
    refl
    centerPinnedStatement
    refl
    offCenterMigrationStatement
    refl
    gateStatement
    refl
    partialRecoveryStatement
    refl
    failClosedStatement
    refl
    S136.canonicalNSSprint136HouLuoSymmetricSourceSignReceipt
    refl
    S145.canonicalNSSprint145ComparisonEnvelopeObstructionReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

data MaximumLocationMigrationPromotion : Set where

maximumLocationMigrationPromotionImpossibleHere :
  MaximumLocationMigrationPromotion →
  ⊥
maximumLocationMigrationPromotionImpossibleHere ()

record MaximumLocationMigrationLemmaReceipt : Set where
  constructor maximumLocationMigrationLemmaReceipt
  field
    gateSurface :
      MaximumLocationMigrationGateSurface
    gateSurfaceIsCanonical :
      gateSurface ≡ canonicalMaximumLocationMigrationGateSurface
    prerequisites :
      List MaximumLocationPrerequisite
    prerequisitesAreCanonical :
      prerequisites ≡ canonicalMaximumLocationPrerequisites
    alternatives :
      List MaximumLocationAlternative
    alternativesAreCanonical :
      alternatives ≡ canonicalMaximumLocationAlternatives
    blockers :
      List MaximumLocationBlocker
    blockersAreCanonical :
      blockers ≡ canonicalMaximumLocationBlockers
    falsePromotionGuards :
      List MaximumLocationFalsePromotionGuard
    falsePromotionGuardsAreCanonical :
      falsePromotionGuards ≡ canonicalMaximumLocationFalsePromotionGuards
    summary :
      String
    summaryIsCanonical :
      summary ≡ failClosedStatement

open MaximumLocationMigrationLemmaReceipt public

canonicalMaximumLocationMigrationLemmaReceipt :
  MaximumLocationMigrationLemmaReceipt
canonicalMaximumLocationMigrationLemmaReceipt =
  maximumLocationMigrationLemmaReceipt
    canonicalMaximumLocationMigrationGateSurface
    refl
    canonicalMaximumLocationPrerequisites
    refl
    canonicalMaximumLocationAlternatives
    refl
    canonicalMaximumLocationBlockers
    refl
    canonicalMaximumLocationFalsePromotionGuards
    refl
    failClosedStatement
    refl

maximumLocationMigrationReceiptPackage :
  MaximumLocationMigrationGateSurface
  × MaximumLocationMigrationLemmaReceipt
maximumLocationMigrationReceiptPackage =
  canonicalMaximumLocationMigrationGateSurface ,
  canonicalMaximumLocationMigrationLemmaReceipt

maximumLocationMigrationCountPackage :
  (maximumLocationPrerequisiteCount ≡ 6)
  × (maximumLocationAlternativeCount ≡ 3)
  × (maximumLocationBlockerCount ≡ 6)
  × (maximumLocationFalsePromotionGuardCount ≡ 5)
maximumLocationMigrationCountPackage =
  refl , refl , refl , refl

maximumLocationMigrationFailClosedPackage :
  (MaximumLocationMigrationLemma ≡ false)
  × (MaximumLocationMigrationLemmaOpen ≡ true)
  × (centerPinnedSourceVanishes ≡ true)
  × (offCenterPositiveFeedbackExcluded ≡ false)
  × (regularityRouteRecoveredUnconditionally ≡ false)
  × (full_clay_ns_solved ≡ false)
  × (clayNavierStokesPromoted ≡ false)
maximumLocationMigrationFailClosedPackage =
  refl , refl , refl , refl , refl , refl , refl
