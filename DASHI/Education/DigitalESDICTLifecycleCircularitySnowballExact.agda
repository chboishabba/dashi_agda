module DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Parent

------------------------------------------------------------------------
-- ICT LIFECYCLE / CIRCULARITY ACQUISITION SNOWBALL
--
-- This owner refines, rather than falsely closes, the parent's
-- `openInteroperabilityDurability` residual.  ITU-T L.1410 and L.1023 pay
-- source-role/method coordinates.  They do not supply a same-object life-cycle
-- inventory, product circularity measurement, durability observation, repair
-- receipt, spare-parts receipt, or deployment authority for the proposed
-- digital-ESD intervention.
--
-- Attribution invariant:
--   source identity + role + same-object status survive every snowball step;
--   citation imports neither proof nor authority;
--   acquisition order need not equal payment order;
--   downstream payment cannot skip an unpaid same-object dependency.
------------------------------------------------------------------------

ituL1410LifecycleMethodSource : Attr.AttributedSource
ituL1410LifecycleMethodSource =
  Attr.mkNoDOISource
    "International Telecommunication Union, ITU-T Study Group 5"
    "ITU-T L.1410 (11/2024): Methodology for environmental life cycle assessments of information and communication technology goods, networks and services"
    "ITU-T Recommendation L.1410"
    "2024"
    "https://www.itu.int/rec/T-REC-L.1410-202411-I"
    Attr.institutionalSource
    "In-force ICT LCA methodology. Part I provides framework/guidance for ICT goods, networks and services; Part II provides comparative-analysis framework against a reference product system. Method authority only: it does not supply the proposed digital-ESD deployment's life-cycle inventory or result."
    Attr.publicAttribution

ituL1023CircularityMethodSource : Attr.AttributedSource
ituL1023CircularityMethodSource =
  Attr.mkNoDOISource
    "International Telecommunication Union, ITU-T Study Group 5"
    "ITU-T L.1023 (08/2023): Assessment method for circularity performance scoring"
    "ITU-T Recommendation L.1023"
    "2023"
    "https://www.itu.int/rec/T-REC-L.1023-202308-I"
    Attr.institutionalSource
    "In-force ICT circularity assessment method. It scores applicable circularity indicators and includes durability plus recycle, repair, reuse and upgrade aspects. Method authority only: it does not supply a score or empirical repair/durability facts for the proposed deployment."
    Attr.publicAttribution

canonicalICTLifecycleCircularitySourceAtlas : Attr.AttributedSourceAtlas
canonicalICTLifecycleCircularitySourceAtlas =
  Attr.mkSourceAtlas
    "digital ESD ICT lifecycle and circularity method snowball"
    "DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact"
    ( ituL1410LifecycleMethodSource
    ∷ ituL1023CircularityMethodSource
    ∷ []
    )
    "Primary ITU-T method sources refine the open digital-ESD durability/lifecycle leaf without promoting standards into measurements of the actual intervention."

l1410SourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt ituL1410LifecycleMethodSource
l1410SourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt ituL1410LifecycleMethodSource

l1023SourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt ituL1023CircularityMethodSource
l1023SourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt ituL1023CircularityMethodSource

------------------------------------------------------------------------
-- Paid source-role coordinates.
------------------------------------------------------------------------

record ICTLifecycleCircularityAcquisition : Set where
  constructor ict-lifecycle-circularity-acquisition
  field
    attributedSources : Attr.AttributedSourceAtlas

    ictLCAMethodSourcePaid : Bool
    ictLCAMethodSourcePaidIsTrue : ictLCAMethodSourcePaid ≡ true

    ictCircularityMethodSourcePaid : Bool
    ictCircularityMethodSourcePaidIsTrue :
      ictCircularityMethodSourcePaid ≡ true

    lcaCoversICTGoodsNetworksServices : Bool
    lcaCoversICTGoodsNetworksServicesIsTrue :
      lcaCoversICTGoodsNetworksServices ≡ true

    comparativeLCARequiresReferenceSystem : Bool
    comparativeLCARequiresReferenceSystemIsTrue :
      comparativeLCARequiresReferenceSystem ≡ true

    circularityIncludesDurability : Bool
    circularityIncludesDurabilityIsTrue : circularityIncludesDurability ≡ true

    circularityIncludesRepairReuseRecycleUpgrade : Bool
    circularityIncludesRepairReuseRecycleUpgradeIsTrue :
      circularityIncludesRepairReuseRecycleUpgrade ≡ true

    sourceRolesRetained : Bool
    sourceRolesRetainedIsTrue : sourceRolesRetained ≡ true

    sameObjectDeploymentInventoryObserved : Bool
    sameObjectDeploymentInventoryObservedIsFalse :
      sameObjectDeploymentInventoryObserved ≡ false

    sameObjectCircularityScoreObserved : Bool
    sameObjectCircularityScoreObservedIsFalse :
      sameObjectCircularityScoreObserved ≡ false

    sameObjectRepairabilityObserved : Bool
    sameObjectRepairabilityObservedIsFalse :
      sameObjectRepairabilityObserved ≡ false

    citationCreatesProof : Bool
    citationCreatesProofIsFalse : citationCreatesProof ≡ false

    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false

open ICTLifecycleCircularityAcquisition public

canonicalICTLifecycleCircularityAcquisition : ICTLifecycleCircularityAcquisition
canonicalICTLifecycleCircularityAcquisition =
  ict-lifecycle-circularity-acquisition
    canonicalICTLifecycleCircularitySourceAtlas
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Explicit non-promotion firewalls.
------------------------------------------------------------------------

data ICTLifecycleMethodPaysDeploymentInventory : Set where

ictLifecycleMethodDoesNotPayDeploymentInventory :
  ICTLifecycleMethodPaysDeploymentInventory → ⊥
ictLifecycleMethodDoesNotPayDeploymentInventory ()

data CircularityMethodPaysDeploymentCircularity : Set where

circularityMethodDoesNotPayDeploymentCircularity :
  CircularityMethodPaysDeploymentCircularity → ⊥
circularityMethodDoesNotPayDeploymentCircularity ()

data CircularityMethodProvesDeploymentDurability : Set where

circularityMethodDoesNotProveDeploymentDurability :
  CircularityMethodProvesDeploymentDurability → ⊥
circularityMethodDoesNotProveDeploymentDurability ()

data LCAFrameworkMakesOnlineScenarioUniversallyGreener : Set where

lcaFrameworkDoesNotMakeOnlineScenarioUniversallyGreener :
  LCAFrameworkMakesOnlineScenarioUniversallyGreener → ⊥
lcaFrameworkDoesNotMakeOnlineScenarioUniversallyGreener ()

data CircularityScoreCreatesProcurementAuthority : Set where

circularityScoreDoesNotCreateProcurementAuthority :
  CircularityScoreCreatesProcurementAuthority → ⊥
circularityScoreDoesNotCreateProcurementAuthority ()

------------------------------------------------------------------------
-- Refined payment fibre.
--
-- The parent has one open `openInteroperabilityDurability` leaf.  This owner
-- opens its method/same-object residual structure without changing the parent
-- payment state.  Source methods are paid; deployment facts remain unpaid.
------------------------------------------------------------------------

data RefinedLifecycleLeaf : Set where
  ictLifecycleMethod : RefinedLifecycleLeaf
  ictCircularityMethod : RefinedLifecycleLeaf
  deploymentSpecificLCI : RefinedLifecycleLeaf
  deploymentReferenceSystem : RefinedLifecycleLeaf
  deploymentHardwareCircularity : RefinedLifecycleLeaf
  deploymentRepairSupport : RefinedLifecycleLeaf
  deploymentServiceLife : RefinedLifecycleLeaf
  deploymentInteroperabilityPersistence : RefinedLifecycleLeaf

data RefinedPaymentState : Set where
  unpaidRefined : RefinedPaymentState
  sourceRolePaidRefined : RefinedPaymentState
  sameObjectPaidRefined : RefinedPaymentState

refinedPaymentState : RefinedLifecycleLeaf → RefinedPaymentState
refinedPaymentState ictLifecycleMethod = sourceRolePaidRefined
refinedPaymentState ictCircularityMethod = sourceRolePaidRefined
refinedPaymentState deploymentSpecificLCI = unpaidRefined
refinedPaymentState deploymentReferenceSystem = unpaidRefined
refinedPaymentState deploymentHardwareCircularity = unpaidRefined
refinedPaymentState deploymentRepairSupport = unpaidRefined
refinedPaymentState deploymentServiceLife = unpaidRefined
refinedPaymentState deploymentInteroperabilityPersistence = unpaidRefined

refinedLeafReference : RefinedLifecycleLeaf → String
refinedLeafReference ictLifecycleMethod =
  "ITU-T L.1410 ICT LCA framework/guidance: source-role paid"
refinedLeafReference ictCircularityMethod =
  "ITU-T L.1023 ICT circularity performance method: source-role paid"
refinedLeafReference deploymentSpecificLCI =
  "same-object inventory for actual learner devices, institution/network, cloud/service and associated material/energy flows"
refinedLeafReference deploymentReferenceSystem =
  "consumer-declared same-object baseline/reference system for any comparative environmental claim"
refinedLeafReference deploymentHardwareCircularity =
  "actual selected ICT goods scored/observed for relevant circularity indicators"
refinedLeafReference deploymentRepairSupport =
  "same-object spare-parts, documentation, repair access, maintenance capacity and support-window evidence"
refinedLeafReference deploymentServiceLife =
  "observed/contracted service-life, update/support and replacement assumptions for the actual deployment"
refinedLeafReference deploymentInteroperabilityPersistence =
  "same-object evidence that export, standards, interfaces and migration paths persist over the relevant time horizon"

currentRefinedLifecycleFrontier : List RefinedLifecycleLeaf
currentRefinedLifecycleFrontier =
  deploymentSpecificLCI
  ∷ deploymentReferenceSystem
  ∷ deploymentHardwareCircularity
  ∷ deploymentRepairSupport
  ∷ deploymentServiceLife
  ∷ deploymentInteroperabilityPersistence
  ∷ []

------------------------------------------------------------------------
-- BIDI: source method -> bounded coordinate; consumer claim -> reopen same
-- object acquisition.  The method reduces *method debt*, not empirical debt.
------------------------------------------------------------------------

record ICTLifecycleMethodBidiReceipt : Set where
  constructor ict-lifecycle-method-bidi-receipt
  field
    sourceReference : String
    boundedForwardPayment : String
    reverseReopenObligation : String
    sourceIdentityRetained : Bool
    sourceRoleRetained : Bool
    sameObjectStatusRetained : Bool
    methodPaymentClosesDeploymentObservation : Bool
    citationCreatesAuthority : Bool

open ICTLifecycleMethodBidiReceipt public

l1410LifecycleBidi : ICTLifecycleMethodBidiReceipt
l1410LifecycleBidi =
  ict-lifecycle-method-bidi-receipt
    "ITU-T L.1410 (11/2024), in-force ICT LCA methodology"
    "pay the method coordinate for ICT goods/networks/services LCA and comparative reference-system analysis"
    "before any deployment footprint/comparison claim, acquire the actual intervention LCI, goal/scope, reference system where comparative, uncertainty/sensitivity inputs and same-object provenance"
    true true true false false

l1023CircularityBidi : ICTLifecycleMethodBidiReceipt
l1023CircularityBidi =
  ict-lifecycle-method-bidi-receipt
    "ITU-T L.1023 (08/2023), in-force ICT circularity performance scoring method"
    "pay the method coordinate for applicable durability/recycle/repair/reuse/upgrade indicators"
    "before any deployment circularity/durability claim, acquire the actual product/manufacturer evidence, indicator applicability and same-object score/observations"
    true true true false false

------------------------------------------------------------------------
-- Parent-residual preservation.
------------------------------------------------------------------------

parentOpenDurabilityLeaf : Parent.AcquisitionLeaf
parentOpenDurabilityLeaf = Parent.openInteroperabilityDurability

parentOpenDurabilityState : Parent.PaymentState
parentOpenDurabilityState = Parent.paymentState parentOpenDurabilityLeaf

parentOpenDurabilityRemainsUnpaid :
  parentOpenDurabilityState ≡ Parent.unpaid
parentOpenDurabilityRemainsUnpaid = refl

record ICTLifecycleCircularitySnowballBoundary : Set where
  constructor ict-lifecycle-circularity-snowball-boundary
  field
    sourceMethodEqualsSameObjectMeasurement : Bool
    methodStandardEqualsObservedDurability : Bool
    circularityMethodEqualsDeploymentScore : Bool
    methodPaymentClosesParentResidual : Bool
    oneMethodImpliesUniversalComparativeResult : Bool
    sourceRoleAndSameObjectRemainDistinct : Bool
    paidMethodMayRefineUnpaidParentLeaf : Bool
    downstreamClaimMaySkipSameObjectInventory : Bool

open ICTLifecycleCircularitySnowballBoundary public

canonicalICTLifecycleCircularitySnowballBoundary :
  ICTLifecycleCircularitySnowballBoundary
canonicalICTLifecycleCircularitySnowballBoundary =
  ict-lifecycle-circularity-snowball-boundary
    false false false false false true true false

highestAlphaLifecycleReading : String
highestAlphaLifecycleReading =
  "ITU-T L.1410 and L.1023 now pay ICT lifecycle/circularity method coordinates. The Pareto frontier therefore contracts by method debt, but not by same-object empirical debt: the actual digital-ESD deployment still needs its LCI/reference system, hardware circularity/repair support/service-life evidence and persistent interoperability evidence before lifecycle or durability conclusions can be promoted."
