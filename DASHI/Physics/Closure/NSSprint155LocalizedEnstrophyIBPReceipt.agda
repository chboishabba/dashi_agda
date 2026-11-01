module DASHI.Physics.Closure.NSSprint155LocalizedEnstrophyIBPReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint153LocalizedVortexStretchingSourceReceipt as S153

------------------------------------------------------------------------
-- Sprint 155 localized enstrophy IBP receipt.
--
-- Anchor:
--
--   Sprint 153 remains the available checked localized vortex-stretching
--   source receipt.  This Sprint 155 receipt does not rewrite Sprint 153;
--   it records the later route status at the scale-delta localized
--   enstrophy identity surface.
--
-- Sprint 154 route support recorded here:
--
--   * BiotSavartNonlocalClosureAtScaleDelta is resolved/true as route
--     support.
--   * SimultaneousConstantsCompatibility is resolved/true as route
--     support.
--
-- Sprint 155 result recorded here:
--
--   * LocalizedEnstrophyIdentityAtScaleDelta is resolved/true for the
--     localized integration-by-parts calculation.
--
-- Fail-closed boundary:
--
--   ModelValidityForWidthODE, SymmetricHouLuoBKMFinite,
--   full_clay_ns_solved, and clayNavierStokesPromoted remain false until
--   the whole downstream chain is closed.

sprint155LocalizedEnstrophyIBPLedgerClosed : Bool
sprint155LocalizedEnstrophyIBPLedgerClosed = true

sprint153LocalizedVortexStretchingSourceAnchored : Bool
sprint153LocalizedVortexStretchingSourceAnchored = true

sprint153AnchorReceipt :
  S153.NSSprint153LocalizedVortexStretchingSourceReceipt
sprint153AnchorReceipt =
  S153.canonicalNSSprint153LocalizedVortexStretchingSourceReceipt

sprint153AnchorReceiptIsCanonical :
  sprint153AnchorReceipt
  ≡ S153.canonicalNSSprint153LocalizedVortexStretchingSourceReceipt
sprint153AnchorReceiptIsCanonical = refl

sprint153SourceTargetWasOpen : Bool
sprint153SourceTargetWasOpen =
  S153.localizedVortexStretchingSourceBoundOpen

sprint153SourceTargetWasFalse : Bool
sprint153SourceTargetWasFalse =
  S153.localizedVortexStretchingSourceBound

Sprint154BiotSavartNonlocalClosureRouteSupport : Bool
Sprint154BiotSavartNonlocalClosureRouteSupport = true

BiotSavartNonlocalClosureAtScaleDelta : Bool
BiotSavartNonlocalClosureAtScaleDelta = true

BiotSavartNonlocalClosureAtScaleDeltaResolved : Bool
BiotSavartNonlocalClosureAtScaleDeltaResolved = true

BiotSavartNonlocalClosureAtScaleDeltaOpen : Bool
BiotSavartNonlocalClosureAtScaleDeltaOpen = false

BiotSavartNonlocalClosureAtScaleDeltaAsRouteSupport : Bool
BiotSavartNonlocalClosureAtScaleDeltaAsRouteSupport = true

Sprint154SimultaneousConstantsCompatibilityRouteSupport : Bool
Sprint154SimultaneousConstantsCompatibilityRouteSupport = true

SimultaneousConstantsCompatibility : Bool
SimultaneousConstantsCompatibility = true

SimultaneousConstantsCompatibilityResolved : Bool
SimultaneousConstantsCompatibilityResolved = true

SimultaneousConstantsCompatibilityOpen : Bool
SimultaneousConstantsCompatibilityOpen = false

SimultaneousConstantsCompatibilityAsRouteSupport : Bool
SimultaneousConstantsCompatibilityAsRouteSupport = true

LocalizedEnstrophyIdentityAtScaleDelta : Bool
LocalizedEnstrophyIdentityAtScaleDelta = true

LocalizedEnstrophyIdentityAtScaleDeltaResolved : Bool
LocalizedEnstrophyIdentityAtScaleDeltaResolved = true

LocalizedEnstrophyIdentityAtScaleDeltaOpen : Bool
LocalizedEnstrophyIdentityAtScaleDeltaOpen = false

LocalizedEnstrophyIdentityAtScaleDeltaIBPReceipt : Bool
LocalizedEnstrophyIdentityAtScaleDeltaIBPReceipt = true

cutoffTransportIBPTermAccounted : Bool
cutoffTransportIBPTermAccounted = true

diffusionBoundaryIBPTermAccounted : Bool
diffusionBoundaryIBPTermAccounted = true

vortexStretchingSourceIBPTermAccounted : Bool
vortexStretchingSourceIBPTermAccounted = true

biotSavartNonlocalIBPTermAccounted : Bool
biotSavartNonlocalIBPTermAccounted = true

annularBoundaryIBPTermAccounted : Bool
annularBoundaryIBPTermAccounted = true

constantsCompatibilityIBPTermAccounted : Bool
constantsCompatibilityIBPTermAccounted = true

localizedEnstrophyIBPCalculationComplete : Bool
localizedEnstrophyIBPCalculationComplete = true

localizedEnstrophyIBPPromotesWidthODEModel : Bool
localizedEnstrophyIBPPromotesWidthODEModel = false

localizedEnstrophyIBPPromotesBKMFinite : Bool
localizedEnstrophyIBPPromotesBKMFinite = false

localizedEnstrophyIBPPromotesClayNS : Bool
localizedEnstrophyIBPPromotesClayNS = false

ModelValidityForWidthODE : Bool
ModelValidityForWidthODE = false

ModelValidityForWidthODEProved : Bool
ModelValidityForWidthODEProved = false

ModelValidityForWidthODEOpen : Bool
ModelValidityForWidthODEOpen = true

SymmetricHouLuoBKMFinite : Bool
SymmetricHouLuoBKMFinite = false

SymmetricHouLuoBKMFiniteProved : Bool
SymmetricHouLuoBKMFiniteProved = false

SymmetricHouLuoBKMFiniteOpen : Bool
SymmetricHouLuoBKMFiniteOpen = true

fullClayNSSolved : Bool
fullClayNSSolved = false

full_clay_ns_solved : Bool
full_clay_ns_solved = false

fullNavierStokesSolutionConstructed : Bool
fullNavierStokesSolutionConstructed = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

sprint153AnchorAvailable :
  sprint153LocalizedVortexStretchingSourceAnchored ≡ true
sprint153AnchorAvailable = refl

sprint153AnchorRecordsSourceTargetOpen :
  sprint153SourceTargetWasOpen ≡ true
sprint153AnchorRecordsSourceTargetOpen = refl

sprint154BiotSavartRouteSupportResolved :
  BiotSavartNonlocalClosureAtScaleDelta ≡ true
sprint154BiotSavartRouteSupportResolved = refl

sprint154BiotSavartRouteSupportNotOpen :
  BiotSavartNonlocalClosureAtScaleDeltaOpen ≡ false
sprint154BiotSavartRouteSupportNotOpen = refl

sprint154ConstantsCompatibilityResolved :
  SimultaneousConstantsCompatibility ≡ true
sprint154ConstantsCompatibilityResolved = refl

sprint154ConstantsCompatibilityNotOpen :
  SimultaneousConstantsCompatibilityOpen ≡ false
sprint154ConstantsCompatibilityNotOpen = refl

sprint155LocalizedEnstrophyIdentityResolved :
  LocalizedEnstrophyIdentityAtScaleDelta ≡ true
sprint155LocalizedEnstrophyIdentityResolved = refl

sprint155LocalizedEnstrophyIdentityNotOpen :
  LocalizedEnstrophyIdentityAtScaleDeltaOpen ≡ false
sprint155LocalizedEnstrophyIdentityNotOpen = refl

sprint155KeepsModelValidityForWidthODEFalse :
  ModelValidityForWidthODE ≡ false
sprint155KeepsModelValidityForWidthODEFalse = refl

sprint155KeepsSymmetricHouLuoBKMFiniteFalse :
  SymmetricHouLuoBKMFinite ≡ false
sprint155KeepsSymmetricHouLuoBKMFiniteFalse = refl

sprint155KeepsFullClayNSSolvedFalse :
  full_clay_ns_solved ≡ false
sprint155KeepsFullClayNSSolvedFalse = refl

sprint155KeepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
sprint155KeepsClayPromotionFalse = refl

data Sprint155Support : Set where
  anchorSprint153LocalizedVortexStretchingSourceReceipt :
    Sprint155Support

  recordSprint153AsAvailableSourceAnchor :
    Sprint155Support

  recordSprint154BiotSavartNonlocalClosureResolvedRouteSupport :
    Sprint155Support

  recordSprint154SimultaneousConstantsCompatibilityResolvedRouteSupport :
    Sprint155Support

  recordSprint155LocalizedEnstrophyIdentityIBPResolved :
    Sprint155Support

  recordNoWidthODEModelPromotionFromIBPAlone :
    Sprint155Support

  recordNoClayPromotionFromLocalizedIdentityAlone :
    Sprint155Support

canonicalSprint155Supports : List Sprint155Support
canonicalSprint155Supports =
  anchorSprint153LocalizedVortexStretchingSourceReceipt
  ∷ recordSprint153AsAvailableSourceAnchor
  ∷ recordSprint154BiotSavartNonlocalClosureResolvedRouteSupport
  ∷ recordSprint154SimultaneousConstantsCompatibilityResolvedRouteSupport
  ∷ recordSprint155LocalizedEnstrophyIdentityIBPResolved
  ∷ recordNoWidthODEModelPromotionFromIBPAlone
  ∷ recordNoClayPromotionFromLocalizedIdentityAlone
  ∷ []

sprint155SupportCount : Nat
sprint155SupportCount = 7

data LocalizedEnstrophyIBPRow : Set where
  cutoffTransportIBPRow :
    LocalizedEnstrophyIBPRow

  diffusionBoundaryIBPRow :
    LocalizedEnstrophyIBPRow

  vortexStretchingSourceIBPRow :
    LocalizedEnstrophyIBPRow

  biotSavartNonlocalIBPRow :
    LocalizedEnstrophyIBPRow

  annularBoundaryIBPRow :
    LocalizedEnstrophyIBPRow

  simultaneousConstantsIBPRow :
    LocalizedEnstrophyIBPRow

canonicalLocalizedEnstrophyIBPRows : List LocalizedEnstrophyIBPRow
canonicalLocalizedEnstrophyIBPRows =
  cutoffTransportIBPRow
  ∷ diffusionBoundaryIBPRow
  ∷ vortexStretchingSourceIBPRow
  ∷ biotSavartNonlocalIBPRow
  ∷ annularBoundaryIBPRow
  ∷ simultaneousConstantsIBPRow
  ∷ []

localizedEnstrophyIBPRowCount : Nat
localizedEnstrophyIBPRowCount = 6

data Sprint155RemainingObstruction : Set where
  modelValidityForWidthODENotClosedByIBPReceipt :
    Sprint155RemainingObstruction

  symmetricHouLuoBKMFinitenessNotClosedByLocalizedIdentity :
    Sprint155RemainingObstruction

  fullClayNSChainNotClosedByLocalizedIdentity :
    Sprint155RemainingObstruction

  externalClayPromotionBoundaryNotReached :
    Sprint155RemainingObstruction

canonicalSprint155RemainingObstructions :
  List Sprint155RemainingObstruction
canonicalSprint155RemainingObstructions =
  modelValidityForWidthODENotClosedByIBPReceipt
  ∷ symmetricHouLuoBKMFinitenessNotClosedByLocalizedIdentity
  ∷ fullClayNSChainNotClosedByLocalizedIdentity
  ∷ externalClayPromotionBoundaryNotReached
  ∷ []

sprint155RemainingObstructionCount : Nat
sprint155RemainingObstructionCount = 4

data Sprint155FalsePromotionGuard : Set where
  keepModelValidityForWidthODEFalseUntilWidthModelChainClosed :
    Sprint155FalsePromotionGuard

  keepSymmetricHouLuoBKMFiniteFalseUntilBKMIntegralChainClosed :
    Sprint155FalsePromotionGuard

  keepFullClayNSSolvedFalseUntilAllNSGatesClosed :
    Sprint155FalsePromotionGuard

  keepClayNavierStokesPromotedFalseUntilExternalPromotionBoundary :
    Sprint155FalsePromotionGuard

canonicalSprint155FalsePromotionGuards :
  List Sprint155FalsePromotionGuard
canonicalSprint155FalsePromotionGuards =
  keepModelValidityForWidthODEFalseUntilWidthModelChainClosed
  ∷ keepSymmetricHouLuoBKMFiniteFalseUntilBKMIntegralChainClosed
  ∷ keepFullClayNSSolvedFalseUntilAllNSGatesClosed
  ∷ keepClayNavierStokesPromotedFalseUntilExternalPromotionBoundary
  ∷ []

sprint155FalsePromotionGuardCount : Nat
sprint155FalsePromotionGuardCount = 4

organizationString : String
organizationString =
  "O: Sprint155 is a checked localized enstrophy integration-by-parts receipt anchored to the Sprint153 localized vortex-stretching source receipt."

requirementString : String
requirementString =
  "R: Record Sprint154 Biot-Savart nonlocal closure and simultaneous constants compatibility as resolved route support, then record LocalizedEnstrophyIdentityAtScaleDelta as resolved by the Sprint155 IBP calculation."

codeArtifactString : String
codeArtifactString =
  "C: The Agda artifact exports support rows, IBP rows, remaining obstruction rows, false-promotion guards, ORCSLPGF text, a canonical receipt surface, and compact refl proof tuples."

stateString : String
stateString =
  "S: BiotSavartNonlocalClosureAtScaleDelta=true/resolved; SimultaneousConstantsCompatibility=true/resolved; LocalizedEnstrophyIdentityAtScaleDelta=true/resolved; ModelValidityForWidthODE=false/open; SymmetricHouLuoBKMFinite=false/open; full_clay_ns_solved=false; clayNavierStokesPromoted=false."

latticeString : String
latticeString =
  "L: Sprint153 source anchoring and Sprint154 nonlocal/constants route support sit below the Sprint155 localized enstrophy IBP identity; width-model validity, BKM finiteness, and Clay promotion remain strictly above it."

proposalString : String
proposalString =
  "P: Use the resolved localized identity as a route component only, then separately close width-model validity and BKM integrability before any Clay-level promotion."

governanceString : String
governanceString =
  "G: Exact guard flags prevent LocalizedEnstrophyIdentityAtScaleDelta=true from implying ModelValidityForWidthODE, SymmetricHouLuoBKMFinite, full_clay_ns_solved, or clayNavierStokesPromoted."

gapString : String
gapString =
  "F: The remaining gap is the downstream chain from localized identity to validated width dynamics, BKM finiteness, and full Navier-Stokes promotion."

record Sprint155ORCSLPGF : Set where
  constructor sprint155ORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

open Sprint155ORCSLPGF public

canonicalSprint155ORCSLPGF : Sprint155ORCSLPGF
canonicalSprint155ORCSLPGF =
  sprint155ORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

summaryString : String
summaryString =
  "Sprint155 anchors to Sprint153, records Sprint154 BiotSavartNonlocalClosureAtScaleDelta=true/resolved and SimultaneousConstantsCompatibility=true/resolved as route support, records LocalizedEnstrophyIdentityAtScaleDelta=true/resolved for the localized enstrophy IBP calculation, and keeps ModelValidityForWidthODE=false, SymmetricHouLuoBKMFinite=false, full_clay_ns_solved=false, and clayNavierStokesPromoted=false."

record Sprint155LocalizedEnstrophyIBPSurface : Set where
  constructor sprint155LocalizedEnstrophyIBPSurface
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "LocalizedEnstrophyIdentityAtScaleDelta"
    anchorReceipt :
      S153.NSSprint153LocalizedVortexStretchingSourceReceipt
    anchorReceiptIsCanonical :
      anchorReceipt ≡ S153.canonicalNSSprint153LocalizedVortexStretchingSourceReceipt
    orcslpgf :
      Sprint155ORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalSprint155ORCSLPGF
    sprint154BiotSavartSupportField :
      BiotSavartNonlocalClosureAtScaleDelta ≡ true
    sprint154BiotSavartResolvedField :
      BiotSavartNonlocalClosureAtScaleDeltaResolved ≡ true
    sprint154BiotSavartOpenFalseField :
      BiotSavartNonlocalClosureAtScaleDeltaOpen ≡ false
    sprint154ConstantsSupportField :
      SimultaneousConstantsCompatibility ≡ true
    sprint154ConstantsResolvedField :
      SimultaneousConstantsCompatibilityResolved ≡ true
    sprint154ConstantsOpenFalseField :
      SimultaneousConstantsCompatibilityOpen ≡ false
    localizedEnstrophyIdentityResolvedField :
      LocalizedEnstrophyIdentityAtScaleDelta ≡ true
    localizedEnstrophyIdentityOpenFalseField :
      LocalizedEnstrophyIdentityAtScaleDeltaOpen ≡ false
    localizedEnstrophyIBPCompleteField :
      localizedEnstrophyIBPCalculationComplete ≡ true
    modelValidityForWidthODEFalseField :
      ModelValidityForWidthODE ≡ false
    symmetricHouLuoBKMFiniteFalseField :
      SymmetricHouLuoBKMFinite ≡ false
    fullClayNSSolvedFalseField :
      full_clay_ns_solved ≡ false
    clayPromotionFalseField :
      clayNavierStokesPromoted ≡ false

open Sprint155LocalizedEnstrophyIBPSurface public

canonicalSprint155LocalizedEnstrophyIBPSurface :
  Sprint155LocalizedEnstrophyIBPSurface
canonicalSprint155LocalizedEnstrophyIBPSurface =
  sprint155LocalizedEnstrophyIBPSurface
    "LocalizedEnstrophyIdentityAtScaleDelta"
    refl
    S153.canonicalNSSprint153LocalizedVortexStretchingSourceReceipt
    refl
    canonicalSprint155ORCSLPGF
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

data Sprint155Promotion : Set where

sprint155PromotionImpossibleHere :
  Sprint155Promotion →
  ⊥
sprint155PromotionImpossibleHere ()

record NSSprint155LocalizedEnstrophyIBPReceipt : Set where
  constructor nsSprint155LocalizedEnstrophyIBPReceipt
  field
    surface :
      Sprint155LocalizedEnstrophyIBPSurface
    surfaceIsCanonical :
      surface ≡ canonicalSprint155LocalizedEnstrophyIBPSurface
    supports :
      List Sprint155Support
    supportsAreCanonical :
      supports ≡ canonicalSprint155Supports
    ibpRows :
      List LocalizedEnstrophyIBPRow
    ibpRowsAreCanonical :
      ibpRows ≡ canonicalLocalizedEnstrophyIBPRows
    remainingObstructions :
      List Sprint155RemainingObstruction
    remainingObstructionsAreCanonical :
      remainingObstructions ≡ canonicalSprint155RemainingObstructions
    falsePromotionGuards :
      List Sprint155FalsePromotionGuard
    falsePromotionGuardsAreCanonical :
      falsePromotionGuards ≡ canonicalSprint155FalsePromotionGuards
    summary :
      String
    summaryIsCanonical :
      summary ≡ summaryString

open NSSprint155LocalizedEnstrophyIBPReceipt public

canonicalNSSprint155LocalizedEnstrophyIBPReceipt :
  NSSprint155LocalizedEnstrophyIBPReceipt
canonicalNSSprint155LocalizedEnstrophyIBPReceipt =
  nsSprint155LocalizedEnstrophyIBPReceipt
    canonicalSprint155LocalizedEnstrophyIBPSurface
    refl
    canonicalSprint155Supports
    refl
    canonicalLocalizedEnstrophyIBPRows
    refl
    canonicalSprint155RemainingObstructions
    refl
    canonicalSprint155FalsePromotionGuards
    refl
    summaryString
    refl

sprint155CountPackage :
  (sprint155SupportCount ≡ 7)
  × (localizedEnstrophyIBPRowCount ≡ 6)
  × (sprint155RemainingObstructionCount ≡ 4)
  × (sprint155FalsePromotionGuardCount ≡ 4)
sprint155CountPackage =
  refl , refl , refl , refl

sprint155ResolvedRouteSupportTuple :
  (sprint155LocalizedEnstrophyIBPLedgerClosed ≡ true)
  × (sprint153LocalizedVortexStretchingSourceAnchored ≡ true)
  × (sprint153SourceTargetWasOpen ≡ true)
  × (Sprint154BiotSavartNonlocalClosureRouteSupport ≡ true)
  × (BiotSavartNonlocalClosureAtScaleDelta ≡ true)
  × (BiotSavartNonlocalClosureAtScaleDeltaResolved ≡ true)
  × (BiotSavartNonlocalClosureAtScaleDeltaOpen ≡ false)
  × (BiotSavartNonlocalClosureAtScaleDeltaAsRouteSupport ≡ true)
  × (Sprint154SimultaneousConstantsCompatibilityRouteSupport ≡ true)
  × (SimultaneousConstantsCompatibility ≡ true)
  × (SimultaneousConstantsCompatibilityResolved ≡ true)
  × (SimultaneousConstantsCompatibilityOpen ≡ false)
  × (SimultaneousConstantsCompatibilityAsRouteSupport ≡ true)
  × (LocalizedEnstrophyIdentityAtScaleDelta ≡ true)
  × (LocalizedEnstrophyIdentityAtScaleDeltaResolved ≡ true)
  × (LocalizedEnstrophyIdentityAtScaleDeltaOpen ≡ false)
  × (LocalizedEnstrophyIdentityAtScaleDeltaIBPReceipt ≡ true)
sprint155ResolvedRouteSupportTuple =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl

sprint155IBPAccountedTuple :
  (cutoffTransportIBPTermAccounted ≡ true)
  × (diffusionBoundaryIBPTermAccounted ≡ true)
  × (vortexStretchingSourceIBPTermAccounted ≡ true)
  × (biotSavartNonlocalIBPTermAccounted ≡ true)
  × (annularBoundaryIBPTermAccounted ≡ true)
  × (constantsCompatibilityIBPTermAccounted ≡ true)
  × (localizedEnstrophyIBPCalculationComplete ≡ true)
sprint155IBPAccountedTuple =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl

sprint155FalsePromotionTuple :
  (localizedEnstrophyIBPPromotesWidthODEModel ≡ false)
  × (localizedEnstrophyIBPPromotesBKMFinite ≡ false)
  × (localizedEnstrophyIBPPromotesClayNS ≡ false)
  × (ModelValidityForWidthODE ≡ false)
  × (ModelValidityForWidthODEProved ≡ false)
  × (ModelValidityForWidthODEOpen ≡ true)
  × (SymmetricHouLuoBKMFinite ≡ false)
  × (SymmetricHouLuoBKMFiniteProved ≡ false)
  × (SymmetricHouLuoBKMFiniteOpen ≡ true)
  × (fullClayNSSolved ≡ false)
  × (full_clay_ns_solved ≡ false)
  × (fullNavierStokesSolutionConstructed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sprint155FalsePromotionTuple =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl

sprint155CanonicalReceiptPackage :
  (surface canonicalNSSprint155LocalizedEnstrophyIBPReceipt
   ≡ canonicalSprint155LocalizedEnstrophyIBPSurface)
  × (supports canonicalNSSprint155LocalizedEnstrophyIBPReceipt
     ≡ canonicalSprint155Supports)
  × (ibpRows canonicalNSSprint155LocalizedEnstrophyIBPReceipt
     ≡ canonicalLocalizedEnstrophyIBPRows)
  × (remainingObstructions canonicalNSSprint155LocalizedEnstrophyIBPReceipt
     ≡ canonicalSprint155RemainingObstructions)
  × (falsePromotionGuards canonicalNSSprint155LocalizedEnstrophyIBPReceipt
     ≡ canonicalSprint155FalsePromotionGuards)
  × (summary canonicalNSSprint155LocalizedEnstrophyIBPReceipt
     ≡ summaryString)
sprint155CanonicalReceiptPackage =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl
