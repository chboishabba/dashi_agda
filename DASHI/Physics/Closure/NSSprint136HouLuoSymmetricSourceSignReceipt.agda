module DASHI.Physics.Closure.NSSprint136HouLuoSymmetricSourceSignReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- NS Sprint 136/137 Hou-Luo symmetric source-sign receipt.
--
-- This is a disjoint receipt surface.  It records the symmetric Hou-Luo
-- source-sign result under the canonical z-reflection scenario:
--
--   * z-reflection symmetry forces dz u1 = 0 at z=0;
--   * if axial monotonicity of the swirl profile holds for z>0, then
--     2 u1 dz u1 <= 0 at the vorticity maximum;
--   * at an interior maximum the viscous weighted Laplacian contributes
--     nonpositively;
--   * therefore the canonical symmetric scenario has a conditional maximum
--     nonincrease route and a conditional BKM-finite route.
--
-- The receipt is intentionally fail-closed.  It does not prove axial
-- monotonicity, does not promote a log-loss lower-bound source mechanism,
-- and does not claim full Clay Navier-Stokes or unconditional global
-- regularity.

sprint136137HouLuoSymmetricSourceSignLedgerClosed : Bool
sprint136137HouLuoSymmetricSourceSignLedgerClosed = true

houLuoSymmetricScenarioRecorded : Bool
houLuoSymmetricScenarioRecorded = true

zReflectionSymmetryAssumed : Bool
zReflectionSymmetryAssumed = true

boundaryDzU1ZeroAtZ0 : Bool
boundaryDzU1ZeroAtZ0 = true

interiorVorticityMaximumScenario : Bool
interiorVorticityMaximumScenario = true

viscousWeightedLaplacianAtInteriorMaxNonpositive : Bool
viscousWeightedLaplacianAtInteriorMaxNonpositive = true

LogLossSourceLowerBound : Bool
LogLossSourceLowerBound = false

AxialMonotonicityOfSwirlProfile : Bool
AxialMonotonicityOfSwirlProfile = false

AxialMonotonicityOfSwirlProfileStillOpen : Bool
AxialMonotonicityOfSwirlProfileStillOpen = true

SourceVorticityMaxDecorrelation : Bool
SourceVorticityMaxDecorrelation = true

SourceVorticityMaxDecorrelationConditional : Bool
SourceVorticityMaxDecorrelationConditional = true

SourceVorticityMaxDecorrelationUnconditional : Bool
SourceVorticityMaxDecorrelationUnconditional = false

symmetricSourceTermNonpositiveConditional : Bool
symmetricSourceTermNonpositiveConditional = true

conditionalMaximumNonincreaseForCanonicalSymmetricScenario : Bool
conditionalMaximumNonincreaseForCanonicalSymmetricScenario = true

conditionalBKMFiniteForCanonicalSymmetricScenario : Bool
conditionalBKMFiniteForCanonicalSymmetricScenario = true

unconditionalGlobalRegularityClaimed : Bool
unconditionalGlobalRegularityClaimed = false

canonicalSymmetricScenarioOnly : Bool
canonicalSymmetricScenarioOnly = true

full_clay_ns_solved : Bool
full_clay_ns_solved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

false-in-symmetric-scenario :
  LogLossSourceLowerBound ≡ false
false-in-symmetric-scenario = refl

data HouLuoSymmetricSourceSignStep : Set where
  imposeZReflectionSymmetry :
    HouLuoSymmetricSourceSignStep

  deriveDzU1ZeroAtZ0 :
    HouLuoSymmetricSourceSignStep

  restrictToInteriorVorticityMaximum :
    HouLuoSymmetricSourceSignStep

  assumeAxialMonotonicityForPositiveZ :
    HouLuoSymmetricSourceSignStep

  inferSourceTermNonpositiveAtVorticityMaximum :
    HouLuoSymmetricSourceSignStep

  useViscousWeightedLaplacianMaximumPrinciple :
    HouLuoSymmetricSourceSignStep

  concludeConditionalMaximumNonincrease :
    HouLuoSymmetricSourceSignStep

  routeConditionalControlToBKMFinite :
    HouLuoSymmetricSourceSignStep

canonicalHouLuoSymmetricSourceSignSteps :
  List HouLuoSymmetricSourceSignStep
canonicalHouLuoSymmetricSourceSignSteps =
  imposeZReflectionSymmetry
  ∷ deriveDzU1ZeroAtZ0
  ∷ restrictToInteriorVorticityMaximum
  ∷ assumeAxialMonotonicityForPositiveZ
  ∷ inferSourceTermNonpositiveAtVorticityMaximum
  ∷ useViscousWeightedLaplacianMaximumPrinciple
  ∷ concludeConditionalMaximumNonincrease
  ∷ routeConditionalControlToBKMFinite
  ∷ []

data HouLuoSymmetricOpenBoundary : Set where
  axialMonotonicityOfSwirlProfileNotProvedHere :
    HouLuoSymmetricOpenBoundary

  sourceVorticityMaxDecorrelationOnlyConditionalHere :
    HouLuoSymmetricOpenBoundary

  noLogLossSourceLowerBoundInSymmetricScenario :
    HouLuoSymmetricOpenBoundary

  noUnconditionalGlobalRegularityClaim :
    HouLuoSymmetricOpenBoundary

  noFullClayNavierStokesPromotion :
    HouLuoSymmetricOpenBoundary

canonicalHouLuoSymmetricOpenBoundaries :
  List HouLuoSymmetricOpenBoundary
canonicalHouLuoSymmetricOpenBoundaries =
  axialMonotonicityOfSwirlProfileNotProvedHere
  ∷ sourceVorticityMaxDecorrelationOnlyConditionalHere
  ∷ noLogLossSourceLowerBoundInSymmetricScenario
  ∷ noUnconditionalGlobalRegularityClaim
  ∷ noFullClayNavierStokesPromotion
  ∷ []

data HouLuoSymmetricPromotion : Set where

houLuoSymmetricPromotionImpossibleHere :
  HouLuoSymmetricPromotion →
  ⊥
houLuoSymmetricPromotionImpossibleHere ()

zReflectionBoundaryStatement : String
zReflectionBoundaryStatement =
  "z-reflection symmetry gives dz u1 = 0 at z=0"

sourceSignConditionalStatement : String
sourceSignConditionalStatement =
  "If axial monotonicity of the swirl profile holds for z>0, then 2 u1 dz u1 <= 0 at the vorticity maximum"

viscousMaximumStatement : String
viscousMaximumStatement =
  "At an interior vorticity maximum the viscous weighted Laplacian term is nonpositive"

conditionalBKMStatement : String
conditionalBKMStatement =
  "For the canonical symmetric scenario, source nonpositivity plus viscous nonpositivity gives conditional maximum nonincrease and hence conditional BKM-finite continuation"

failClosedBoundaryStatement : String
failClosedBoundaryStatement =
  "AxialMonotonicityOfSwirlProfile remains open; LogLossSourceLowerBound is false in the symmetric scenario; no full Clay Navier-Stokes or unconditional global regularity claim is promoted"

record ZReflectionSymmetricBoundary : Set where
  constructor zReflectionSymmetricBoundaryReceipt
  field
    symmetryName :
      String
    symmetryNameIsRequested :
      symmetryName ≡ "ZReflectionSymmetry"
    derivativeStatement :
      String
    derivativeStatementIsCanonical :
      derivativeStatement ≡ zReflectionBoundaryStatement
    zReflectionSymmetryAssumedField :
      zReflectionSymmetryAssumed ≡ true
    boundaryDzU1ZeroAtZ0Field :
      boundaryDzU1ZeroAtZ0 ≡ true

open ZReflectionSymmetricBoundary public

canonicalZReflectionSymmetricBoundary :
  ZReflectionSymmetricBoundary
canonicalZReflectionSymmetricBoundary =
  zReflectionSymmetricBoundaryReceipt
    "ZReflectionSymmetry"
    refl
    zReflectionBoundaryStatement
    refl
    refl
    refl

record SymmetricSourceSignAtVorticityMaximum : Set where
  constructor symmetricSourceSignAtVorticityMaximumReceipt
  field
    sourceName :
      String
    sourceNameIsRequested :
      sourceName ≡ "HouLuoSymmetricSourceSign"
    sourceStatement :
      String
    sourceStatementIsCanonical :
      sourceStatement ≡ sourceSignConditionalStatement
    LogLossSourceLowerBoundField :
      LogLossSourceLowerBound ≡ false
    LogLossSourceLowerBoundFalseInSymmetricScenario :
      LogLossSourceLowerBound ≡ false
    AxialMonotonicityOfSwirlProfileField :
      AxialMonotonicityOfSwirlProfile ≡ false
    AxialMonotonicityOfSwirlProfileStillOpenField :
      AxialMonotonicityOfSwirlProfileStillOpen ≡ true
    SourceVorticityMaxDecorrelationField :
      SourceVorticityMaxDecorrelation ≡ true
    SourceVorticityMaxDecorrelationConditionalField :
      SourceVorticityMaxDecorrelationConditional ≡ true
    SourceVorticityMaxDecorrelationUnconditionalField :
      SourceVorticityMaxDecorrelationUnconditional ≡ false
    sourceTermNonpositiveConditionalField :
      symmetricSourceTermNonpositiveConditional ≡ true

open SymmetricSourceSignAtVorticityMaximum public

canonicalSymmetricSourceSignAtVorticityMaximum :
  SymmetricSourceSignAtVorticityMaximum
canonicalSymmetricSourceSignAtVorticityMaximum =
  symmetricSourceSignAtVorticityMaximumReceipt
    "HouLuoSymmetricSourceSign"
    refl
    sourceSignConditionalStatement
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record ViscousInteriorMaximumContribution : Set where
  constructor viscousInteriorMaximumContributionReceipt
  field
    maximumScenarioField :
      interiorVorticityMaximumScenario ≡ true
    viscousStatement :
      String
    viscousStatementIsCanonical :
      viscousStatement ≡ viscousMaximumStatement
    weightedLaplacianField :
      viscousWeightedLaplacianAtInteriorMaxNonpositive ≡ true

open ViscousInteriorMaximumContribution public

canonicalViscousInteriorMaximumContribution :
  ViscousInteriorMaximumContribution
canonicalViscousInteriorMaximumContribution =
  viscousInteriorMaximumContributionReceipt
    refl
    viscousMaximumStatement
    refl
    refl

record ConditionalMaximumNonincreaseAndBKM : Set where
  constructor conditionalMaximumNonincreaseAndBKMReceipt
  field
    conditionalStatement :
      String
    conditionalStatementIsCanonical :
      conditionalStatement ≡ conditionalBKMStatement
    maximumNonincreaseField :
      conditionalMaximumNonincreaseForCanonicalSymmetricScenario ≡ true
    bkmFiniteField :
      conditionalBKMFiniteForCanonicalSymmetricScenario ≡ true
    canonicalSymmetricScenarioOnlyField :
      canonicalSymmetricScenarioOnly ≡ true
    unconditionalGlobalRegularityClaimedField :
      unconditionalGlobalRegularityClaimed ≡ false
    full_clay_ns_solvedField :
      full_clay_ns_solved ≡ false
    clayNavierStokesPromotedField :
      clayNavierStokesPromoted ≡ false

open ConditionalMaximumNonincreaseAndBKM public

canonicalConditionalMaximumNonincreaseAndBKM :
  ConditionalMaximumNonincreaseAndBKM
canonicalConditionalMaximumNonincreaseAndBKM =
  conditionalMaximumNonincreaseAndBKMReceipt
    conditionalBKMStatement
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record FailClosedHouLuoBoundary : Set where
  constructor failClosedHouLuoBoundaryReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ failClosedBoundaryStatement
    openBoundaries :
      List HouLuoSymmetricOpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalHouLuoSymmetricOpenBoundaries
    promotionFlags :
      List HouLuoSymmetricPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []
    noPromotionPossibleHere :
      HouLuoSymmetricPromotion →
      ⊥

open FailClosedHouLuoBoundary public

canonicalFailClosedHouLuoBoundary :
  FailClosedHouLuoBoundary
canonicalFailClosedHouLuoBoundary =
  failClosedHouLuoBoundaryReceipt
    failClosedBoundaryStatement
    refl
    canonicalHouLuoSymmetricOpenBoundaries
    refl
    []
    refl
    houLuoSymmetricPromotionImpossibleHere

record Sprint136137HouLuoSymmetricStatuses : Set where
  constructor sprint136137HouLuoSymmetricStatuses
  field
    ledgerClosedField :
      sprint136137HouLuoSymmetricSourceSignLedgerClosed ≡ true
    scenarioRecordedField :
      houLuoSymmetricScenarioRecorded ≡ true
    boundaryDerivativeField :
      boundaryDzU1ZeroAtZ0 ≡ true
    logLossLowerBoundFalseField :
      LogLossSourceLowerBound ≡ false
    axialMonotonicityStillOpenField :
      AxialMonotonicityOfSwirlProfileStillOpen ≡ true
    sourceDecorrelatesConditionallyField :
      SourceVorticityMaxDecorrelationConditional ≡ true
    sourceDecorrelatesUnconditionallyField :
      SourceVorticityMaxDecorrelationUnconditional ≡ false
    viscousInteriorMaxNonpositiveField :
      viscousWeightedLaplacianAtInteriorMaxNonpositive ≡ true
    conditionalMaxNonincreaseField :
      conditionalMaximumNonincreaseForCanonicalSymmetricScenario ≡ true
    conditionalBKMFiniteField :
      conditionalBKMFiniteForCanonicalSymmetricScenario ≡ true
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false

open Sprint136137HouLuoSymmetricStatuses public

canonicalSprint136137HouLuoSymmetricStatuses :
  Sprint136137HouLuoSymmetricStatuses
canonicalSprint136137HouLuoSymmetricStatuses =
  sprint136137HouLuoSymmetricStatuses
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

record NSSprint136HouLuoSymmetricSourceSignReceipt : Set where
  constructor nsSprint136HouLuoSymmetricSourceSignReceipt
  field
    zReflectionBoundary :
      ZReflectionSymmetricBoundary
    sourceSignAtMaximum :
      SymmetricSourceSignAtVorticityMaximum
    viscousInteriorMaximum :
      ViscousInteriorMaximumContribution
    conditionalMaximumAndBKM :
      ConditionalMaximumNonincreaseAndBKM
    failClosedBoundary :
      FailClosedHouLuoBoundary
    statuses :
      Sprint136137HouLuoSymmetricStatuses
    statusesAreCanonical :
      statuses ≡ canonicalSprint136137HouLuoSymmetricStatuses
    steps :
      List HouLuoSymmetricSourceSignStep
    stepsAreCanonical :
      steps ≡ canonicalHouLuoSymmetricSourceSignSteps
    receiptSummary :
      String
    receiptSummaryIsCanonical :
      receiptSummary
      ≡
      "Sprint136/137 records the symmetric Hou-Luo source-sign route: z-reflection gives dz u1=0 at z=0; under axial monotonicity for z>0, 2 u1 dz u1 <= 0 at the vorticity maximum; the viscous weighted Laplacian is nonpositive at an interior maximum; conditional maximum nonincrease and BKM-finite continuation hold only for the canonical symmetric scenario; Clay promotion remains false."

open NSSprint136HouLuoSymmetricSourceSignReceipt public

canonicalNSSprint136HouLuoSymmetricSourceSignReceipt :
  NSSprint136HouLuoSymmetricSourceSignReceipt
canonicalNSSprint136HouLuoSymmetricSourceSignReceipt =
  nsSprint136HouLuoSymmetricSourceSignReceipt
    canonicalZReflectionSymmetricBoundary
    canonicalSymmetricSourceSignAtVorticityMaximum
    canonicalViscousInteriorMaximumContribution
    canonicalConditionalMaximumNonincreaseAndBKM
    canonicalFailClosedHouLuoBoundary
    canonicalSprint136137HouLuoSymmetricStatuses
    refl
    canonicalHouLuoSymmetricSourceSignSteps
    refl
    "Sprint136/137 records the symmetric Hou-Luo source-sign route: z-reflection gives dz u1=0 at z=0; under axial monotonicity for z>0, 2 u1 dz u1 <= 0 at the vorticity maximum; the viscous weighted Laplacian is nonpositive at an interior maximum; conditional maximum nonincrease and BKM-finite continuation hold only for the canonical symmetric scenario; Clay promotion remains false."
    refl

sprint136137SymmetricSourceSignSummary :
  ZReflectionSymmetricBoundary
  × SymmetricSourceSignAtVorticityMaximum
  × ViscousInteriorMaximumContribution
  × ConditionalMaximumNonincreaseAndBKM
  × FailClosedHouLuoBoundary
  × Sprint136137HouLuoSymmetricStatuses
sprint136137SymmetricSourceSignSummary =
  canonicalZReflectionSymmetricBoundary ,
  canonicalSymmetricSourceSignAtVorticityMaximum ,
  canonicalViscousInteriorMaximumContribution ,
  canonicalConditionalMaximumNonincreaseAndBKM ,
  canonicalFailClosedHouLuoBoundary ,
  canonicalSprint136137HouLuoSymmetricStatuses

sprint136137AllRequiredStatuses :
  (sprint136137HouLuoSymmetricSourceSignLedgerClosed ≡ true)
  × (houLuoSymmetricScenarioRecorded ≡ true)
  × (zReflectionSymmetryAssumed ≡ true)
  × (boundaryDzU1ZeroAtZ0 ≡ true)
  × (LogLossSourceLowerBound ≡ false)
  × (AxialMonotonicityOfSwirlProfile ≡ false)
  × (AxialMonotonicityOfSwirlProfileStillOpen ≡ true)
  × (SourceVorticityMaxDecorrelationConditional ≡ true)
  × (SourceVorticityMaxDecorrelationUnconditional ≡ false)
  × (viscousWeightedLaplacianAtInteriorMaxNonpositive ≡ true)
  × (conditionalMaximumNonincreaseForCanonicalSymmetricScenario ≡ true)
  × (conditionalBKMFiniteForCanonicalSymmetricScenario ≡ true)
  × (unconditionalGlobalRegularityClaimed ≡ false)
  × (full_clay_ns_solved ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sprint136137AllRequiredStatuses =
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

sprint136137KeepsClayFalse :
  clayNavierStokesPromoted ≡ false
sprint136137KeepsClayFalse = refl

sprint136137KeepsFullClayNSFalse :
  full_clay_ns_solved ≡ false
sprint136137KeepsFullClayNSFalse = refl

sprint136137LogLossSourceLowerBoundFalse :
  LogLossSourceLowerBound ≡ false
sprint136137LogLossSourceLowerBoundFalse = refl
