module DASHI.Promotion.Gate3StandardModelClayEvidenceReducer where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.Gate3ClayObligations as Gate3Clay
import DASHI.Promotion.StandardModelTerminalObligations as SMT

import DASHI.Physics.Closure.Gate3PrunedDensityMoscoReceipt as Gate3Mosco
import DASHI.Physics.Closure.Gate3NoSpectralPollutionReceipt as Gate3NSP
import DASHI.Physics.Closure.CarrierEnergyToMassShellReceipt as MassShell
import DASHI.Physics.QFT.SMContentSummaryReceipt as SMContent
import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM
import DASHI.Physics.Closure.ClayNSCurrentStateReceipt as NSState
import DASHI.Physics.Closure.YMClayFinalStateReceipt as YMState
import DASHI.Physics.Closure.TerminalOpenProblemStatusSurface as Terminal

------------------------------------------------------------------------
-- Gate3/SM/Clay evidence reducer.
--
-- This module is not a new promotion receipt.  It reduces the already typed
-- evidence owners into the exact token classes that still block Gate 3,
-- Standard Model, Navier-Stokes Clay, Yang-Mills Clay, and terminal claims.

data EvidenceLane : Set where
  gate3Lane :
    EvidenceLane

  standardModelLane :
    EvidenceLane

  navierStokesLane :
    EvidenceLane

  yangMillsLane :
    EvidenceLane

  terminalLane :
    EvidenceLane

data EvidenceClass : Set where
  presentInternalCandidate :
    EvidenceClass

  authorityMissing :
    EvidenceClass

  proofMissing :
    EvidenceClass

  translationMissing :
    EvidenceClass

data ReducerToken : Set where
  gate3DensityCandidateToken :
    ReducerToken

  gate3MoscoLiminfToken :
    ReducerToken

  gate3MoscoRecoveryToken :
    ReducerToken

  gate3NoSpectralPollutionConditionalToken :
    ReducerToken

  gate3ContinuumTransferToken :
    ReducerToken

  gate3MassShellBridgeToken :
    ReducerToken

  gate3ClosureToken :
    ReducerToken

  smContentSummaryToken :
    ReducerToken

  smFiniteDHRAndSU3Token :
    ReducerToken

  smCarrierFunctorEquivalenceToken :
    ReducerToken

  smDHRCompactGroupTranslationToken :
    ReducerToken

  smLowEnergySU2RBreakingToken :
    ReducerToken

  smPDGAuthorityToken :
    ReducerToken

  smPhysicalSectorMapToken :
    ReducerToken

  smEmpiricalObservableAuthorityToken :
    ReducerToken

  nsLerayWeakBranchToken :
    ReducerToken

  nsPressureReconstructionToken :
    ReducerToken

  nsNonlinearTermPassageToken :
    ReducerToken

  nsEnergyInequalityToken :
    ReducerToken

  nsH118ClayEquivalentHardOpenToken :
    ReducerToken

  nsSprint145ComparisonEnvelopeFailedClosedToken :
    ReducerToken

  nsMaximumLocationMigrationLemmaToken :
    ReducerToken

  nsGlobalSmoothnessToken :
    ReducerToken

  ymFiniteCarrierLayerToken :
    ReducerToken

  ymWilsonActionCandidateToken :
    ReducerToken

  ymOSPositivityToken :
    ReducerToken

  ymContinuumLimitToken :
    ReducerToken

  ymWightmanTranslationToken :
    ReducerToken

  ymPositiveMassGapToken :
    ReducerToken

  ymExternalAcceptanceToken :
    ReducerToken

  terminalOpenStatusToken :
    ReducerToken

  terminalCrossLaneConsistencyToken :
    ReducerToken

  terminalAggregateValidationToken :
    ReducerToken

  terminalClaimSurfaceAuditToken :
    ReducerToken

  terminalTheoremAuthorityToken :
    ReducerToken

data EvidenceOwner : Set where
  gate3ObligationOwner :
    EvidenceOwner

  smTerminalObligationOwner :
    EvidenceOwner

  gate3MoscoOwner :
    EvidenceOwner

  gate3NoSpectralPollutionOwner :
    EvidenceOwner

  massShellOwner :
    EvidenceOwner

  smContentOwner :
    EvidenceOwner

  exactSMOwner :
    EvidenceOwner

  nsStateOwner :
    EvidenceOwner

  ymStateOwner :
    EvidenceOwner

  terminalOpenOwner :
    EvidenceOwner

record EvidenceReducerRow : Set where
  field
    lane :
      EvidenceLane

    token :
      ReducerToken

    classification :
      EvidenceClass

    owner :
      EvidenceOwner

    evidenceName :
      String

    requiredForGuard :
      String

    missingDischarge :
      String

open EvidenceReducerRow public

mkRow :
  EvidenceLane →
  ReducerToken →
  EvidenceClass →
  EvidenceOwner →
  String →
  String →
  String →
  EvidenceReducerRow
mkRow lane token classification owner evidenceName requiredForGuard missingDischarge =
  record
    { lane = lane
    ; token = token
    ; classification = classification
    ; owner = owner
    ; evidenceName = evidenceName
    ; requiredForGuard = requiredForGuard
    ; missingDischarge = missingDischarge
    }

rowCount : List EvidenceReducerRow → Nat
rowCount [] =
  zero
rowCount (_ ∷ rows) =
  suc (rowCount rows)

infixr 5 _++_

_++_ : List EvidenceReducerRow → List EvidenceReducerRow → List EvidenceReducerRow
[] ++ ys =
  ys
(x ∷ xs) ++ ys =
  x ∷ (xs ++ ys)

statusCount : EvidenceClass → List EvidenceReducerRow → Nat
statusCount wanted [] =
  zero
statusCount presentInternalCandidate (row ∷ rows) with classification row
... | presentInternalCandidate =
  suc (statusCount presentInternalCandidate rows)
... | authorityMissing =
  statusCount presentInternalCandidate rows
... | proofMissing =
  statusCount presentInternalCandidate rows
... | translationMissing =
  statusCount presentInternalCandidate rows
statusCount authorityMissing (row ∷ rows) with classification row
... | presentInternalCandidate =
  statusCount authorityMissing rows
... | authorityMissing =
  suc (statusCount authorityMissing rows)
... | proofMissing =
  statusCount authorityMissing rows
... | translationMissing =
  statusCount authorityMissing rows
statusCount proofMissing (row ∷ rows) with classification row
... | presentInternalCandidate =
  statusCount proofMissing rows
... | authorityMissing =
  statusCount proofMissing rows
... | proofMissing =
  suc (statusCount proofMissing rows)
... | translationMissing =
  statusCount proofMissing rows
statusCount translationMissing (row ∷ rows) with classification row
... | presentInternalCandidate =
  statusCount translationMissing rows
... | authorityMissing =
  statusCount translationMissing rows
... | proofMissing =
  statusCount translationMissing rows
... | translationMissing =
  suc (statusCount translationMissing rows)

gate3Owner :
  EvidenceOwner
gate3Owner =
  gate3ObligationOwner

smTerminalOwner :
  EvidenceOwner
smTerminalOwner =
  smTerminalObligationOwner

canonicalGate3EvidenceRows : List EvidenceReducerRow
canonicalGate3EvidenceRows =
  mkRow
    gate3Lane
    gate3DensityCandidateToken
    presentInternalCandidate
    gate3MoscoOwner
    "Gate3PrunedDensityMoscoReceipt.finitePrunedFrameExists=true"
    "gate3Closed"
    "uniform level density and continuum covering/separation bounds are not proved"
  ∷ mkRow
    gate3Lane
    gate3MoscoLiminfToken
    proofMissing
    gate3Owner
    "Gate3ClayObligations.moscoLiminfPromoted=false"
    "moscoLiminfPromoted"
    "liminf lower-semicontinuity over the target continuum operator is still absent"
  ∷ mkRow
    gate3Lane
    gate3MoscoRecoveryToken
    proofMissing
    gate3MoscoOwner
    "Gate3PrunedDensityMoscoReceipt.prunedMoscoRecoveryProved=false"
    "moscoRecoveryPromoted"
    "constructive recovery sequence remains open"
  ∷ mkRow
    gate3Lane
    gate3NoSpectralPollutionConditionalToken
    presentInternalCandidate
    gate3NoSpectralPollutionOwner
    "Gate3NoSpectralPollutionReceipt.conditional receipt"
    "noSpectralPollutionPromoted"
    "conditional operator receipt still requires unconditional phase/twist and Mosco discharge"
  ∷ mkRow
    gate3Lane
    gate3ContinuumTransferToken
    proofMissing
    gate3Owner
    "Gate3ClayObligations.continuumTransferPromoted=false"
    "continuumTransferPromoted"
    "finite/pruned spectral transfer has not been promoted to the continuum operator"
  ∷ mkRow
    gate3Lane
    gate3MassShellBridgeToken
    translationMissing
    massShellOwner
    "CarrierEnergyToMassShellReceipt.internalCarrierEnergyGapRecorded=true"
    "massShellBridgePromoted"
    "internal carrier energy gap is not translated to physical mass-shell gap"
  ∷ mkRow
    gate3Lane
    gate3ClosureToken
    proofMissing
    gate3Owner
    "Gate3ClayObligations.gate3Closed=false"
    "gate3Closed"
    "Gate 3 cannot close before Mosco, no-pollution, transfer, and mass-shell discharge"
  ∷ []

canonicalStandardModelEvidenceRows : List EvidenceReducerRow
canonicalStandardModelEvidenceRows =
  mkRow
    standardModelLane
    smContentSummaryToken
    presentInternalCandidate
    smContentOwner
    "SMContentSummaryReceipt finite content map"
    "standardModelPromoted"
    "summary records candidates and blockers but not a complete Standard Model construction"
  ∷ mkRow
    standardModelLane
    smFiniteDHRAndSU3Token
    presentInternalCandidate
    exactSMOwner
    "ExactSMMatchBlockerReceipt upstream finite U1/SU2/SU3 witnesses"
    "standardModelPromoted"
    "finite witnesses are packaged but exact SM match remains blocked"
  ∷ mkRow
    standardModelLane
    smCarrierFunctorEquivalenceToken
    proofMissing
    exactSMOwner
    "blockedByNoGate1Gate6CarrierFunctorEquivalence"
    "standardModelPromoted"
    "Gate 1/Gate 6 carrier-functor equivalence is not constructed"
  ∷ mkRow
    standardModelLane
    smDHRCompactGroupTranslationToken
    translationMissing
    exactSMOwner
    "blockedByNoDHRCompactGroupToSMGaugeIsomorphism"
    "standardModelPromoted"
    "DHR compact group is not translated to SU3 x SU2 x U1 as a physical gauge isomorphism"
  ∷ mkRow
    standardModelLane
    smLowEnergySU2RBreakingToken
    proofMissing
    exactSMOwner
    "blockedByNoLowEnergySU2RBreakingReceipt"
    "standardModelPromoted"
    "low-energy SU2R breaking receipt is not supplied"
  ∷ mkRow
    standardModelLane
    smPDGAuthorityToken
    authorityMissing
    smTerminalOwner
    "PDG/Higgs/Yukawa/CKM/PMNS authority row"
    "standardModelPromoted"
    "accepted particle-data authority and per-slot consumption tokens are not bound here"
  ∷ mkRow
    standardModelLane
    smPhysicalSectorMapToken
    translationMissing
    smTerminalOwner
    "physical sector map obligation"
    "standardModelPromoted"
    "finite sectors are not yet translated to the full low-energy physical sector map"
  ∷ mkRow
    standardModelLane
    smEmpiricalObservableAuthorityToken
    authorityMissing
    smTerminalOwner
    "SM empirical observable bridge obligation"
    "standardModelPromoted"
    "empirical observable authority and validation protocol are still absent"
  ∷ []

canonicalNavierStokesEvidenceRows : List EvidenceReducerRow
canonicalNavierStokesEvidenceRows =
  mkRow
    navierStokesLane
    nsLerayWeakBranchToken
    presentInternalCandidate
    nsStateOwner
    "ClayNSCurrentStateReceipt.lerayWeakSolutionBranchAvailable=true"
    "navierStokesClayPromoted"
    "Leray weak branch does not imply global smooth regularity"
  ∷ mkRow
    navierStokesLane
    nsPressureReconstructionToken
    proofMissing
    gate3Owner
    "Navier-Stokes pressure reconstruction obligation"
    "navierStokesClayPromoted"
    "pressure reconstruction compatible with the Clay formulation is not discharged"
  ∷ mkRow
    navierStokesLane
    nsNonlinearTermPassageToken
    proofMissing
    gate3Owner
    "Navier-Stokes nonlinear term passage obligation"
    "navierStokesClayPromoted"
    "nonlinear term passage in the target solution class is not proved"
  ∷ mkRow
    navierStokesLane
    nsEnergyInequalityToken
    proofMissing
    gate3Owner
    "Navier-Stokes energy inequality obligation"
    "navierStokesClayPromoted"
    "energy inequality is not elevated to a Clay-equivalent regularity proof"
  ∷ mkRow
    navierStokesLane
    nsH118ClayEquivalentHardOpenToken
    proofMissing
    nsStateOwner
    "NSH118VsClayGapReceipt.H11/8 reformulation is Clay-equivalent but hard open"
    "navierStokesClayPromoted"
    "H11/8 is treated as the Clay-equivalent reformulation target; the hard proof remains open"
  ∷ mkRow
    navierStokesLane
    nsSprint145ComparisonEnvelopeFailedClosedToken
    presentInternalCandidate
    nsStateOwner
    "NSSprint145ComparisonEnvelopeObstructionReceipt comparison-envelope route failed/closed"
    "navierStokesClayPromoted"
    "Sprint145 comparison-envelope evidence is a closed obstruction ledger, not a discharge"
  ∷ mkRow
    navierStokesLane
    nsMaximumLocationMigrationLemmaToken
    proofMissing
    nsStateOwner
    "MaximumLocationMigrationLemma next active Hou-Luo gate"
    "navierStokesClayPromoted"
    "Hou-Luo route now gates on maximum-location migration rather than the closed comparison envelope"
  ∷ mkRow
    navierStokesLane
    nsGlobalSmoothnessToken
    proofMissing
    nsStateOwner
    "ClayNSCurrentStateReceipt.globalSmoothRegularityProved=false"
    "navierStokesClayPromoted"
    "global smoothness remains false/open"
  ∷ []

canonicalYangMillsEvidenceRows : List EvidenceReducerRow
canonicalYangMillsEvidenceRows =
  mkRow
    yangMillsLane
    ymFiniteCarrierLayerToken
    presentInternalCandidate
    ymStateOwner
    "YMClayFinalStateReceipt.L1-L8 conditional chain scaffolded"
    "yangMillsClayPromoted"
    "finite carrier and conditional layers are evidence only"
  ∷ mkRow
    yangMillsLane
    ymWilsonActionCandidateToken
    presentInternalCandidate
    ymStateOwner
    "YMClayFinalStateReceipt.productLatticeActionRecorded=true"
    "yangMillsClayPromoted"
    "Wilson/product-lattice candidate is not an OS-positive continuum construction"
  ∷ mkRow
    yangMillsLane
    ymOSPositivityToken
    proofMissing
    gate3Owner
    "Yang-Mills OS positivity obligation"
    "yangMillsClayPromoted"
    "OS reflection positivity, BRST gauge-fixed OS3, and ghost sign issues remain open"
  ∷ mkRow
    yangMillsLane
    ymContinuumLimitToken
    proofMissing
    ymStateOwner
    "YMClayFinalStateReceipt.continuumConstructionGap"
    "yangMillsClayPromoted"
    "continuum and infinite-volume limits are not constructed"
  ∷ mkRow
    yangMillsLane
    ymWightmanTranslationToken
    translationMissing
    gate3Owner
    "Yang-Mills Wightman reconstruction obligation"
    "yangMillsClayPromoted"
    "OS/AQFT data are not translated to Wightman reconstruction"
  ∷ mkRow
    yangMillsLane
    ymPositiveMassGapToken
    proofMissing
    massShellOwner
    "CarrierEnergyToMassShellReceipt.physicalMassShellGapProvedHere=false"
    "yangMillsClayPromoted"
    "positive physical mass gap is not proved"
  ∷ mkRow
    yangMillsLane
    ymExternalAcceptanceToken
    authorityMissing
    terminalOpenOwner
    "TerminalOpenProblemStatusSurface external Clay/mass-gap authority gate"
    "yangMillsClayPromoted"
    "accepted external theorem authority is missing"
  ∷ []

canonicalTerminalEvidenceRows : List EvidenceReducerRow
canonicalTerminalEvidenceRows =
  mkRow
    terminalLane
    terminalOpenStatusToken
    presentInternalCandidate
    terminalOpenOwner
    "TerminalOpenProblemStatusSurface.terminalClaimStillBlocked=true"
    "terminalPromotion"
    "open-status surface records blockers and weak modulo claims only"
  ∷ mkRow
    terminalLane
    terminalCrossLaneConsistencyToken
    proofMissing
    smTerminalOwner
    "terminal cross-lane consistency obligation"
    "terminalPromotion"
    "all lane promotions and consistency receipts are not simultaneously discharged"
  ∷ mkRow
    terminalLane
    terminalAggregateValidationToken
    proofMissing
    smTerminalOwner
    "terminal aggregate validation obligation"
    "terminalPromotion"
    "aggregate validation over promoted lanes has not passed because the lanes remain false"
  ∷ mkRow
    terminalLane
    terminalClaimSurfaceAuditToken
    proofMissing
    smTerminalOwner
    "terminal claim-surface audit obligation"
    "terminalPromotion"
    "claim audit cannot accept terminal/full-unification while source guards are false"
  ∷ mkRow
    terminalLane
    terminalTheoremAuthorityToken
    authorityMissing
    terminalOpenOwner
    "terminal theorem/authority token"
    "terminalPromotion"
    "unqualified terminal theorem or accepted authority token is absent"
  ∷ []

canonicalEvidenceReducerRows : List EvidenceReducerRow
canonicalEvidenceReducerRows =
  canonicalGate3EvidenceRows
  ++ canonicalStandardModelEvidenceRows
  ++ canonicalNavierStokesEvidenceRows
  ++ canonicalYangMillsEvidenceRows
  ++ canonicalTerminalEvidenceRows

record Gate3StandardModelClayEvidenceReducer : Setω where
  field
    gate3ObligationReceipt :
      Gate3Clay.Gate3ClayPromotionObligationReceipt

    standardModelTerminalReceipt :
      SMT.StandardModelTerminalPromotionObligationReceipt

    gate3MoscoReceipt :
      Gate3Mosco.Gate3PrunedDensityMoscoReceipt

    gate3NoSpectralPollutionReceipt :
      Gate3NSP.Gate3NoSpectralPollutionReceipt

    massShellReceipt :
      MassShell.CarrierEnergyToMassShellReceipt

    smContentReceipt :
      SMContent.SMContentSummaryReceipt

    exactSMBlockerReceipt :
      ExactSM.ExactSMMatchBlockerReceipt

    navierStokesStateReceipt :
      NSState.ClayNSCurrentStateReceipt

    yangMillsStateReceipt :
      YMState.YMClayFinalStateReceipt

    terminalOpenStatus :
      Terminal.TerminalOpenProblemStatusSurface

    gate3Rows :
      List EvidenceReducerRow

    standardModelRows :
      List EvidenceReducerRow

    navierStokesRows :
      List EvidenceReducerRow

    yangMillsRows :
      List EvidenceReducerRow

    terminalRows :
      List EvidenceReducerRow

    allRows :
      List EvidenceReducerRow

    gate3RowCount :
      Nat

    gate3RowCountIs7 :
      gate3RowCount ≡ 7

    standardModelRowCount :
      Nat

    standardModelRowCountIs8 :
      standardModelRowCount ≡ 8

    navierStokesRowCount :
      Nat

    navierStokesRowCountIs5 :
      navierStokesRowCount ≡ 8

    yangMillsRowCount :
      Nat

    yangMillsRowCountIs7 :
      yangMillsRowCount ≡ 7

    terminalRowCount :
      Nat

    terminalRowCountIs5 :
      terminalRowCount ≡ 5

    allRowCount :
      Nat

    allRowCountIs32 :
      allRowCount ≡ 35

    presentInternalCandidateCount :
      Nat

    presentInternalCandidateCountIs8 :
      presentInternalCandidateCount ≡ 9

    authorityMissingCount :
      Nat

    authorityMissingCountIs4 :
      authorityMissingCount ≡ 4

    proofMissingCount :
      Nat

    proofMissingCountIs16 :
      proofMissingCount ≡ 18

    translationMissingCount :
      Nat

    translationMissingCountIs4 :
      translationMissingCount ≡ 4

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

    navierStokesClayPromoted :
      Bool

    navierStokesClayPromotedIsFalse :
      navierStokesClayPromoted ≡ false

    yangMillsClayPromoted :
      Bool

    yangMillsClayPromotedIsFalse :
      yangMillsClayPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    reducerPromotesAnyClaim :
      Bool

    reducerPromotesAnyClaimIsFalse :
      reducerPromotesAnyClaim ≡ false

    validationCommand :
      String

open Gate3StandardModelClayEvidenceReducer public

canonicalGate3StandardModelClayEvidenceReducer :
  Gate3StandardModelClayEvidenceReducer
canonicalGate3StandardModelClayEvidenceReducer =
  record
    { gate3ObligationReceipt =
        Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; standardModelTerminalReceipt =
        SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; gate3MoscoReceipt =
        Gate3Mosco.canonicalGate3PrunedDensityMoscoReceipt
    ; gate3NoSpectralPollutionReceipt =
        Gate3NSP.canonicalGate3NoSpectralPollutionReceipt
    ; massShellReceipt =
        MassShell.canonicalCarrierEnergyToMassShellReceipt
    ; smContentReceipt =
        SMContent.canonicalSMContentSummaryReceipt
    ; exactSMBlockerReceipt =
        ExactSM.canonicalExactSMMatchBlockerReceipt
    ; navierStokesStateReceipt =
        NSState.canonicalClayNSCurrentStateReceipt
    ; yangMillsStateReceipt =
        YMState.canonicalYMClayFinalStateReceipt
    ; terminalOpenStatus =
        Terminal.canonicalTerminalOpenProblemStatusSurface
    ; gate3Rows =
        canonicalGate3EvidenceRows
    ; standardModelRows =
        canonicalStandardModelEvidenceRows
    ; navierStokesRows =
        canonicalNavierStokesEvidenceRows
    ; yangMillsRows =
        canonicalYangMillsEvidenceRows
    ; terminalRows =
        canonicalTerminalEvidenceRows
    ; allRows =
        canonicalEvidenceReducerRows
    ; gate3RowCount =
        rowCount canonicalGate3EvidenceRows
    ; gate3RowCountIs7 =
        refl
    ; standardModelRowCount =
        rowCount canonicalStandardModelEvidenceRows
    ; standardModelRowCountIs8 =
        refl
    ; navierStokesRowCount =
        rowCount canonicalNavierStokesEvidenceRows
    ; navierStokesRowCountIs5 =
        refl
    ; yangMillsRowCount =
        rowCount canonicalYangMillsEvidenceRows
    ; yangMillsRowCountIs7 =
        refl
    ; terminalRowCount =
        rowCount canonicalTerminalEvidenceRows
    ; terminalRowCountIs5 =
        refl
    ; allRowCount =
        rowCount canonicalEvidenceReducerRows
    ; allRowCountIs32 =
        refl
    ; presentInternalCandidateCount =
        statusCount presentInternalCandidate canonicalEvidenceReducerRows
    ; presentInternalCandidateCountIs8 =
        refl
    ; authorityMissingCount =
        statusCount authorityMissing canonicalEvidenceReducerRows
    ; authorityMissingCountIs4 =
        refl
    ; proofMissingCount =
        statusCount proofMissing canonicalEvidenceReducerRows
    ; proofMissingCountIs16 =
        refl
    ; translationMissingCount =
        statusCount translationMissing canonicalEvidenceReducerRows
    ; translationMissingCountIs4 =
        refl
    ; gate3Closed =
        Gate3Clay.gate3Closed
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; gate3ClosedIsFalse =
        Gate3Clay.gate3ClosedIsFalse
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; standardModelPromoted =
        SMT.standardModelPromoted
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; standardModelPromotedIsFalse =
        SMT.standardModelPromotedIsFalse
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; navierStokesClayPromoted =
        Gate3Clay.navierStokesClayPromoted
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; navierStokesClayPromotedIsFalse =
        Gate3Clay.navierStokesClayPromotedIsFalse
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; yangMillsClayPromoted =
        Gate3Clay.yangMillsClayPromoted
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; yangMillsClayPromotedIsFalse =
        Gate3Clay.yangMillsClayPromotedIsFalse
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; terminalPromotion =
        SMT.terminalPromotion
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; terminalPromotionIsFalse =
        SMT.terminalPromotionIsFalse
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; reducerPromotesAnyClaim =
        false
    ; reducerPromotesAnyClaimIsFalse =
        refl
    ; validationCommand =
        "agda -i . DASHI/Promotion/Gate3StandardModelClayEvidenceReducer.agda"
    }

canonicalGate3ReducerRowCountIs7 :
  gate3RowCount canonicalGate3StandardModelClayEvidenceReducer ≡ 7
canonicalGate3ReducerRowCountIs7 =
  gate3RowCountIs7 canonicalGate3StandardModelClayEvidenceReducer

canonicalStandardModelReducerRowCountIs8 :
  standardModelRowCount canonicalGate3StandardModelClayEvidenceReducer ≡ 8
canonicalStandardModelReducerRowCountIs8 =
  standardModelRowCountIs8 canonicalGate3StandardModelClayEvidenceReducer

canonicalReducerRowCountIs32 :
  allRowCount canonicalGate3StandardModelClayEvidenceReducer ≡ 35
canonicalReducerRowCountIs32 =
  allRowCountIs32 canonicalGate3StandardModelClayEvidenceReducer

canonicalReducerPresentInternalCandidateCountIs8 :
  presentInternalCandidateCount canonicalGate3StandardModelClayEvidenceReducer
  ≡
  9
canonicalReducerPresentInternalCandidateCountIs8 =
  presentInternalCandidateCountIs8 canonicalGate3StandardModelClayEvidenceReducer

canonicalReducerAuthorityMissingCountIs4 :
  authorityMissingCount canonicalGate3StandardModelClayEvidenceReducer ≡ 4
canonicalReducerAuthorityMissingCountIs4 =
  authorityMissingCountIs4 canonicalGate3StandardModelClayEvidenceReducer

canonicalReducerProofMissingCountIs16 :
  proofMissingCount canonicalGate3StandardModelClayEvidenceReducer ≡ 18
canonicalReducerProofMissingCountIs16 =
  proofMissingCountIs16 canonicalGate3StandardModelClayEvidenceReducer

canonicalReducerTranslationMissingCountIs4 :
  translationMissingCount canonicalGate3StandardModelClayEvidenceReducer ≡ 4
canonicalReducerTranslationMissingCountIs4 =
  translationMissingCountIs4 canonicalGate3StandardModelClayEvidenceReducer

internalGate3EvidenceDoesNotPromoteGate3 :
  Gate3Mosco.gate3Closed
    Gate3Mosco.canonicalGate3PrunedDensityMoscoReceipt
  ≡
  false
internalGate3EvidenceDoesNotPromoteGate3 =
  Gate3Mosco.gate3ClosedIsFalse
    Gate3Mosco.canonicalGate3PrunedDensityMoscoReceipt

conditionalNoSpectralEvidenceDoesNotPromoteYMClay :
  Gate3NSP.clayYangMillsPromoted
    Gate3NSP.canonicalGate3NoSpectralPollutionReceipt
  ≡
  false
conditionalNoSpectralEvidenceDoesNotPromoteYMClay =
  Gate3NSP.clayYangMillsPromotedIsFalse
    Gate3NSP.canonicalGate3NoSpectralPollutionReceipt

massShellInternalCandidateDoesNotPromoteYMClay :
  MassShell.clayYangMillsPromoted
    MassShell.canonicalCarrierEnergyToMassShellReceipt
  ≡
  false
massShellInternalCandidateDoesNotPromoteYMClay =
  MassShell.clayYangMillsPromoted-v
    MassShell.canonicalCarrierEnergyToMassShellReceipt

smInternalCandidateDoesNotPromoteStandardModel :
  ExactSM.exactSMMatchPromoted
    ExactSM.canonicalExactSMMatchBlockerReceipt
  ≡
  false
smInternalCandidateDoesNotPromoteStandardModel =
  ExactSM.exactSMMatchPromotedIsFalse
    ExactSM.canonicalExactSMMatchBlockerReceipt

smContentCandidateDoesNotPromoteTerminal :
  SMContent.terminalClaimPromoted
    SMContent.canonicalSMContentSummaryReceipt
  ≡
  false
smContentCandidateDoesNotPromoteTerminal =
  SMContent.terminalClaimPromotedIsFalse
    SMContent.canonicalSMContentSummaryReceipt

nsInternalCandidateDoesNotPromoteClay :
  NSState.clayNavierStokesPromoted
    NSState.canonicalClayNSCurrentStateReceipt
  ≡
  false
nsInternalCandidateDoesNotPromoteClay =
  NSState.clayNavierStokesPromotedIsFalse
    NSState.canonicalClayNSCurrentStateReceipt

ymInternalCandidateDoesNotPromoteClay :
  YMState.ymClayPromotion
    YMState.canonicalYMClayFinalStateReceipt
  ≡
  false
ymInternalCandidateDoesNotPromoteClay =
  YMState.ymClayPromotionIsFalse
    YMState.canonicalYMClayFinalStateReceipt

terminalOpenStatusDoesNotPromoteTerminal :
  Terminal.terminalClaimPromoted
    Terminal.canonicalTerminalOpenProblemStatusSurface
  ≡
  false
terminalOpenStatusDoesNotPromoteTerminal =
  Terminal.terminalClaimPromoted-v
    Terminal.canonicalTerminalOpenProblemStatusSurface

reducerDoesNotPromoteGate3 :
  gate3Closed canonicalGate3StandardModelClayEvidenceReducer ≡ false
reducerDoesNotPromoteGate3 =
  gate3ClosedIsFalse canonicalGate3StandardModelClayEvidenceReducer

reducerDoesNotPromoteStandardModel :
  standardModelPromoted canonicalGate3StandardModelClayEvidenceReducer
  ≡
  false
reducerDoesNotPromoteStandardModel =
  standardModelPromotedIsFalse canonicalGate3StandardModelClayEvidenceReducer

reducerDoesNotPromoteNavierStokesClay :
  navierStokesClayPromoted canonicalGate3StandardModelClayEvidenceReducer
  ≡
  false
reducerDoesNotPromoteNavierStokesClay =
  navierStokesClayPromotedIsFalse
    canonicalGate3StandardModelClayEvidenceReducer

reducerDoesNotPromoteYangMillsClay :
  yangMillsClayPromoted canonicalGate3StandardModelClayEvidenceReducer
  ≡
  false
reducerDoesNotPromoteYangMillsClay =
  yangMillsClayPromotedIsFalse canonicalGate3StandardModelClayEvidenceReducer

reducerDoesNotPromoteTerminal :
  terminalPromotion canonicalGate3StandardModelClayEvidenceReducer ≡ false
reducerDoesNotPromoteTerminal =
  terminalPromotionIsFalse canonicalGate3StandardModelClayEvidenceReducer

reducerPromotesNoClaim :
  reducerPromotesAnyClaim canonicalGate3StandardModelClayEvidenceReducer
  ≡
  false
reducerPromotesNoClaim =
  reducerPromotesAnyClaimIsFalse canonicalGate3StandardModelClayEvidenceReducer
