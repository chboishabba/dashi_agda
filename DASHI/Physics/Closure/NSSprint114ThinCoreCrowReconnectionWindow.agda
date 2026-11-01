module DASHI.Physics.Closure.NSSprint114ThinCoreCrowReconnectionWindow where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint112ThickCoreCrowDominanceRegime
  as Sprint112
import DASHI.Physics.Closure.NSSprint113CrowPersistenceUnderNSEvolution
  as Sprint113

------------------------------------------------------------------------
-- Sprint 114 thin-core Crow reconnection-window correction.
--
-- This receipt replaces the Sprint112 thick-core condition with the
-- thin-core Crow-dominant comparison regime.  It closes the correction
-- ledger and the elliptic backreaction comparison bound, but it records
-- the live blocker as the ReconnectionWindowLowerBound / finite flux
-- surplus obligation.  No Clay Navier-Stokes promotion is made here.

sprint114ThinCoreCorrectionLedgerClosed : Bool
sprint114ThinCoreCorrectionLedgerClosed = true

sprint112ThickCoreConditionCorrected : Bool
sprint112ThickCoreConditionCorrected = true

thinCoreCrowDominanceRegimeClosed : Bool
thinCoreCrowDominanceRegimeClosed = true

ellipticBackreactionBoundClosed : Bool
ellipticBackreactionBoundClosed = true

reconnectionWindowLowerBoundClosed : Bool
reconnectionWindowLowerBoundClosed = false

viscousDecayWindowClosed : Bool
viscousDecayWindowClosed = false

nonlinearDeformationControlClosed : Bool
nonlinearDeformationControlClosed = false

positiveFluxAccumulationWindowClosed : Bool
positiveFluxAccumulationWindowClosed = false

finiteTimeFluxSurplusFromCrowDominance : Bool
finiteTimeFluxSurplusFromCrowDominance = false

finiteKStarCollapseClosed : Bool
finiteKStarCollapseClosed = false

strainCompressionAtHighFrequencyConcentrationPointsClosed : Bool
strainCompressionAtHighFrequencyConcentrationPointsClosed = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

record ImportedPriorReceipts : Set where
  constructor importedPriorReceiptsReceipt
  field
    sprint113Receipt :
      Sprint113.NSSprint113CrowPersistenceUnderNSEvolution
    sprint113ReceiptIsCanonical :
      sprint113Receipt
      ≡ Sprint113.canonicalNSSprint113CrowPersistenceUnderNSEvolution
    sprint113LedgerClosed :
      Sprint113.crowPersistenceUnderNSEvolutionLedgerClosed ≡ true
    sprint113FluxSurplusStillFalse :
      Sprint113.FiniteTimeFluxSurplusFromCrowDominance ≡ false
    sprint113ClayPromotionStillFalse :
      Sprint113.clayNavierStokesPromoted ≡ false
    sprint112Receipt :
      Sprint112.NSSprint112ThickCoreCrowDominanceRegime
    sprint112ReceiptIsCanonical :
      sprint112Receipt
      ≡ Sprint112.canonicalNSSprint112ThickCoreCrowDominanceRegime
    sprint112ThickCoreAnchorReplacedHere :
      sprint112ThickCoreConditionCorrected ≡ true
    importScope :
      String

open ImportedPriorReceipts public

canonicalImportedPriorReceipts : ImportedPriorReceipts
canonicalImportedPriorReceipts =
  importedPriorReceiptsReceipt
    Sprint113.canonicalNSSprint113CrowPersistenceUnderNSEvolution
    refl
    refl
    refl
    refl
    Sprint112.canonicalNSSprint112ThickCoreCrowDominanceRegime
    refl
    refl
    "Sprint113 is the active upstream ledger; Sprint112 is imported only to mark that its thick-core condition is replaced by the Sprint114 thin-core regime."

record ThinCoreCrowRegimeCorrection : Set where
  constructor thinCoreCrowRegimeCorrectionReceipt
  field
    thinCoreRange :
      String
    correctedSprint112Condition :
      sprint112ThickCoreConditionCorrected ≡ true
    thinCoreRegimeClosed :
      thinCoreCrowDominanceRegimeClosed ≡ true
    crowReconnectionTime :
      String
    crowGrowthTime :
      String
    regimeStatement :
      String

open ThinCoreCrowRegimeCorrection public

canonicalThinCoreCrowRegimeCorrection :
  ThinCoreCrowRegimeCorrection
canonicalThinCoreCrowRegimeCorrection =
  thinCoreCrowRegimeCorrectionReceipt
    "delta / b in (0, 0.4825)"
    refl
    refl
    "T_reconnect ~ b^2 / Gamma"
    "T_grow ~ 7.9 * b^2 / Gamma"
    "The Sprint114 correction uses the thin-core Crow-dominant regime in place of the Sprint112 thick-core condition."

record EllipticBackreactionComparisonBound : Set where
  constructor ellipticBackreactionComparisonBoundReceipt
  field
    comparisonBound :
      String
    boundClosed :
      ellipticBackreactionBoundClosed ≡ true
    comparisonScope :
      String

open EllipticBackreactionComparisonBound public

canonicalEllipticBackreactionComparisonBound :
  EllipticBackreactionComparisonBound
canonicalEllipticBackreactionComparisonBound =
  ellipticBackreactionComparisonBoundReceipt
    "|Pi_elliptic(t)| <= C * (delta / b)^4 * |Pi_Crow(t)|"
    refl
    "Elliptic backreaction is bounded at the rate-comparison and ledger level only."

record ReconnectionWindowBlocker : Set where
  constructor reconnectionWindowBlockerReceipt
  field
    lowerBoundClosed :
      reconnectionWindowLowerBoundClosed ≡ false
    positiveFluxWindowClosed :
      positiveFluxAccumulationWindowClosed ≡ false
    fluxSurplusClosed :
      finiteTimeFluxSurplusFromCrowDominance ≡ false
    requiredFluxIntegral :
      String
    blockerStatement :
      String

open ReconnectionWindowBlocker public

canonicalReconnectionWindowBlocker : ReconnectionWindowBlocker
canonicalReconnectionWindowBlocker =
  reconnectionWindowBlockerReceipt
    refl
    refl
    refl
    "integral_0_to_T_reconnect Pi_HH_to_L(t) dt"
    "The live blocker is ReconnectionWindowLowerBound / finite flux surplus."

record Sprint114GateStatuses : Set where
  constructor sprint114GateStatusesReceipt
  field
    ledgerClosedField :
      sprint114ThinCoreCorrectionLedgerClosed ≡ true
    sprint112CorrectionField :
      sprint112ThickCoreConditionCorrected ≡ true
    thinCoreRegimeField :
      thinCoreCrowDominanceRegimeClosed ≡ true
    ellipticBackreactionField :
      ellipticBackreactionBoundClosed ≡ true
    reconnectionWindowLowerBoundField :
      reconnectionWindowLowerBoundClosed ≡ false
    viscousDecayWindowField :
      viscousDecayWindowClosed ≡ false
    nonlinearDeformationControlField :
      nonlinearDeformationControlClosed ≡ false
    positiveFluxAccumulationWindowField :
      positiveFluxAccumulationWindowClosed ≡ false
    finiteFluxSurplusField :
      finiteTimeFluxSurplusFromCrowDominance ≡ false
    finiteKStarCollapseField :
      finiteKStarCollapseClosed ≡ false
    strainCompressionField :
      strainCompressionAtHighFrequencyConcentrationPointsClosed ≡ false
    clayNavierStokesPromotedField :
      clayNavierStokesPromoted ≡ false
    statusScope :
      String

open Sprint114GateStatuses public

canonicalSprint114GateStatuses : Sprint114GateStatuses
canonicalSprint114GateStatuses =
  sprint114GateStatusesReceipt
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
    "Sprint114 closes the corrected thin-core ledger and elliptic comparison bound while leaving the reconnection lower bound, finite flux surplus, and downstream gates false."

canonicalSprint114ThinCoreCorrectionFlags :
  (sprint114ThinCoreCorrectionLedgerClosed ≡ true)
  × (sprint112ThickCoreConditionCorrected ≡ true)
  × (thinCoreCrowDominanceRegimeClosed ≡ true)
  × (ellipticBackreactionBoundClosed ≡ true)
  × (reconnectionWindowLowerBoundClosed ≡ false)
  × (viscousDecayWindowClosed ≡ false)
  × (nonlinearDeformationControlClosed ≡ false)
  × (positiveFluxAccumulationWindowClosed ≡ false)
  × (finiteTimeFluxSurplusFromCrowDominance ≡ false)
  × (finiteKStarCollapseClosed ≡ false)
  × (strainCompressionAtHighFrequencyConcentrationPointsClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
canonicalSprint114ThinCoreCorrectionFlags =
  refl , refl , refl , refl , refl , refl , refl , refl , refl , refl ,
  refl , refl

record NSSprint114ThinCoreCrowReconnectionWindow : Set where
  constructor nsSprint114ThinCoreCrowReconnectionWindowReceipt
  field
    importedPriorReceipts :
      ImportedPriorReceipts
    importedPriorReceiptsAreCanonical :
      importedPriorReceipts ≡ canonicalImportedPriorReceipts
    thinCoreCrowRegimeCorrection :
      ThinCoreCrowRegimeCorrection
    thinCoreCrowRegimeCorrectionIsCanonical :
      thinCoreCrowRegimeCorrection
      ≡ canonicalThinCoreCrowRegimeCorrection
    ellipticBackreactionComparisonBound :
      EllipticBackreactionComparisonBound
    ellipticBackreactionComparisonBoundIsCanonical :
      ellipticBackreactionComparisonBound
      ≡ canonicalEllipticBackreactionComparisonBound
    reconnectionWindowBlocker :
      ReconnectionWindowBlocker
    reconnectionWindowBlockerIsCanonical :
      reconnectionWindowBlocker
      ≡ canonicalReconnectionWindowBlocker
    sprint114GateStatuses :
      Sprint114GateStatuses
    sprint114GateStatusesAreCanonical :
      sprint114GateStatuses ≡ canonicalSprint114GateStatuses
    flags :
      (sprint114ThinCoreCorrectionLedgerClosed ≡ true)
      × (sprint112ThickCoreConditionCorrected ≡ true)
      × (thinCoreCrowDominanceRegimeClosed ≡ true)
      × (ellipticBackreactionBoundClosed ≡ true)
      × (reconnectionWindowLowerBoundClosed ≡ false)
      × (viscousDecayWindowClosed ≡ false)
      × (nonlinearDeformationControlClosed ≡ false)
      × (positiveFluxAccumulationWindowClosed ≡ false)
      × (finiteTimeFluxSurplusFromCrowDominance ≡ false)
      × (finiteKStarCollapseClosed ≡ false)
      × (strainCompressionAtHighFrequencyConcentrationPointsClosed ≡ false)
      × (clayNavierStokesPromoted ≡ false)
    nonPromotionBoundary :
      String

open NSSprint114ThinCoreCrowReconnectionWindow public

canonicalNSSprint114ThinCoreCrowReconnectionWindow :
  NSSprint114ThinCoreCrowReconnectionWindow
canonicalNSSprint114ThinCoreCrowReconnectionWindow =
  nsSprint114ThinCoreCrowReconnectionWindowReceipt
    canonicalImportedPriorReceipts
    refl
    canonicalThinCoreCrowRegimeCorrection
    refl
    canonicalEllipticBackreactionComparisonBound
    refl
    canonicalReconnectionWindowBlocker
    refl
    canonicalSprint114GateStatuses
    refl
    canonicalSprint114ThinCoreCorrectionFlags
    "Clay Navier-Stokes remains unpromoted because ReconnectionWindowLowerBound / finite flux surplus and downstream analytic gates remain false."

canonicalNSSprint114ThinCoreCrowReconnectionWindowReceipt :
  NSSprint114ThinCoreCrowReconnectionWindow
canonicalNSSprint114ThinCoreCrowReconnectionWindowReceipt =
  canonicalNSSprint114ThinCoreCrowReconnectionWindow

canonicalThinCoreCrowReconnectionWindowReceipt :
  NSSprint114ThinCoreCrowReconnectionWindow
canonicalThinCoreCrowReconnectionWindowReceipt =
  canonicalNSSprint114ThinCoreCrowReconnectionWindow
