module DASHI.Papers.CoreTheoremInterfaces where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Papers.NavierStokes.TheoremInterface as NS
import DASHI.Papers.YangMills.TheoremInterface as YM
import DASHI.Papers.Unification.TheoremInterface as U
import DASHI.Physics.Closure.NSFinalStateReceipt as NSFinal
import DASHI.Physics.Closure.YMFinalStateReceipt as YMFinal

------------------------------------------------------------------------
-- Checked aggregate over the paper-facing theorem interfaces.
--
-- This module is deliberately conservative: it gathers the currently checked
-- paper theorem interfaces and records only their fail-closed Clay/terminal
-- boundaries.  It does not assert any Clay solution, physical terminal claim,
-- or terminal unification promotion beyond the imported interfaces.

data CoreTheoremAggregateStatus : Set where
  importedPaperInterfacesAssembled_terminalClaimsFalse :
    CoreTheoremAggregateStatus

coreTheoremInterfacesStatement : String
coreTheoremInterfacesStatement =
  "Checked aggregate for NS, YM, and Unification paper theorem interfaces; canonical interface records are imported and all Clay or terminal promotion flags remain false."

record CoreTheoremInterfaces : Setω where
  field
    status :
      CoreTheoremAggregateStatus

    statusIsCanonical :
      status ≡ importedPaperInterfacesAssembled_terminalClaimsFalse

    navierStokesInterface :
      NS.NSPaperTheoremStatus

    navierStokesClayStillFalse :
      NSFinal.clayNavierStokesPromoted
        (NS.finalStateReceipt navierStokesInterface)
      ≡
      false

    navierStokesTerminalStillFalse :
      NS.clayTerminalPromotion navierStokesInterface ≡ false

    yangMillsInterface :
      YM.YangMillsPaperTheoremInterface

    yangMillsClayStillFalse :
      YMFinal.clayYangMillsPromoted
        (YM.finalStateReceipt yangMillsInterface)
      ≡
      false

    yangMillsTerminalStillFalse :
      YM.paperClayTerminalPromoted yangMillsInterface ≡ false

    unificationInterface :
      U.UnificationPaperTheoremInterface

    unificationTerminalStillFalse :
      U.terminalUnificationPromoted unificationInterface ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ coreTheoremInterfacesStatement

open CoreTheoremInterfaces public

canonicalCoreTheoremInterfaces : CoreTheoremInterfaces
canonicalCoreTheoremInterfaces =
  record
    { status =
        importedPaperInterfacesAssembled_terminalClaimsFalse
    ; statusIsCanonical =
        refl
    ; navierStokesInterface =
        NS.canonicalNSPaperTheoremStatus
    ; navierStokesClayStillFalse =
        NS.nsPaperInterfaceClayFalse
    ; navierStokesTerminalStillFalse =
        NS.nsPaperInterfaceTerminalFalse
    ; yangMillsInterface =
        YM.canonicalYangMillsPaperTheoremInterface
    ; yangMillsClayStillFalse =
        YM.paperInterfaceFinalClayFalse
    ; yangMillsTerminalStillFalse =
        YM.paperInterfaceClayTerminalFalse
    ; unificationInterface =
        U.canonicalUnificationPaperTheoremInterface
    ; unificationTerminalStillFalse =
        U.unificationPaperInterfaceTerminalFalse
    ; statement =
        coreTheoremInterfacesStatement
    ; statementIsCanonical =
        refl
    }

coreNavierStokesTerminalFalse :
  NS.clayTerminalPromotion
    (navierStokesInterface canonicalCoreTheoremInterfaces)
  ≡ false
coreNavierStokesTerminalFalse =
  NS.nsPaperInterfaceTerminalFalse

coreYangMillsTerminalFalse :
  YM.paperClayTerminalPromoted
    (yangMillsInterface canonicalCoreTheoremInterfaces)
  ≡ false
coreYangMillsTerminalFalse =
  YM.paperInterfaceClayTerminalFalse

coreUnificationTerminalFalse :
  U.terminalUnificationPromoted
    (unificationInterface canonicalCoreTheoremInterfaces)
  ≡ false
coreUnificationTerminalFalse =
  U.unificationPaperInterfaceTerminalFalse
