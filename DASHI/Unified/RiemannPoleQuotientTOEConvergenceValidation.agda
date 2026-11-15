module DASHI.Unified.RiemannPoleQuotientTOEConvergenceValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Unified.RiemannPoleQuotientTOEConvergenceExact as TOE
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as AnalyticCore

validationTwoHighOrdinateLeaves :
  TOE.exactlyTwoTerminalAnalyticPayments ≡ true
validationTwoHighOrdinateLeaves =
  TOE.exactlyTwoTerminalAnalyticPaymentsIsTrue

validationDeterminantDoesNotPromote :
  TOE.determinantMayReplaceFinalCarrier ≡ false
validationDeterminantDoesNotPromote =
  TOE.determinantMayNotReplaceFinalCarrier

validationLowOrdinateAttachmentOpen :
  TOE.plattTrudgianTheoremImportedIntoAgda ≡ false
validationLowOrdinateAttachmentOpen =
  TOE.plattTrudgianTheoremStillNotImported

validationRHStillOpen :
  TOE.rhDerived ≡ false
validationRHStillOpen =
  TOE.rhStillOpen

validationHighOrdinateCompiler :
  (cores : AnalyticCore.FinalPoleQuotientTwoAnalyticCores) ->
  (attachments : AnalyticCore.FinalPoleQuotientAnalyticCoreAttachments cores) ->
  AnalyticCore.FinalPoleQuotientAnalyticCompletion cores attachments ->
  ⊥
validationHighOrdinateCompiler =
  TOE.highOrdinateCompletionTheorem

validationZKPFrame :
  TOE.RiemannPoleQuotientTOEZKPFrame
validationZKPFrame =
  TOE.canonicalRiemannPoleQuotientTOEZKPFrame
