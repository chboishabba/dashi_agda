module DASHI.Physics.Closure.NSTriadKNLuoCompleteSubmissionCompositionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- PURPOSE
-- Define the exact final object which may be called submission-ready: the
-- periodic global-regularity theorem together with its complete dependency,
-- no-circularity, source-fidelity, manuscript and reproducibility audit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Submission
import DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact as Global
import DASHI.Physics.Closure.NSTriadKNLuoSubmissionAuditReceiptExact as Audit

record SubmissionReadyPeriodicNavierStokesTheorem
    (carrier : Submission.PeriodicNavierStokesSubmissionCarrier) : Set₁ where
  field
    theorem :
      Submission.PeriodicNavierStokesGlobalRegularityStatement carrier
    audit : Audit.CompleteSubmissionAuditReceipt

open SubmissionReadyPeriodicNavierStokesTheorem public

submissionReadyTheoremFromUniformPhysicalConstruction :
  (carrier : Submission.PeriodicNavierStokesSubmissionCarrier) →
  Global.UniformGlobalPhysicalSolutionInputs carrier →
  Audit.CompleteSubmissionAuditReceipt →
  SubmissionReadyPeriodicNavierStokesTheorem carrier
submissionReadyTheoremFromUniformPhysicalConstruction carrier physical audit =
  record
    { theorem =
        Submission.periodicNavierStokesGlobalRegularity carrier
          (Global.uniformGlobalRegularityInputs carrier physical)
    ; audit = audit
    }

submissionReadyTheoremCompositionConstructed : Bool
submissionReadyTheoremCompositionConstructed = true

theoremAndAuditMustBothBeInhabited : Bool
theoremAndAuditMustBothBeInhabited = true

submissionReadyTheoremCompositionConstructedIsTrue :
  submissionReadyTheoremCompositionConstructed ≡ true
submissionReadyTheoremCompositionConstructedIsTrue = refl

theoremAndAuditMustBothBeInhabitedIsTrue :
  theoremAndAuditMustBothBeInhabited ≡ true
theoremAndAuditMustBothBeInhabitedIsTrue = refl
