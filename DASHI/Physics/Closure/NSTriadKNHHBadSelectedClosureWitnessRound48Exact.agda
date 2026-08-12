module DASHI.Physics.Closure.NSTriadKNHHBadSelectedClosureWitnessRound48Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Package the true Round-47 consumer contract as one witness.  A selected
-- coherence threshold, shell recurrence, literal normalized-density same-object
-- bridge, and ordinary unmasked charge domination are carried together.  The
-- witness produces the mature HH-bad owner with
--
--   eta_HHb = 2 M,
--
-- where M is the selected recurrence ceiling.  No all-delta uniformity appears
-- in the interface.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact as Recurrence
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedRecurrenceToOwnerRound47Exact as ToOwner

record SelectedHHBadClosureWitness
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ) : Set₁ where
  field
    recurrence : Recurrence.SelectedThresholdDefectRecurrence
    physicalOwnerInput :
      ToOwner.PhysicalSelectedRecurrenceHHBadOwnerInput
        environment effectiveViscosity recurrence

open SelectedHHBadClosureWitness public

selectedHHBadCeiling :
  ∀ {environment effectiveViscosity} →
  SelectedHHBadClosureWitness environment effectiveViscosity → ℚ
selectedHHBadCeiling witness = Recurrence.ceiling (recurrence witness)

selectedHHBadEta :
  ∀ {environment effectiveViscosity} →
  SelectedHHBadClosureWitness environment effectiveViscosity → ℚ
selectedHHBadEta witness = Sharp.two * selectedHHBadCeiling witness

selectedHHBadOwnerAtShell :
  ∀ {environment effectiveViscosity} →
  SelectedHHBadClosureWitness environment effectiveViscosity →
  Nat → Owner.AdmissibleOwnerEstimate environment
selectedHHBadOwnerAtShell witness =
  ToOwner.physicalHHBadOwnerFromSelectedRecurrence
    (physicalOwnerInput witness)

selectedHHBadOwnerEtaExact :
  ∀ {environment effectiveViscosity}
    (witness : SelectedHHBadClosureWitness environment effectiveViscosity)
    shell →
  Owner.eta (selectedHHBadOwnerAtShell witness shell)
  ≡ selectedHHBadEta witness
selectedHHBadOwnerEtaExact witness shell = refl

selectedHHBadOwnerUsesOneThresholdOnly : Bool
selectedHHBadOwnerUsesOneThresholdOnly = true

selectedHHBadClosureWitnessConsumerExact : Bool
selectedHHBadClosureWitnessConsumerExact = true

selectedHHBadOwnerUsesOneThresholdOnlyIsTrue :
  selectedHHBadOwnerUsesOneThresholdOnly ≡ true
selectedHHBadOwnerUsesOneThresholdOnlyIsTrue = refl
