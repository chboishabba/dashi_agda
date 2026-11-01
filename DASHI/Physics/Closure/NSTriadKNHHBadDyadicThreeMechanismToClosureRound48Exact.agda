module DASHI.Physics.Closure.NSTriadKNHHBadDyadicThreeMechanismToClosureRound48Exact where

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
-- Compose the actual Round-48 HH-bad research surface all the way to the
-- mature owner.  The packet owns the selected-threshold three-mechanism shell
-- transport together with the Round-47 same-object density/charge producer on
-- the definitionally identical recurrence.  Therefore the dyadic 1/2,
-- recurrence induction, inverse-shell certificate and owner eta = 2M are all
-- derived internally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicThreeMechanismRecurrenceRound48Exact as Three
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedRecurrenceToOwnerRound47Exact as ToOwner
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedClosureWitnessRound48Exact as Closure

record PhysicalDyadicSelectedHHBadClosurePacket
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ) : Set₁ where
  field
    transfer : Three.PhysicalDyadicThreeMechanismTransfer
    physicalOwnerInput :
      ToOwner.PhysicalSelectedRecurrenceHHBadOwnerInput
        environment effectiveViscosity
        (Three.asSelectedThresholdDefectRecurrence transfer)

open PhysicalDyadicSelectedHHBadClosurePacket public

physicalDyadicSelectedClosureWitness :
  ∀ {environment effectiveViscosity} →
  PhysicalDyadicSelectedHHBadClosurePacket environment effectiveViscosity →
  Closure.SelectedHHBadClosureWitness environment effectiveViscosity
physicalDyadicSelectedClosureWitness input = record
  { recurrence =
      Three.asSelectedThresholdDefectRecurrence (transfer input)
  ; physicalOwnerInput = physicalOwnerInput input
  }

physicalDyadicSelectedHHBadOwner :
  ∀ {environment effectiveViscosity} →
  PhysicalDyadicSelectedHHBadClosurePacket environment effectiveViscosity →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalDyadicSelectedHHBadOwner input =
  Closure.selectedHHBadOwnerAtShell
    (physicalDyadicSelectedClosureWitness input)

hhBadThreeMechanismToMatureOwnerClosed : Bool
hhBadThreeMechanismToMatureOwnerClosed = true

physicalHHBadThreeMechanismProducerConstructed : Bool
physicalHHBadThreeMechanismProducerConstructed = false

hhBadThreeMechanismToMatureOwnerClosedIsTrue :
  hhBadThreeMechanismToMatureOwnerClosed ≡ true
hhBadThreeMechanismToMatureOwnerClosedIsTrue = refl

physicalHHBadThreeMechanismProducerConstructedIsFalse :
  physicalHHBadThreeMechanismProducerConstructed ≡ false
physicalHHBadThreeMechanismProducerConstructedIsFalse = refl
