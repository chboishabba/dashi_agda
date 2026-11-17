{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalControlledPointerInterventionResponseExact where

------------------------------------------------------------------------
-- OBS01/OBS04/OBS05: ORIGINAL NONTRIVIAL PHYSICAL-SOURCE FINITE
-- RETARDED INTERVENTION WITNESS, NOT A GENERIC IMPULSE RECORD.
--
-- Reuses the ACTUAL C^2(pointer) tensor C^2(environment)
-- norm-preserving complex controlledRecordPulse from
-- TSVF2017ControlledPointerRecordUnitaryExact.
--
-- Two original interventions at the SAME prepared pointer/environment:
-- identity pulse (c=1,s=0), and the 3/5,4/5 norm-preserving pulse.
--
-- Their early RIGHT record is exactly the same original vacuum.
-- The later WRONG record, after actual selected unitary application,
-- has a different complex overlap; difference in measured real
-- overlap is 1-3/5=2/5, not an assumed response label. Both pulses
-- conserve the entire four-complex-coordinate Born norm.
--
-- This directly advances original finite causal intervention meaning
-- and falsifies a "the micro response must vanish" reading, while
-- leaving continuous physical time, spatial locality, Kubo derivative
-- and measured 4D Lorentz principal symbol separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _-_; _/_)
open import Data.Product using (_×_; _,_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans; sym)

import DASHI.Quantum.TSVF2017ControlledPointerRecordUnitaryExact as Pulse
import DASHI.Quantum.TSVF2017HeterogeneousEnvironmentABLExact as Hetero
import DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact as Env
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact
  as C

originalIdentityPulse : Pulse.CertifiedRotation
originalIdentityPulse =
  Pulse.certifiedRotation 1ℚ 0ℚ (Ring.solve [])

originalIdentityPulsePreservesVacuum :
  Pulse.rotate originalIdentityPulse Pulse.vacuum ≡ Pulse.vacuum
originalIdentityPulsePreservesVacuum =
  cong₂ Env.pointerRecord
    (C.complexExt (Ring.solve []) (Ring.solve []))
    (C.complexExt (Ring.solve []) (Ring.solve []))

originalIdentityPulseOverlapIsOne :
  Hetero.siteOverlap (Pulse.emittedEnvironmentSite originalIdentityPulse)
    ≡ C.oneC
originalIdentityPulseOverlapIsOne =
  trans
    (cong (λ v → Env.hermitianPair Pulse.vacuum v)
      originalIdentityPulsePreservesVacuum)
    (C.complexExt (Ring.solve []) (Ring.solve []))

-- Exact "unchanged earlier record" from the actual two controlled
-- unitary interventions; no state postselection changes that record.
originalEarlyRecordUnchangedByLaterPulse :
  Hetero.rightRecord
    (Pulse.emittedEnvironmentSite originalIdentityPulse)
  ≡ Hetero.rightRecord
    (Pulse.emittedEnvironmentSite Pulse.threeFourPulse)
originalEarlyRecordUnchangedByLaterPulse =
  trans
    (Pulse.rightEmissionIsOriginalVacuum originalIdentityPulse)
    (sym (Pulse.rightEmissionIsOriginalVacuum Pulse.threeFourPulse))

-- A genuine NONZERO later influence on the same original readout.
-- This is the physical-source finite pulse amplitude response, not
-- a separate abstract Kubo Green function or arbitrary Gamma rate.
originalLaterOverlapRealResponseIsTwoFifths :
  C.re
    (Hetero.siteOverlap
      (Pulse.emittedEnvironmentSite originalIdentityPulse))
  -
  C.re
    (Hetero.siteOverlap
      (Pulse.emittedEnvironmentSite Pulse.threeFourPulse))
  ≡ + 2 / 5
originalLaterOverlapRealResponseIsTwoFifths =
  trans
    (cong₂ _-_
      (cong C.re originalIdentityPulseOverlapIsOne)
      (cong C.re Pulse.threeFourPulseOverlap))
    (Ring.solve [])

originalBothSelectedInterventionsConserveTotalNorm :
  (Pulse.pointerEnvironmentNorm
    (Pulse.controlledRecordPulse originalIdentityPulse
      Pulse.preparedPointerEnvironment)
    ≡ Pulse.pointerEnvironmentNorm Pulse.preparedPointerEnvironment)
  ×
  (Pulse.pointerEnvironmentNorm
    (Pulse.controlledRecordPulse Pulse.threeFourPulse
      Pulse.preparedPointerEnvironment)
    ≡ Pulse.pointerEnvironmentNorm Pulse.preparedPointerEnvironment)
originalBothSelectedInterventionsConserveTotalNorm =
  (Pulse.controlledRecordPreservesFullBornNorm
      originalIdentityPulse Pulse.preparedPointerEnvironment)
  ,
  (Pulse.controlledRecordPreservesFullBornNorm
      Pulse.threeFourPulse Pulse.preparedPointerEnvironment)

-- This concrete source witnesses finite earlier/later intervention
-- separation and norm conservation; source's Time remains Unit in
-- TSVF2017OriginalComplexABLSelectedExact. It cannot yield a
-- physically measured 4D Kubo cone or continuum with no new dynamics.
