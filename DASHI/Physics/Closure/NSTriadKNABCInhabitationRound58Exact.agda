module DASHI.Physics.Closure.NSTriadKNABCInhabitationRound58Exact where

------------------------------------------------------------------------
-- ROUND 58/60 — one typed boundary for the three quantitative gates.
--
-- Round 60 sharpens A: the package no longer accepts an independently supplied
-- transfer plus an equality claiming that it came from the physical source.
-- It accepts only the canonical physical source and estimates indexed by that
-- source; the transfer is constructed definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNHHBadDyadicThreeMechanismRecurrenceRound48Exact as A
import DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadLiteralDuhamelAdapterRound58Exact as AAdapter
import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalDuhamelSourceRound59 as ASource
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceAdapterRound58 as BSource
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as CHeadroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftUniformProductCapacityRound57Exact as C
import DASHI.Physics.Closure.NSTriadKNFixedShiftPhysicalCapacityAdapterRound58 as CSource
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine

record LiteralABCSourceWitnesses : Set₁ where
  field
    hhBadPhysicalSource : ASource.PhysicalLocalizedDuhamelSource
    hhBadPhysicalEstimates :
      ASource.PhysicalLocalizedDuhamelEstimates hhBadPhysicalSource

    comSource : BSource.PhysicalNormalizedOddPQSource

    fixedShiftSource : CSource.PhysicalFixedShiftSource

open LiteralABCSourceWitnesses public

literalHHBadTransfer :
  (source : LiteralABCSourceWitnesses) →
  A.PhysicalDyadicThreeMechanismTransfer
literalHHBadTransfer source =
  ASource.physicalTransferFromSource
    (hhBadPhysicalSource source)
    (hhBadPhysicalEstimates source)

-- A: source-indexed estimates produce the exact source transfer and then the
-- raw-variable Duhamel consumer.  There is no same-object equality left to
-- postulate separately.
literalHHBadDuhamel :
  (source : LiteralABCSourceWitnesses) →
  Raw.PhysicalGeneralVariableDefectDuhamel
literalHHBadDuhamel source =
  AAdapter.asLiteralDuhamel (literalHHBadTransfer source)

-- B: the common-hat and normalized same/adjacent estimates feed the existing
-- width-one reduction.  Round60 also exposes the direct 133/256 aggregate in
-- NSTriadKNComNormalizedFibreAggregateRound60Exact.
literalComEnvelope :
  (source : LiteralABCSourceWitnesses) →
  Support.PhysicalComSupportOverlapEnvelope
literalComEnvelope source =
  BSource.legacyEnvelope (comSource source)

-- C: the division-free uniform product capacity feeds the complete additive
-- correction headroom theorem.
literalFixedShiftHeadroom :
  (source : LiteralABCSourceWitnesses) →
  ∀ n →
  Round53.ownerAggregateDataRemainder
      (CSource.balances (fixedShiftSource source) n)
    + C.uniformCoefficient
        (CSource.uniformProductCapacity (fixedShiftSource source))
      * Owner.integralCritical
          (Nine.environment
            (CSource.balances (fixedShiftSource source) n))
    ≤ CHeadroom.fixedShiftCorrectionHeadroom
        (CSource.fixedBlock (fixedShiftSource source)) n
literalFixedShiftHeadroom source =
  C.uniformCoefficientPlusDataFitsFullCorrectionHeadroom
    (CSource.uniformProductCapacity (fixedShiftSource source))

abcSourceBoundaryIsTyped : Bool
abcSourceBoundaryIsTyped = true

abcSourceBoundaryIsTypedIsTrue : abcSourceBoundaryIsTyped ≡ true
abcSourceBoundaryIsTypedIsTrue = refl

-- Fail closed: these are still the actual A/B/C physical analytic witnesses.
literalABCSourceWitnessesConstructed : Bool
literalABCSourceWitnessesConstructed = false
