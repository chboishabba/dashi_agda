module DASHI.Physics.Closure.NSTriadKNABCInhabitationRound58Exact where

------------------------------------------------------------------------
-- ROUND 58 — one typed boundary for the three quantitative gates.
--
-- This module deliberately contains no new postulate and no Boolean upgrade.
-- It makes the remaining source data compositional: one A witness supplies the
-- literal Duhamel object, one B witness supplies the common-hat Gram bounds,
-- and one C witness supplies the same-object fixed-shift capacity.  All three
-- downstream consumers can therefore be checked against one package without
-- silently mixing independently named objects.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNHHBadDyadicThreeMechanismRecurrenceRound48Exact as A
import DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadLiteralDuhamelAdapterRound58Exact as AAdapter
import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as B
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as CHeadroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftUniformProductCapacityRound57Exact as C
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

record LiteralABCSourceWitnesses : Set₁ where
  field
    hhBadTransfer : A.PhysicalDyadicThreeMechanismTransfer

    comSkeleton : B.PhysicalOddPQSupportSkeleton
    comHatIdentification :
      B.PhysicalOddPQHatIdentification comSkeleton
    comNormalizedGramBounds :
      B.SameAdjacentPhysicalComBounds
        comSkeleton comHatIdentification

    balances : Nat → Nine.NineOwnerCriticalBalance
    fixedShiftData : Fixed.FixedShiftRecursionPhysicalData
    fixedBlock : Block.RationalFixedBlockDecay
    ownerBlockIdentification :
      CHeadroom.PhysicalOwnerBlockCorrectionIdentification
        balances fixedShiftData fixedBlock
    uniformProductCapacity :
      C.UniformFixedShiftProductCapacity ownerBlockIdentification

open LiteralABCSourceWitnesses public

-- A: the exact source transfer is now available at the raw-variable consumer.
literalHHBadDuhamel :
  (source : LiteralABCSourceWitnesses) →
  Raw.PhysicalGeneralVariableDefectDuhamel
literalHHBadDuhamel source =
  AAdapter.asLiteralDuhamel (hhBadTransfer source)

-- B: the common-hat and normalized same/adjacent estimates feed the existing
-- width-one reduction and its exact 133/256 arithmetic.
literalComEnvelope :
  (source : LiteralABCSourceWitnesses) →
  Support.PhysicalComSupportOverlapEnvelope
literalComEnvelope source =
  B.physicalComEnvelopeFromSameAdjacent
    (comHatIdentification source)
    (comNormalizedGramBounds source)

-- C: the division-free uniform product capacity feeds the complete additive
-- correction headroom theorem.
literalFixedShiftHeadroom :
  (source : LiteralABCSourceWitnesses) →
  ∀ n →
  Round53.ownerAggregateDataRemainder (balances source n)
    + C.uniformCoefficient (uniformProductCapacity source)
      * Owner.integralCritical
          (Nine.environment (balances source n))
    ≤ CHeadroom.fixedShiftCorrectionHeadroom (fixedBlock source) n
literalFixedShiftHeadroom source =
  C.uniformCoefficientPlusDataFitsFullCorrectionHeadroom
    (uniformProductCapacity source)

abcSourceBoundaryIsTyped : Bool
abcSourceBoundaryIsTyped = true

abcSourceBoundaryIsTypedIsTrue : abcSourceBoundaryIsTyped ≡ true
abcSourceBoundaryIsTypedIsTrue = refl

-- The package is intentionally not claimed to exist: its three fields are the
-- actual A–C analytic frontier, not aliases for sampled evidence.
literalABCSourceWitnessesConstructed : Bool
literalABCSourceWitnessesConstructed = false
