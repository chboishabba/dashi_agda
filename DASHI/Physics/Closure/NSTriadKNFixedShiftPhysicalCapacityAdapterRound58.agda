module DASHI.Physics.Closure.NSTriadKNFixedShiftPhysicalCapacityAdapterRound58 where

------------------------------------------------------------------------
-- Round 58/60 C adapter.
--
-- Same-object owner/flux/block transport remains separate from the analytic
-- capacity calculation.  Round60 adds a second constructor: scale-matched
-- physical bounds plus one rational coefficient inequality construct the
-- division-free all-block capacity automatically.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_) 

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNCanonicalOwnerFluxCorrectionRound55Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Separation
import DASHI.Physics.Closure.NSTriadKNFixedShiftPhysicalCapacityLeafRound58 as Leaf
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftUniformProductCapacityRound57Exact as Capacity
import DASHI.Physics.Closure.NSTriadKNFixedShiftScaleMatchedCapacityRound60Exact as ScaleCapacity

record PhysicalBlockCorrectionData
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    (core : Canonical.CanonicalOwnerDrivenFixedShift balances)
    (block : Block.RationalFixedBlockDecay) : Set₁ where
  field
    physicalFluxCorrectionIsBlockCorrection : ∀ n →
      Fixed.integratedFluxCorrection
        (Canonical.asPhysicalFixedShiftData core) n
      ≡ Block.correction block n

    blockShiftCoefficientIsPhysical :
      Block.q block
        ≡ Fixed.correctedShiftCoefficient
          (Canonical.asPhysicalFixedShiftData core)

open PhysicalBlockCorrectionData public

record PhysicalFixedShiftSource : Set₁ where
  field
    balances : Nat → Nine.NineOwnerCriticalBalance
    fixedShiftData : Fixed.FixedShiftRecursionPhysicalData
    fixedBlock : Block.RationalFixedBlockDecay
    ownerBlockIdentification :
      Headroom.PhysicalOwnerBlockCorrectionIdentification
        balances fixedShiftData fixedBlock
    uniformProductCapacity :
      Capacity.UniformFixedShiftProductCapacity ownerBlockIdentification

open PhysicalFixedShiftSource public

physicalFixedShiftSourceFromScaleMatched :
  ∀ {balances data block}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances data block) →
  ScaleCapacity.ScaleMatchedFixedShiftCapacityData identification →
  PhysicalFixedShiftSource
physicalFixedShiftSourceFromScaleMatched
    {balances} {data} {block} identification scaleData = record
  { balances = balances
  ; fixedShiftData = data
  ; fixedBlock = block
  ; ownerBlockIdentification = identification
  ; uniformProductCapacity =
      ScaleCapacity.scaleMatchedUniformProductCapacity scaleData
  }

ownerFluxBlockIdentification :
  ∀ {balances}
    {core : Canonical.CanonicalOwnerDrivenFixedShift balances}
    {block : Block.RationalFixedBlockDecay} →
  PhysicalBlockCorrectionData core block →
  Leaf.PhysicalOwnerFluxBlockIdentification
ownerFluxBlockIdentification
    {balances} {core} {block} physical =
  record
    { ownerRemainder = λ n → Nine.admissibleRemainder (balances n)
    ; integratedFluxCorrection =
        Fixed.integratedFluxCorrection
          (Canonical.asPhysicalFixedShiftData core)
    ; blockCorrection = Block.correction block
    ; blockShiftCoefficient = Block.q block
    ; correctedShiftCoefficient =
        Fixed.correctedShiftCoefficient
          (Canonical.asPhysicalFixedShiftData core)
    ; ownerToFlux = λ n →
        Separation.ownerRemainderIsFluxCorrection
          (Canonical.canonicalOwnerToFluxSameObject core) n
    ; physicalFluxCorrectionIsBlockCorrection =
        physicalFluxCorrectionIsBlockCorrection physical
    ; blockShiftCoefficientIsPhysical =
        blockShiftCoefficientIsPhysical physical
    }

-- The generic leaf's capacity record is deliberately the final argument.  A
-- concrete B_* can be supplied without changing any of the owner identities.
attachUniformCapacity :
  ∀ {integralCritical correctionHeadroom dataRemainder}
    (capacity : Leaf.UniformFixedShiftProductCapacity
      integralCritical correctionHeadroom dataRemainder) →
  Leaf.UniformFixedShiftProductCapacity
    integralCritical correctionHeadroom dataRemainder
attachUniformCapacity capacity = capacity

ownerAggregateDataRemainder :
  Nine.NineOwnerCriticalBalance → ℚ
ownerAggregateDataRemainder balance =
  Owner.sumDataRemainder
    (Owner.nineOwnerList (Nine.family balance))

ownerAggregateCriticalCoefficient :
  Nine.NineOwnerCriticalBalance → ℚ
ownerAggregateCriticalCoefficient balance =
  Owner.sumCriticalCoefficient
    (Owner.nineOwnerList (Nine.family balance))

ownerAggregateFormula :
  ∀ balance →
  Nine.admissibleRemainder balance
  ≡ ownerAggregateDataRemainder balance
      + ownerAggregateCriticalCoefficient balance
        * Owner.integralCritical (Nine.environment balance)
ownerAggregateFormula balance =
  Separation.ownerRemainderFormula balance
