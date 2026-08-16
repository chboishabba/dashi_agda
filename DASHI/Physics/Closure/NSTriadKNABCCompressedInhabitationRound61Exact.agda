module DASHI.Physics.Closure.NSTriadKNABCCompressedInhabitationRound61Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- ROUND 61 CONTRIBUTION
--
-- The Round58/60 canonical ABC root accepts three already-packaged physical
-- sources.  After the Round61 reductions, B and C should not be packaged by
-- callers in that stronger form:
--
--   B: one active literal normalized-PQ = six-three-Gram same-object theorem
--      derives the 17/64, 65/512, 65/512 source fields and 133/256 aggregate;
--
--   C: C1 scale bounds plus C2's strict gap and K>0 derive the maximal positive
--      B_* = ((r-q)-a)/K and hence the complete Round60 fixed-shift capacity.
--
-- This module composes those derivations directly into the canonical ABC
-- source.  A remains source-indexed exactly as in Round59 because A1/A2 are
-- genuine unresolved PDE estimates and are not weakened or replaced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNABCInhabitationRound58Exact as ABC
import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalDuhamelSourceRound59 as A
import DASHI.Physics.Closure.NSTriadKNComActiveSixThreeRealizationRound61Exact as B
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact as BAggregate
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as CHeadroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftPhysicalCapacityAdapterRound58 as CAdapter
import DASHI.Physics.Closure.NSTriadKNFixedShiftSharpStrictGapCapacityRound61Exact as C
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

literalABCSourceFromRound61 :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {fixedShiftData : Fixed.FixedShiftRecursionPhysicalData}
    {fixedBlock : Block.RationalFixedBlockDecay}
    {identification : CHeadroom.PhysicalOwnerBlockCorrectionIdentification
      balances fixedShiftData fixedBlock} →
  (hhBadPhysicalSource : A.PhysicalLocalizedDuhamelSource) →
  A.PhysicalLocalizedDuhamelEstimates hhBadPhysicalSource →
  B.PhysicalActiveSixThreeOddPQSource →
  C.StrictPositiveCriticalScaleData identification →
  ABC.LiteralABCSourceWitnesses
literalABCSourceFromRound61
    {identification = identification}
    hhBadPhysicalSource hhBadPhysicalEstimates comPhysicalSource
    fixedShiftPhysicalData = record
  { hhBadPhysicalSource = hhBadPhysicalSource
  ; hhBadPhysicalEstimates = hhBadPhysicalEstimates
  ; comSource = B.asPhysicalNormalizedOddPQSource comPhysicalSource
  ; fixedShiftSource =
      CAdapter.physicalFixedShiftSourceFromScaleMatched
        identification
        (C.sharpStrictGapScaleMatchedCapacity fixedShiftPhysicalData)
  }

round61ABCComEndpoint :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {fixedShiftData : Fixed.FixedShiftRecursionPhysicalData}
    {fixedBlock : Block.RationalFixedBlockDecay}
    {identification : CHeadroom.PhysicalOwnerBlockCorrectionIdentification
      balances fixedShiftData fixedBlock}
    (hhBadPhysicalSource : A.PhysicalLocalizedDuhamelSource)
    (hhBadPhysicalEstimates :
      A.PhysicalLocalizedDuhamelEstimates hhBadPhysicalSource)
    (comPhysicalSource : B.PhysicalActiveSixThreeOddPQSource)
    (fixedShiftPhysicalData : C.StrictPositiveCriticalScaleData identification) →
  ∀ q →
  ABC.literalComBandwidthOneMass
    (literalABCSourceFromRound61
      hhBadPhysicalSource hhBadPhysicalEstimates
      comPhysicalSource fixedShiftPhysicalData) q
  ≤ BAggregate.bandwidthOneTarget
round61ABCComEndpoint
    hhBadPhysicalSource hhBadPhysicalEstimates
    comPhysicalSource fixedShiftPhysicalData =
  ABC.literalComBandwidthOneMassBelow133Over256
    (literalABCSourceFromRound61
      hhBadPhysicalSource hhBadPhysicalEstimates
      comPhysicalSource fixedShiftPhysicalData)

round61ABCSourceCompressionConstructed : Bool
round61ABCSourceCompressionConstructed = true

round61ABCSourceCompressionConstructedIsTrue :
  round61ABCSourceCompressionConstructed ≡ true
round61ABCSourceCompressionConstructedIsTrue = refl
