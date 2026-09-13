module DASHI.Physics.Chemistry.AtomicPeriodicTable369MadelungPeriodPartitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369MadelungExactSelector as M
import DASHI.Physics.Chemistry.AtomicPeriodicTable369OEISAufbauFormulaWeldExact as O

------------------------------------------------------------------------
-- Same-object bounded weld:
--
--   exact Madelung subshell stream
--      -> period blocks (cut immediately before the next ns block)
--      -> A093907 period lengths
--      -> A018227 cumulative closures.
--
-- The first seven physical-table periods are represented explicitly.  Their
-- concatenation, followed by the next 8s boundary marker, is definitionally the
-- first four diagonal layers of the exact selector.  This makes the 2,8,8,18,
-- 18,32,32 sequence a consumer of the same selected subshell objects rather
-- than merely a separately copied formula.
------------------------------------------------------------------------

infixr 5 _++P_

_++P_ : {A : Set} -> List A -> List A -> List A
[] ++P ys = ys
(x ∷ xs) ++P ys = x ∷ (xs ++P ys)

sumNat : List Nat -> Nat
sumNat [] = 0
sumNat (x ∷ xs) = x + sumNat xs

period1Blocks : List M.OrbitalBlock
period1Blocks = M.orbitalBlock 1 0 ∷ []

period2Blocks : List M.OrbitalBlock
period2Blocks = M.orbitalBlock 2 0 ∷ M.orbitalBlock 2 1 ∷ []

period3Blocks : List M.OrbitalBlock
period3Blocks = M.orbitalBlock 3 0 ∷ M.orbitalBlock 3 1 ∷ []

period4Blocks : List M.OrbitalBlock
period4Blocks =
  M.orbitalBlock 4 0 ∷ M.orbitalBlock 3 2 ∷ M.orbitalBlock 4 1 ∷ []

period5Blocks : List M.OrbitalBlock
period5Blocks =
  M.orbitalBlock 5 0 ∷ M.orbitalBlock 4 2 ∷ M.orbitalBlock 5 1 ∷ []

period6Blocks : List M.OrbitalBlock
period6Blocks =
  M.orbitalBlock 6 0 ∷ M.orbitalBlock 4 3 ∷ M.orbitalBlock 5 2
  ∷ M.orbitalBlock 6 1 ∷ []

period7Blocks : List M.OrbitalBlock
period7Blocks =
  M.orbitalBlock 7 0 ∷ M.orbitalBlock 5 3 ∷ M.orbitalBlock 6 2
  ∷ M.orbitalBlock 7 1 ∷ []

nextBoundary8s : List M.OrbitalBlock
nextBoundary8s = M.orbitalBlock 8 0 ∷ []

------------------------------------------------------------------------
-- Exact selector-stream decomposition through period 7.
------------------------------------------------------------------------

firstSevenPeriodsWithNextBoundary : List M.OrbitalBlock
firstSevenPeriodsWithNextBoundary =
  period1Blocks ++P period2Blocks ++P period3Blocks ++P period4Blocks
  ++P period5Blocks ++P period6Blocks ++P period7Blocks ++P nextBoundary8s

selectorPrefixThroughNextBoundary :
  firstSevenPeriodsWithNextBoundary ≡ M.madelungBlockPrefix 4
selectorPrefixThroughNextBoundary = refl

------------------------------------------------------------------------
-- Capacity images and A093907.
------------------------------------------------------------------------

periodCapacity : List M.OrbitalBlock -> Nat
periodCapacity bs = sumNat (M.mapCapacity bs)

period1Length : periodCapacity period1Blocks ≡ 2
period1Length = refl

period2Length : periodCapacity period2Blocks ≡ 8
period2Length = refl

period3Length : periodCapacity period3Blocks ≡ 8
period3Length = refl

period4Length : periodCapacity period4Blocks ≡ 18
period4Length = refl

period5Length : periodCapacity period5Blocks ≡ 18
period5Length = refl

period6Length : periodCapacity period6Blocks ≡ 32
period6Length = refl

period7Length : periodCapacity period7Blocks ≡ 32
period7Length = refl

periodLengthsMatchA093907Prefix :
  periodCapacity period1Blocks ≡ O.aufbauPeriodLength 1
  × periodCapacity period2Blocks ≡ O.aufbauPeriodLength 2
  × periodCapacity period3Blocks ≡ O.aufbauPeriodLength 3
  × periodCapacity period4Blocks ≡ O.aufbauPeriodLength 4
  × periodCapacity period5Blocks ≡ O.aufbauPeriodLength 5
  × periodCapacity period6Blocks ≡ O.aufbauPeriodLength 6
  × periodCapacity period7Blocks ≡ O.aufbauPeriodLength 7
periodLengthsMatchA093907Prefix =
  refl , (refl , (refl , (refl , (refl , (refl , refl)))))

------------------------------------------------------------------------
-- Cumulative closures and A018227.
------------------------------------------------------------------------

periodClosure1 : periodCapacity period1Blocks ≡ O.aufbauClosure 1
periodClosure1 = refl

periodClosure2 :
  periodCapacity period1Blocks + periodCapacity period2Blocks
  ≡ O.aufbauClosure 2
periodClosure2 = refl

periodClosure3 :
  periodCapacity period1Blocks + periodCapacity period2Blocks
  + periodCapacity period3Blocks
  ≡ O.aufbauClosure 3
periodClosure3 = refl

periodClosure7 :
  periodCapacity period1Blocks + periodCapacity period2Blocks
  + periodCapacity period3Blocks + periodCapacity period4Blocks
  + periodCapacity period5Blocks + periodCapacity period6Blocks
  + periodCapacity period7Blocks
  ≡ O.aufbauClosure 7
periodClosure7 = refl

------------------------------------------------------------------------
-- Source/provenance boundary.
------------------------------------------------------------------------

record PeriodPartitionAttribution : Set where
  constructor periodPartitionAttribution
  field
    oeisPeriodSequence : String
    oeisClosureSequence : String
    qidPeriodicTable : String
    qidAufbau : String
    goldBookAufbau : String
    deweyPeriodicTable : String
    primaryLiterature : String
    directLinks : String
    relationship : String

canonicalPeriodPartitionAttribution : PeriodPartitionAttribution
canonicalPeriodPartitionAttribution =
  periodPartitionAttribution
    "A093907"
    "A018227"
    "Q10693"
    "Q585745"
    "AT06996"
    "546.8"
    "Restrepo/Pachon DOI 10.1007/s10698-006-9026-6; Madelung 1936 DOI archive object 10.1007/978-3-662-02177-4; Klechkovskii 1962 JETP direct source; Allen/Knight DOI 10.1002/qua.965"
    "https://oeis.org/A093907 ; https://oeis.org/A018227 ; https://oeis.org/A167268"
    "identifier/source coordinates for the period/closure/build-up objects; none imports interacting-atom or empirical authority"

record MadelungPeriodPartitionBoundary : Set where
  constructor madelungPeriodPartitionBoundary
  field
    boundedSameObjectPeriodWeldPaid : Bool
    boundedSameObjectClosureWeldPaid : Bool
    genericAllPeriodPartitionTheoremPaid : Bool
    empiricalGroundStateOrderingPaid : Bool
    nuclearStabilityPaid : Bool
    ionizationSpectrumPaid : Bool

canonicalMadelungPeriodPartitionBoundary : MadelungPeriodPartitionBoundary
canonicalMadelungPeriodPartitionBoundary =
  madelungPeriodPartitionBoundary true true false false false false

record MadelungPeriodPartitionFrontier : Set where
  constructor madelungPeriodPartitionFrontier
  field
    paid : String
    firstUnpaidStructural : String
    firstUnpaidPhysical : String
    historicalResidual : String
    paymentRule : String

canonicalMadelungPeriodPartitionFrontier : MadelungPeriodPartitionFrontier
canonicalMadelungPeriodPartitionFrontier =
  madelungPeriodPartitionFrontier
    "the exact selected subshell stream through 7p is partitioned into the first seven period blocks; their capacities equal A093907 2,8,8,18,18,32,32 and cumulative closure reaches A018227 value 118"
    "generalize the split-at-next-ns partition theorem to arbitrary selector depth if an unbounded structural theorem is needed"
    "same-object interacting Hamiltonian -> spectrum -> total energies -> calibrated ionization energies, with empirical exceptions/ground-state configurations kept separate from structural Madelung order"
    "original historical standalone n+alpha*l script/hash/parameter schedule remains unresolved; the exact selector is a later typed repair, not a rewritten historical artifact"
    "OEIS/DOI/QID/GoldBook/Dewey/link route discovery; same-object typed construction pays only its stated structural consumer"
