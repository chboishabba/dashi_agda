module DASHI.Physics.Gravity.KKSmoothCircleChiralityModelForkExact where

------------------------------------------------------------------------
-- 2026-10-24 KK STEELMAN MODEL-SELECTION FORK.
--
-- Existing source: KKCircleQEDChiralityConsumerExact already proves
-- QED charge/mass alone do NOT identify SU2L handedness.
-- This NEW finite theorem adds the topology/fermion-domain choice.
--
-- Physical continuum source (checked in independent Python):
-- 5D real mass M(y), smooth periodic S1 and flat unitary Wilson phase
-- have L/R monodromy exp(-I+i theta), exp(+I+i theta).
-- Both 4D zero modes occur TOGETHER or not at all.
-- The finite labels here are NOT a continuum Dirac operator theorem.
-- An S1/Z2 orbifold can SELECT ONE zero mode, but the source action
-- changes: fixed-plane anomalies, gauge parities and Casimir spectrum.
--
-- Original anomaly inflow prior art:
-- Callan-Harvey 1985; Arkani-Hamed/Cohen/Georgi 2001;
-- Scrucca/Serone/Silvestrini/Zwirner 2002.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Physics.Gravity.KKCircleQEDChiralityConsumerExact as Prior
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

priorQEDChiralityObstruction :
  Transport.ClaimNonTransportWitness Prior.qedObserve Prior.chiralityQuestion
priorQEDChiralityObstruction = Prior.qedDoesNotDetermineChirality

data RealMassMean : Set where
  zeroAverageMass nonzeroAverageMass : RealMassMean

data FlatUnitaryWilson : Set where
  trivialWilson nontrivialWilson : FlatUnitaryWilson

leftZeroModeExists : RealMassMean → FlatUnitaryWilson → Bool
leftZeroModeExists zeroAverageMass trivialWilson = true
leftZeroModeExists _ _ = false

rightZeroModeExists : RealMassMean → FlatUnitaryWilson → Bool
rightZeroModeExists zeroAverageMass trivialWilson = true
rightZeroModeExists _ _ = false

-- Finite consequence of selected smooth-S1 zero-mode monodromy.
smoothSOneHasPairedChiralities :
  ∀ mass holonomy →
  leftZeroModeExists mass holonomy ≡
  rightZeroModeExists mass holonomy
smoothSOneHasPairedChiralities zeroAverageMass trivialWilson = refl
smoothSOneHasPairedChiralities zeroAverageMass nontrivialWilson = refl
smoothSOneHasPairedChiralities nonzeroAverageMass trivialWilson = refl
smoothSOneHasPairedChiralities nonzeroAverageMass nontrivialWilson = refl

data CompactificationModel : Set where
  smoothSOneBulkDirac
  orbifoldSOneOverZTwoBulkDirac
  braneLocalisedFourDChiralMatter : CompactificationModel

-- "can select" differs from a complete/consistent Standard Model.
allowsUnpairedFourDZeroMode : CompactificationModel → Bool
allowsUnpairedFourDZeroMode smoothSOneBulkDirac = false
allowsUnpairedFourDZeroMode orbifoldSOneOverZTwoBulkDirac = true
allowsUnpairedFourDZeroMode braneLocalisedFourDChiralMatter = true

oldPeriodicBulkCasimirSameObject : CompactificationModel → Bool
oldPeriodicBulkCasimirSameObject smoothSOneBulkDirac = true
oldPeriodicBulkCasimirSameObject orbifoldSOneOverZTwoBulkDirac = false
oldPeriodicBulkCasimirSameObject braneLocalisedFourDChiralMatter = false

netSMChiralityAndGaugeAnomaliesCertified :
  CompactificationModel → Bool
netSMChiralityAndGaugeAnomaliesCertified _ = false

-- All options can begin with the same 27-dimensional representation
-- COUNTS, but the zero-mode domain / parity gives a different answer.
commonFirstTitsCarrierDimension : CompactificationModel → Nat
commonFirstTitsCarrierDimension _ = 27

falseIsNotTrue : false ≡ true → ⊥
falseIsNotTrue ()

carrierDimensionDoesNotSelectChiralBoundary :
  Transport.ClaimNonTransportWitness
    commonFirstTitsCarrierDimension allowsUnpairedFourDZeroMode
carrierDimensionDoesNotSelectChiralBoundary =
  Descent.consumerNonDescentWitness
    smoothSOneBulkDirac orbifoldSOneOverZTwoBulkDirac
    refl falseIsNotTrue

noFull27CardinalityToChiralSMZeroMode :
  Transport.ClaimTransport
    commonFirstTitsCarrierDimension allowsUnpairedFourDZeroMode → ⊥
noFull27CardinalityToChiralSMZeroMode =
  Transport.claimNonTransportWitnessBlocksTransport
    carrierDimensionDoesNotSelectChiralBoundary

anySufficientTopologicalRefinementMustSeparateChoices :
  (refine : CompactificationModel → Bool) →
  Repair.RefinementRepairs
    commonFirstTitsCarrierDimension refine allowsUnpairedFourDZeroMode →
  refine smoothSOneBulkDirac
    ≡ refine orbifoldSOneOverZTwoBulkDirac → ⊥
anySufficientTopologicalRefinementMustSeparateChoices refine adequate same =
  Repair.refinementRepairSeparatesWitness
    carrierDimensionDoesNotSelectChiralBoundary adequate same

-- This is the core REUSE COST: the unorbifolded one-loop determinant
-- is not transported to the orbifold/brane theory by cardinality.
smoothPeriodicDeterminantNotSameAsOrbifoldDeterminant :
  Transport.ClaimNonTransportWitness
    commonFirstTitsCarrierDimension oldPeriodicBulkCasimirSameObject
smoothPeriodicDeterminantNotSameAsOrbifoldDeterminant =
  Descent.consumerNonDescentWitness
    orbifoldSOneOverZTwoBulkDirac smoothSOneBulkDirac
    refl falseIsNotTrue

-- No positive Standard Model claim is made from choosing an orbifold:
-- the gauge parities, fixed-plane anomalies, global spin/CS terms,
-- one physical photon and all metric sources must still be paid.
