module Ontology.Hecke.DefectOrbitCollapseBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

open import MonsterOntos using (p2)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecDefectHistograms as FDH
  using (illegalCount)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
  using (DefectOrbitSummary; profileSummaryAt)

open import DASHI.Physics.Closure.ShiftContractAnchoredTrajectoryFamily as SATJ
  using (trajectoryGen)
open import DASHI.Physics.Closure.ShiftContractBalancedComposedFamily as SBCF
  using (balancedComposedGen)
open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( CollapseTime
    ; GeneratorCollapseClass
    ; collapseTime
    ; exitToAnchored
    ; immediateExit
    ; mixedScaleClass
    ; prefixClass
    ; staysOneMoreStep
    ; unknownCollapse
    )
open import DASHI.Physics.Closure.ShiftContractComposedFamily as SCF
  using (composedGen)
open import DASHI.Physics.Closure.ShiftContractFullSupportTrajectory as FS
  using (fullSupport)
open import DASHI.Physics.Closure.ShiftContractMdlLevelExplicitStateSearchAudit as ES
  using (oneHot2)
open import DASHI.Physics.Closure.ShiftContractMixedScaleTrajectoryFamily as MTF
  using (fullSupportCascade; supportCascade)
open import DASHI.Physics.Closure.ShiftContractParametricTrajectoryCompositionFamily as PTF
  using
    ( anchoredTrajectory
    ; balancedComposed
    ; balancedCycle
    ; denseComposed
    ; explicitWidth1
    ; explicitWidth2
    ; explicitWidth3
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStatePrimeImage
    ; shiftContractStateForcedStableTransferBridge
    ; shiftContractStateIllegalCount≤forcedStableCountOrbit
    )
open import DASHI.Physics.Closure.ShiftContractSupportCascadeTrajectory as SSCT
  using (cascade0)
open import DASHI.Physics.Closure.ShiftContractTriadic3CycleInstance as ST3
  using (cycleGen)
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (i2)
open import DASHI.Physics.Closure.ShiftContractDenseTriadicFamily as SDTF
  using (denseGen)
open import DASHI.Physics.Closure.ShiftContractAnchoredTriadicFamily as SATF
  using (anchored0)

------------------------------------------------------------------------
-- First honest bridge from generator-collapse classification into the
-- existing Hecke defect/orbit ladder.
--
-- This does not overclaim a full persistence dictionary.  It selects one
-- representative live `ShiftContractState` for each generator class and then
-- reuses the already-proved `illegalCount ≤ forcedStableCount_orbit` bridge
-- at the prime `p2`.

representativeState : GeneratorCollapseClass → ShiftContractState
representativeState (prefixClass explicitWidth1) = oneHot2
representativeState (prefixClass explicitWidth2) = anchored0
representativeState (prefixClass explicitWidth3) = denseGen i2
representativeState (prefixClass balancedCycle) = cycleGen i2
representativeState (prefixClass denseComposed) = composedGen i2
representativeState (prefixClass balancedComposed) = balancedComposedGen i2
representativeState (prefixClass anchoredTrajectory) = trajectoryGen i2
representativeState (mixedScaleClass supportCascade) = cascade0
representativeState (mixedScaleClass fullSupportCascade) = fullSupport

primeImage : GeneratorCollapseClass → FactorVec
primeImage c = shiftContractStatePrimeImage (representativeState c)

orbitSummaryP2 : GeneratorCollapseClass → DefectOrbitSummary
orbitSummaryP2 c = profileSummaryAt p2 (primeImage c)

illegalCountP2 : GeneratorCollapseClass → Nat
illegalCountP2 c = illegalCount p2 (primeImage c)

forcedStableCountOrbitP2 : GeneratorCollapseClass → Nat
forcedStableCountOrbitP2 c =
  FOS.DefectOrbitSummary.forcedStableCount (orbitSummaryP2 c)

illegalCount≤forcedStableCountOrbitP2 :
  ∀ c →
  illegalCountP2 c ≤ forcedStableCountOrbitP2 c
illegalCount≤forcedStableCountOrbitP2 c =
  shiftContractStateIllegalCount≤forcedStableCountOrbit
    (representativeState c) p2

immediateExit-gives-orbitLowerBound :
  ∀ c →
  collapseTime c ≡ immediateExit →
  illegalCountP2 c ≤ forcedStableCountOrbitP2 c
immediateExit-gives-orbitLowerBound c _ =
  illegalCount≤forcedStableCountOrbitP2 c

staysOneMoreStep-gives-orbitLowerBound :
  ∀ c →
  collapseTime c ≡ staysOneMoreStep →
  illegalCountP2 c ≤ forcedStableCountOrbitP2 c
staysOneMoreStep-gives-orbitLowerBound c _ =
  illegalCount≤forcedStableCountOrbitP2 c

exitToAnchored-gives-orbitLowerBound :
  ∀ c →
  collapseTime c ≡ exitToAnchored →
  illegalCountP2 c ≤ forcedStableCountOrbitP2 c
exitToAnchored-gives-orbitLowerBound c _ =
  illegalCount≤forcedStableCountOrbitP2 c

unknownCollapse-gives-orbitLowerBound :
  ∀ c →
  collapseTime c ≡ unknownCollapse →
  illegalCountP2 c ≤ forcedStableCountOrbitP2 c
unknownCollapse-gives-orbitLowerBound c _ =
  illegalCount≤forcedStableCountOrbitP2 c

record DefectOrbitCollapseBridge : Set₁ where
  field
    representative :
      GeneratorCollapseClass → ShiftContractState
    representativePrimeImage :
      GeneratorCollapseClass → FactorVec
    representativeOrbitSummaryP2 :
      GeneratorCollapseClass → DefectOrbitSummary
    representativeIllegalCountP2 :
      GeneratorCollapseClass → Nat
    representativeForcedStableCountOrbitP2 :
      GeneratorCollapseClass → Nat
    representativeIllegalCount≤forcedStableCountOrbitP2 :
      ∀ c →
      representativeIllegalCountP2 c
        ≤
      representativeForcedStableCountOrbitP2 c

canonicalDefectOrbitCollapseBridge :
  DefectOrbitCollapseBridge
canonicalDefectOrbitCollapseBridge =
  record
    { representative = representativeState
    ; representativePrimeImage = primeImage
    ; representativeOrbitSummaryP2 = orbitSummaryP2
    ; representativeIllegalCountP2 = illegalCountP2
    ; representativeForcedStableCountOrbitP2 = forcedStableCountOrbitP2
    ; representativeIllegalCount≤forcedStableCountOrbitP2 =
        illegalCount≤forcedStableCountOrbitP2
    }

open DefectOrbitCollapseBridge public
