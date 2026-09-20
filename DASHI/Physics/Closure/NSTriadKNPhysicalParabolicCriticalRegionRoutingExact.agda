module DASHI.Physics.Closure.NSTriadKNPhysicalParabolicCriticalRegionRoutingExact where

------------------------------------------------------------------------
-- PERIODIC B / LITERAL R236 DEEP-vs-CRITICAL CLASSIFIER
--
-- R236 identifies the sharp dyadic decision surface but does not evaluate it
-- on literal physical incidences.  This owner supplies that missing routing.
--
-- For the actual R63 Bony tag:
--
--   LH : deep far-low iff 3 j_p <= 2 j_q
--   HL : deep far-low iff 3 j_q <= 2 j_p
--   HH : deep high-high iff 5 j_k <= 4 max(j_p,j_q)
--   CC : always critical core
--
-- Failure of either deep inequality is routed to the critical core.  Thus the
-- core contains exactly the two R236 shoulders plus comparable interactions.
-- No analytic estimate is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties as NatP using (_≤?_)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell

two three four five : Nat
two = suc (suc zero)
three = suc two
four = suc three
five = suc four

natMax : Nat → Nat → Nat
natMax zero n = n
natMax (suc m) zero = suc m
natMax (suc m) (suc n) = suc (natMax m n)

pShell qShell outputShell highInputShell :
  Physical.PhysicalTriadIncidence → Nat
pShell tau = Shell.shellIndex (Physical.p tau)
qShell tau = Shell.shellIndex (Physical.q tau)
outputShell tau = Shell.shellIndex (Physical.k tau)
highInputShell tau = natMax (pShell tau) (qShell tau)

deepLHCondition deepHLCondition deepHHCondition :
  Physical.PhysicalTriadIncidence → Set
deepLHCondition tau = three * pShell tau ≤ two * qShell tau
deepHLCondition tau = three * qShell tau ≤ two * pShell tau
deepHHCondition tau = five * outputShell tau ≤ four * highInputShell tau

data CriticalRegionTag : Set where
  deepFarLowRegion : CriticalRegionTag
  deepHighHighRegion : CriticalRegionTag
  criticalCoreRegion : CriticalRegionTag

data PhysicalCriticalRegion
    (tau : Physical.PhysicalTriadIncidence) : Set where
  deepFarLowLH :
    deepLHCondition tau →
    PhysicalCriticalRegion tau
  criticalFarLowLH :
    ¬ deepLHCondition tau →
    PhysicalCriticalRegion tau

  deepFarLowHL :
    deepHLCondition tau →
    PhysicalCriticalRegion tau
  criticalFarLowHL :
    ¬ deepHLCondition tau →
    PhysicalCriticalRegion tau

  deepHighHigh :
    deepHHCondition tau →
    PhysicalCriticalRegion tau
  criticalHighHigh :
    ¬ deepHHCondition tau →
    PhysicalCriticalRegion tau

  criticalComparable :
    PhysicalCriticalRegion tau

classifyPhysicalCriticalRegion :
  (tau : Physical.PhysicalTriadIncidence) →
  PhysicalCriticalRegion tau
classifyPhysicalCriticalRegion tau with Bony.bonyTag tau
... | Bony.lhTag with NatP._≤?_ (three * pShell tau) (two * qShell tau)
...   | yes deep = deepFarLowLH deep
...   | no shoulder = criticalFarLowLH shoulder
... | Bony.hlTag with NatP._≤?_ (three * qShell tau) (two * pShell tau)
...   | yes deep = deepFarLowHL deep
...   | no shoulder = criticalFarLowHL shoulder
... | Bony.hhToLowTag
    with NatP._≤?_ (five * outputShell tau) (four * highInputShell tau)
...   | yes deep = deepHighHigh deep
...   | no shoulder = criticalHighHigh shoulder
... | Bony.comparableTag = criticalComparable

regionTagFromEvidence :
  ∀ {tau} → PhysicalCriticalRegion tau → CriticalRegionTag
regionTagFromEvidence (deepFarLowLH deep) = deepFarLowRegion
regionTagFromEvidence (criticalFarLowLH shoulder) = criticalCoreRegion
regionTagFromEvidence (deepFarLowHL deep) = deepFarLowRegion
regionTagFromEvidence (criticalFarLowHL shoulder) = criticalCoreRegion
regionTagFromEvidence (deepHighHigh deep) = deepHighHighRegion
regionTagFromEvidence (criticalHighHigh shoulder) = criticalCoreRegion
regionTagFromEvidence criticalComparable = criticalCoreRegion

criticalRegionTag :
  Physical.PhysicalTriadIncidence → CriticalRegionTag
criticalRegionTag tau =
  regionTagFromEvidence (classifyPhysicalCriticalRegion tau)

data DeepFarLowEvidence
    (tau : Physical.PhysicalTriadIncidence) : Set where
  deepLH :
    Bony.bonyTag tau ≡ Bony.lhTag →
    deepLHCondition tau →
    DeepFarLowEvidence tau
  deepHL :
    Bony.bonyTag tau ≡ Bony.hlTag →
    deepHLCondition tau →
    DeepFarLowEvidence tau

data DeepHighHighEvidence
    (tau : Physical.PhysicalTriadIncidence) : Set where
  deepHH :
    Bony.bonyTag tau ≡ Bony.hhToLowTag →
    deepHHCondition tau →
    DeepHighHighEvidence tau

data CriticalCoreEvidence
    (tau : Physical.PhysicalTriadIncidence) : Set where
  shoulderLH :
    Bony.bonyTag tau ≡ Bony.lhTag →
    ¬ deepLHCondition tau →
    CriticalCoreEvidence tau
  shoulderHL :
    Bony.bonyTag tau ≡ Bony.hlTag →
    ¬ deepHLCondition tau →
    CriticalCoreEvidence tau
  shoulderHH :
    Bony.bonyTag tau ≡ Bony.hhToLowTag →
    ¬ deepHHCondition tau →
    CriticalCoreEvidence tau
  comparable :
    Bony.bonyTag tau ≡ Bony.comparableTag →
    CriticalCoreEvidence tau

criticalRegionEvidence :
  (tau : Physical.PhysicalTriadIncidence) →
  (DeepFarLowEvidence tau)
  ⊎ ((DeepHighHighEvidence tau) ⊎ CriticalCoreEvidence tau)
criticalRegionEvidence tau with Bony.bonyTag tau in tagEq
... | Bony.lhTag with NatP._≤?_ (three * pShell tau) (two * qShell tau)
...   | yes deep = inj₁ (deepLH tagEq deep)
...   | no shoulder = inj₂ (inj₂ (shoulderLH tagEq shoulder))
... | Bony.hlTag with NatP._≤?_ (three * qShell tau) (two * pShell tau)
...   | yes deep = inj₁ (deepHL tagEq deep)
...   | no shoulder = inj₂ (inj₂ (shoulderHL tagEq shoulder))
... | Bony.hhToLowTag
    with NatP._≤?_ (five * outputShell tau) (four * highInputShell tau)
...   | yes deep = inj₂ (inj₁ (deepHH tagEq deep))
...   | no shoulder = inj₂ (inj₂ (shoulderHH tagEq shoulder))
... | Bony.comparableTag =
  inj₂ (inj₂ (comparable tagEq))

literalR236PhysicalRegionClassifierClosed : Bool
literalR236PhysicalRegionClassifierClosed = true

literalR236RegionCoverExhaustive : Bool
literalR236RegionCoverExhaustive = true

criticalCoreContainsFarLowShoulder : Bool
criticalCoreContainsFarLowShoulder = true

criticalCoreContainsHighHighShoulder : Bool
criticalCoreContainsHighHighShoulder = true

criticalCoreContainsComparable : Bool
criticalCoreContainsComparable = true

literalR236RegionClassifierIntroducesEstimate : Bool
literalR236RegionClassifierIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

literalR236PhysicalRegionClassifierClosedIsTrue :
  literalR236PhysicalRegionClassifierClosed ≡ true
literalR236PhysicalRegionClassifierClosedIsTrue = refl
