module Ontology.Hecke.DefectOrbitPressureOrder where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-trans)

open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( GeneratorCollapseClass
    ; collapseTime
    ; collapseTime-anchoredTrajectory
    ; collapseTime-balancedComposed
    ; collapseTime-balancedCycle
    ; collapseTime-denseComposed
    ; collapseTime-explicitWidth1
    ; collapseTime-explicitWidth2
    ; collapseTime-explicitWidth3
    ; exitToAnchored
    ; immediateExit
    ; prefixClass
    ; staysOneMoreStep
    )
open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( CertifiedExitClass
    ; CertifiedExitToAnchoredClass
    ; CertifiedStayClass
    ; exitClassToGeneratorClass
    ; exitToAnchoredClassToGeneratorClass
    ; stayClassToGeneratorClass
    )
open import Ontology.Hecke.DefectOrbitCollapsePressure as DOCP
  using
    ( PressureClass
    ; highPressure
    ; lowPressure
    ; mediumPressure
    ; pressureClass
    ; pressureClass-explicit-exitToAnchored
    ; pressureClass-explicit-immediateExit
    ; pressureClass-explicit-staysOneMoreStep
    )
open import Ontology.Hecke.DefectOrbitCollapseBridge as DOCB
  using (forcedStableCountOrbitP2; illegalCountP2)

------------------------------------------------------------------------
-- Ordered pressure surface above the collapse-time pressure tiers.
--
-- This is the first honest monotonic comparison theorem on the current
-- bridge: the order is between coarse pressure classes, not yet between the
-- raw numeric orbit summaries.

------------------------------------------------------------------------
-- Assumption-guarded numeric pressure surfaces.
--
-- These do not replace the coarse order theorems below.  They expose the
-- next theorem layer as explicit success predicates so later representative
-- computations can discharge them without changing the interface.

ImmediateExitOrbitPressureOK : GeneratorCollapseClass → Set
ImmediateExitOrbitPressureOK c = suc zero ≤ illegalCountP2 c

StayVsImmediateOrbitOrderOK :
  GeneratorCollapseClass → GeneratorCollapseClass → Set
StayVsImmediateOrbitOrderOK cₛ cₑ =
  forcedStableCountOrbitP2 cₛ ≤ forcedStableCountOrbitP2 cₑ

AnchoredVsImmediateOrbitOrderOK :
  GeneratorCollapseClass → GeneratorCollapseClass → Set
AnchoredVsImmediateOrbitOrderOK cₐ cₑ =
  forcedStableCountOrbitP2 cₐ ≤ forcedStableCountOrbitP2 cₑ

immediateExit-orbit-pressure-assumption :
  ∀ c →
  collapseTime c ≡ immediateExit →
  ImmediateExitOrbitPressureOK c →
  suc zero ≤ forcedStableCountOrbitP2 c
immediateExit-orbit-pressure-assumption c _ pressure =
  ≤-trans
    pressure
    (DOCP.pressureLowerBoundAtP2 c)

stays-vs-immediate-order-assumption :
  ∀ cₛ cₑ →
  collapseTime cₛ ≡ staysOneMoreStep →
  collapseTime cₑ ≡ immediateExit →
  StayVsImmediateOrbitOrderOK cₛ cₑ →
  forcedStableCountOrbitP2 cₛ ≤ forcedStableCountOrbitP2 cₑ
stays-vs-immediate-order-assumption _ _ _ _ ok = ok

anchored-vs-immediate-order-assumption :
  ∀ cₐ cₑ →
  collapseTime cₐ ≡ exitToAnchored →
  collapseTime cₑ ≡ immediateExit →
  AnchoredVsImmediateOrbitOrderOK cₐ cₑ →
  forcedStableCountOrbitP2 cₐ ≤ forcedStableCountOrbitP2 cₑ
anchored-vs-immediate-order-assumption _ _ _ _ ok = ok

data _≤P_ : PressureClass → PressureClass → Set where
  low≤low : lowPressure ≤P lowPressure
  low≤medium : lowPressure ≤P mediumPressure
  low≤high : lowPressure ≤P highPressure
  medium≤medium : mediumPressure ≤P mediumPressure
  medium≤high : mediumPressure ≤P highPressure
  high≤high : highPressure ≤P highPressure

collapseTime-monotone-pressure :
  ∀ c₁ c₂ →
  collapseTime c₁ ≡ staysOneMoreStep →
  collapseTime c₂ ≡ immediateExit →
  pressureClass c₁ ≤P pressureClass c₂
collapseTime-monotone-pressure c₁ c₂ stay exit
  rewrite pressureClass-explicit-staysOneMoreStep c₁ stay
        | pressureClass-explicit-immediateExit c₂ exit
  = low≤high

anchored-vs-immediate-monotone-pressure :
  ∀ c₁ c₂ →
  collapseTime c₁ ≡ exitToAnchored →
  collapseTime c₂ ≡ immediateExit →
  pressureClass c₁ ≤P pressureClass c₂
anchored-vs-immediate-monotone-pressure c₁ c₂ anchored exit
  rewrite pressureClass-explicit-exitToAnchored c₁ anchored
        | pressureClass-explicit-immediateExit c₂ exit
  = medium≤high

stays-vs-anchored-monotone-pressure :
  ∀ c₁ c₂ →
  collapseTime c₁ ≡ staysOneMoreStep →
  collapseTime c₂ ≡ exitToAnchored →
  pressureClass c₁ ≤P pressureClass c₂
stays-vs-anchored-monotone-pressure c₁ c₂ stay anchored
  rewrite pressureClass-explicit-staysOneMoreStep c₁ stay
        | pressureClass-explicit-exitToAnchored c₂ anchored
  = low≤medium

stayCertifiedClass :
  CertifiedStayClass → GeneratorCollapseClass
stayCertifiedClass c = SCT.prefixClass (stayClassToGeneratorClass c)

exitCertifiedClass :
  CertifiedExitClass → GeneratorCollapseClass
exitCertifiedClass c = SCT.prefixClass (exitClassToGeneratorClass c)

anchoredCertifiedClass :
  CertifiedExitToAnchoredClass → GeneratorCollapseClass
anchoredCertifiedClass c =
  SCT.prefixClass (exitToAnchoredClassToGeneratorClass c)

stayCertifiedCollapse :
  (c : CertifiedStayClass) →
  collapseTime (stayCertifiedClass c) ≡ staysOneMoreStep
stayCertifiedCollapse GT.certifiedExplicitWidth1 = collapseTime-explicitWidth1
stayCertifiedCollapse GT.certifiedExplicitWidth3 = collapseTime-explicitWidth3
stayCertifiedCollapse GT.certifiedDenseComposed = collapseTime-denseComposed

exitCertifiedCollapse :
  (c : CertifiedExitClass) →
  collapseTime (exitCertifiedClass c) ≡ immediateExit
exitCertifiedCollapse GT.certifiedExplicitWidth2 = collapseTime-explicitWidth2
exitCertifiedCollapse GT.certifiedAnchoredTrajectory =
  collapseTime-anchoredTrajectory

anchoredCertifiedCollapse :
  (c : CertifiedExitToAnchoredClass) →
  collapseTime (anchoredCertifiedClass c) ≡ exitToAnchored
anchoredCertifiedCollapse GT.certifiedBalancedCycle =
  collapseTime-balancedCycle
anchoredCertifiedCollapse GT.certifiedBalancedComposed =
  collapseTime-balancedComposed

stayCertified≤exitCertified :
  ∀ cs ce →
  pressureClass (stayCertifiedClass cs)
    ≤P
  pressureClass (exitCertifiedClass ce)
stayCertified≤exitCertified cs ce =
  collapseTime-monotone-pressure
    (stayCertifiedClass cs)
    (exitCertifiedClass ce)
    (stayCertifiedCollapse cs)
    (exitCertifiedCollapse ce)

stayCertified≤anchoredCertified :
  ∀ cs ca →
  pressureClass (stayCertifiedClass cs)
    ≤P
  pressureClass (anchoredCertifiedClass ca)
stayCertified≤anchoredCertified cs ca =
  stays-vs-anchored-monotone-pressure
    (stayCertifiedClass cs)
    (anchoredCertifiedClass ca)
    (stayCertifiedCollapse cs)
    (anchoredCertifiedCollapse ca)

anchoredCertified≤exitCertified :
  ∀ ca ce →
  pressureClass (anchoredCertifiedClass ca)
    ≤P
  pressureClass (exitCertifiedClass ce)
anchoredCertified≤exitCertified ca ce =
  anchored-vs-immediate-monotone-pressure
    (anchoredCertifiedClass ca)
    (exitCertifiedClass ce)
    (anchoredCertifiedCollapse ca)
    (exitCertifiedCollapse ce)
