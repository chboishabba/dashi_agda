module DASHI.Analysis.RHFourWindowAngularC3C4SufficientConsumerExact where

-- ORIGINAL SOURCE CONSUMER CUT (23 Nov 2026).
-- RH fourth-difference angular step h=pi/2 is C4 as an integer-q
-- phase, not a C3 spatial shift. Source original pi/3 raw
-- contributions are retained through RH.Source4 even when observed
-- zero. Original C3 torus source: FiniteThreeCycleTorusExact.
-- Original FOUR phase source: ShiftPhaseTableInterference.Phase4.
-- Original consumer authority: ConsumerDescentMinimalObserverExact,
-- which REUSES ObserverFactorizedRefinementExact.
-- Lacan/Irigaray directed relational grammars remain SEPARATE.
-- Source-written pending Agda kernel, finite integer-q fixture only.
-- Does NOT prove analytic noninteger-q phase, ζ zeros, mu or FarExact.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as C3
import DASHI.Physics.ShiftPhaseTableInterference as C4
import DASHI.Analysis.RHFourWindowBiharmonicFiniteCubeExact as RH

-- Preserve original source actor types; do not define a new trit,
-- cyclic three carrier, four-phase carrier, or H05 cube.
JointPhase : Set
JointPhase = C3.Residue3 × C4.Phase4

phaseNext : C4.Phase4 → C4.Phase4
phaseNext C4.φ0 = C4.φ1
phaseNext C4.φ1 = C4.φ2
phaseNext C4.φ2 = C4.φ3
phaseNext C4.φ3 = C4.φ0

jointNext : JointPhase → JointPhase
jointNext (r , a) = C3.next3 r , phaseNext a

iterateJoint : Nat → JointPhase → JointPhase
iterateJoint zero p = p
iterateJoint (suc n) p = jointNext (iterateJoint n p)

-- C3×C4 has ONE joint orbit of length 12.
jointCycle12 : (r : C3.Residue3) (a : C4.Phase4) →
  iterateJoint 12 (r , a) ≡ (r , a)
jointCycle12 C3.residueZero C4.φ0 = refl
jointCycle12 C3.residueZero C4.φ1 = refl
jointCycle12 C3.residueZero C4.φ2 = refl
jointCycle12 C3.residueZero C4.φ3 = refl
jointCycle12 C3.residuePlus C4.φ0 = refl
jointCycle12 C3.residuePlus C4.φ1 = refl
jointCycle12 C3.residuePlus C4.φ2 = refl
jointCycle12 C3.residuePlus C4.φ3 = refl
jointCycle12 C3.residueMinus C4.φ0 = refl
jointCycle12 C3.residueMinus C4.φ1 = refl
jointCycle12 C3.residueMinus C4.φ2 = refl
jointCycle12 C3.residueMinus C4.φ3 = refl

-- The fourth step advances C3 while preserving the RH C4 phase.
fourStepsAdvanceSpatial :
  (r : C3.Residue3) (a : C4.Phase4) →
  iterateJoint 4 (r , a) ≡ (C3.next3 r , a)
fourStepsAdvanceSpatial C3.residueZero C4.φ0 = refl
fourStepsAdvanceSpatial C3.residueZero C4.φ1 = refl
fourStepsAdvanceSpatial C3.residueZero C4.φ2 = refl
fourStepsAdvanceSpatial C3.residueZero C4.φ3 = refl
fourStepsAdvanceSpatial C3.residuePlus C4.φ0 = refl
fourStepsAdvanceSpatial C3.residuePlus C4.φ1 = refl
fourStepsAdvanceSpatial C3.residuePlus C4.φ2 = refl
fourStepsAdvanceSpatial C3.residuePlus C4.φ3 = refl
fourStepsAdvanceSpatial C3.residueMinus C4.φ0 = refl
fourStepsAdvanceSpatial C3.residueMinus C4.φ1 = refl
fourStepsAdvanceSpatial C3.residueMinus C4.φ2 = refl
fourStepsAdvanceSpatial C3.residueMinus C4.φ3 = refl

-- The ninth step advances original FOUR angular phases, C3 fixed.
nineStepsAdvanceAngular :
  (r : C3.Residue3) (a : C4.Phase4) →
  iterateJoint 9 (r , a) ≡ (r , phaseNext a)
nineStepsAdvanceAngular C3.residueZero C4.φ0 = refl
nineStepsAdvanceAngular C3.residueZero C4.φ1 = refl
nineStepsAdvanceAngular C3.residueZero C4.φ2 = refl
nineStepsAdvanceAngular C3.residueZero C4.φ3 = refl
nineStepsAdvanceAngular C3.residuePlus C4.φ0 = refl
nineStepsAdvanceAngular C3.residuePlus C4.φ1 = refl
nineStepsAdvanceAngular C3.residuePlus C4.φ2 = refl
nineStepsAdvanceAngular C3.residuePlus C4.φ3 = refl
nineStepsAdvanceAngular C3.residueMinus C4.φ0 = refl
nineStepsAdvanceAngular C3.residueMinus C4.φ1 = refl
nineStepsAdvanceAngular C3.residueMinus C4.φ2 = refl
nineStepsAdvanceAngular C3.residueMinus C4.φ3 = refl

-- For INTEGER angular q the original atomic response is
-- F(q)=-80/351*(1-cos(pi*q/2))². In units -80/351 the table
-- is 0,1,4,1 (zero means observed FOURTH-DIFFERENCE NOTCH,
-- NOT a zeta zero). The sign is negative for all nonzero entries.
quarticMagnitude4 : C4.Phase4 → Nat
quarticMagnitude4 C4.φ0 = 0
quarticMagnitude4 C4.φ1 = 1
quarticMagnitude4 C4.φ2 = 4
quarticMagnitude4 C4.φ3 = 1

data QuarticSign : Set where
  observedNotchZero negativeNotch : QuarticSign

quarticSigned4 : C4.Phase4 → QuarticSign
quarticSigned4 C4.φ0 = observedNotchZero
quarticSigned4 C4.φ1 = negativeNotch
quarticSigned4 C4.φ2 = negativeNotch
quarticSigned4 C4.φ3 = negativeNotch

jointRHResponse : JointPhase → Nat
jointRHResponse p = quarticMagnitude4 (proj₂ p)

-- The native original C3 stroboscopic time phase is + on q≡0 mod3
-- and minus on the two nonzero classes. This is a different consumer.
nativeTimePhase : C3.Residue3 → Bool
nativeTimePhase C3.residueZero = true
nativeTimePhase C3.residuePlus = false
nativeTimePhase C3.residueMinus = false

jointTimePhase : JointPhase → Bool
jointTimePhase p = nativeTimePhase (proj₁ p)

-- Explicit POSITIVE FactorsThrough receipts for different consumers.
rhFactorsThroughAngular4 :
  Consumer.FactorsThrough proj₂ jointRHResponse
rhFactorsThroughAngular4 =
  Factorized.factorizedRefinement quarticMagnitude4 (λ _ → refl)

timeFactorsThroughNative3 :
  Consumer.FactorsThrough proj₁ jointTimePhase
timeFactorsThroughNative3 =
  Factorized.factorizedRefinement nativeTimePhase (λ _ → refl)

-- Source-labelled integer angular frequencies: q=1 and q=4
-- both alias to the SAME C3 frequency, but NOT the same RH value.
data SelectedRHFrequency : Set where
  originalQOne originalQFour : SelectedRHFrequency

selectedNative3 : SelectedRHFrequency → C3.Residue3
selectedNative3 originalQOne = C3.residuePlus
selectedNative3 originalQFour = C3.residuePlus

selectedAngular4 : SelectedRHFrequency → C4.Phase4
selectedAngular4 originalQOne = C4.φ1
selectedAngular4 originalQFour = C4.φ0

selectedRHResponse : SelectedRHFrequency → Nat
selectedRHResponse f = quarticMagnitude4 (selectedAngular4 f)

sameC3SourceFrequency :
  selectedNative3 originalQOne ≡ selectedNative3 originalQFour
sameC3SourceFrequency = refl

originalQOneDiffersFromQFour :
  selectedRHResponse originalQOne ≡
  selectedRHResponse originalQFour → ⊥
originalQOneDiffersFromQFour ()

c3AloneNotRHSufficient :
  Consumer.ConsumerNonDescentWitness selectedNative3 selectedRHResponse
c3AloneNotRHSufficient =
  Consumer.consumerNonDescentWitness
    originalQOne originalQFour
    sameC3SourceFrequency originalQOneDiffersFromQFour

noC3OnlyRHFactorsThrough :
  Consumer.FactorsThrough selectedNative3 selectedRHResponse → ⊥
noC3OnlyRHFactorsThrough =
  Consumer.nonDescentWitnessBlocksFactorization c3AloneNotRHSufficient

selectedC4RepairsRHConsumer :
  Consumer.FactorsThrough selectedAngular4 selectedRHResponse
selectedC4RepairsRHConsumer =
  Factorized.factorizedRefinement quarticMagnitude4 (λ _ → refl)

-- A nonidentity ANGULAR C4 step changes the original Fourier notch;
-- do NOT treat that step as analytic RH ζ-zero symmetry.
qFourNotchIsZero : jointRHResponse (C3.residuePlus , C4.φ0) ≡ 0
qFourNotchIsZero = refl

qFourAngularNextNotZero :
  jointRHResponse (jointNext (C3.residuePlus , C4.φ0)) ≡ 1
qFourAngularNextNotZero = refl

qFourNativeTimePhaseNegative :
  jointTimePhase (C3.residuePlus , C4.φ0) ≡ false
qFourNativeTimePhaseNegative = refl

-- SOURCE TRACE: original four source sites, including TWO NONZERO
-- cancelled pi/3 components, are not discarded by finite phase.
PhasedOriginalFour : Set
PhasedOriginalFour = JointPhase × RH.Source4

jointMoveOriginal : PhasedOriginalFour → PhasedOriginalFour
jointMoveOriginal (phase , source) = jointNext phase , source

projectOriginal : PhasedOriginalFour →
  JointPhase × RH.TracedFold
projectOriginal (phase , source) = phase , RH.projectWithSource source

unfoldOriginal :
  JointPhase × RH.TracedFold → JointPhase × RH.TracedFive
unfoldOriginal (phase , source) = phase , RH.unfoldWithSource source

directOriginal : PhasedOriginalFour →
  JointPhase × RH.TracedFive
directOriginal (phase , source) = phase , RH.directWithSource source

originalRHPhaseSquare : (state : PhasedOriginalFour) →
  directOriginal state ≡ unfoldOriginal (projectOriginal state)
originalRHPhaseSquare
  (phase , RH.source4 c l r cancel inner outer) = refl

sourceReturned : (state : PhasedOriginalFour) →
  proj₂ (directOriginal state) ≡
    RH.directWithSource (proj₂ state)
sourceReturned (phase , source) = refl

-- Reuse RH's original H05 history/time/refinement/Frobenius/version
-- metadata and distinct sign/residual/mode/observation fields.
indexedJointShift :
  ∀ {Index Sign Residual Mode Observation : Set} →
  RH.IndexedSource Index Sign Residual Mode Observation PhasedOriginalFour →
  RH.IndexedSource Index Sign Residual Mode Observation PhasedOriginalFour
indexedJointShift = RH.mapIndexedPayload jointMoveOriginal

-- Unlike an atom q=4 finite notch, the actual zero-side ζ source,
-- marked derivatives, µ, signed FarExact and A2 scalar are not inhabited.
