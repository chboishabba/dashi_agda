module DASHI.Biology.IITJFineD4OrientedC4HeisenbergSteelmanExact where

------------------------------------------------------------------------
-- ORIGINAL OWNERS: source 3x3/c-gauge and geometric D4 in
-- IITJFineFourOneFourS3ZetaGaugeExact and
-- IITJFineD4EquivariantHeisenbergGaugeExact; original irrep roles in
-- TernaryMonsterSymmetryCandidateExact / D4IrrepFiniteFrickeEquivariantExact;
-- standard H6 group law in Monster3BFiniteHeisenbergCentralExtensionExact.
--
-- This is a NEW ACTION on the same oriented-eight / centre C3 CARRIER.
-- The old geometric quarter on corner E is REPLACED by a B1+B2 block;
-- one A1 trivial line is changed to an A2 orientation/sign line.
-- D4 mirror inverts the distinguished C3 centre, while r fixes it.
-- A GSp form of multiplier A2 is finite-checked in Python, but no
-- original-site D4 equivalence, full Agda group automorphism theorem,
-- Monster 3B subgroup, or physical identification is claimed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H6
import DASHI.Biology.IITJFineD4OrientationLineH4BypassExact as Prior

-- Relative order is (tE,tC,bE,bC,XE,YE,XC,YC).
-- New D4 character: A1+A2+2B1+2B2+E.
-- quarter r: B1/B2 both -1, E rotates, old second E replaced by -I2.
quarterPhasePreserving :
  Prior.OrientedEight → Prior.OrientedEight
quarterPhasePreserving
  (Prior.orientedEight c te tc be bc xe ye xc yc) =
  Prior.orientedEight c te tc
    (G.negate3 be) (G.negate3 bc)
    (G.negate3 ye) xe (G.negate3 xc) (G.negate3 yc)

-- mirror m: A2 inverts tC and the central phase, B2 inverts bC,
-- surviving E has diag(1,-1); new corner B1+B2 also diag(1,-1).
mirrorPhaseInverting :
  Prior.OrientedEight → Prior.OrientedEight
mirrorPhaseInverting
  (Prior.orientedEight c te tc be bc xe ye xc yc) =
  Prior.orientedEight (G.negate3 c)
    te (G.negate3 tc) be (G.negate3 bc)
    xe (G.negate3 ye) xc (G.negate3 yc)

quarterPreservesCentre : (q : Prior.OrientedEight) →
  Prior.phaseCentre (quarterPhasePreserving q) ≡ Prior.phaseCentre q
quarterPreservesCentre (Prior.orientedEight c te tc be bc xe ye xc yc) = refl

mirrorInvertsCentre : (q : Prior.OrientedEight) →
  Prior.phaseCentre (mirrorPhaseInverting q)
  ≡ G.negate3 (Prior.phaseCentre q)
mirrorInvertsCentre (Prior.orientedEight c te tc be bc xe ye xc yc) = refl

-- This is the ordinary ORIGINAL source H6 first-four-pair carrier.
-- Translation a=(tC,bC,yC,yE), modulation b=(tE,bE,xC,xE).
-- Unlike the earlier one-line mirror models, a general D4 GSp lift
-- also requires the t=c+a.b quadratic central rechart.
embedIntoOriginalH6 :
  Prior.OrientedEight → H6.Heisenberg6
embedIntoOriginalH6
  (Prior.orientedEight c te tc be bc xe ye xc yc) =
  H6.heisenberg6
    (H6.symplectic12
      (G.x6 tc bc yc ye zer zer)
      (G.x6 te be xc xe zer zer)) c

projectFromOriginalH6 :
  H6.Heisenberg6 → Prior.OrientedEight
projectFromOriginalH6
  (H6.heisenberg6 (H6.symplectic12
      (G.x6 tc bc yc ye a4 a5)
      (G.x6 te be xc xe b4 b5)) c) =
  Prior.orientedEight c te tc be bc xe ye xc yc

sourceProjectEmbed : (q : Prior.OrientedEight) →
  projectFromOriginalH6 (embedIntoOriginalH6 q) ≡ q
sourceProjectEmbed (Prior.orientedEight c te tc be bc xe ye xc yc) = refl

-- Finite phase-preserving C4 necessary-character target:
-- Original pointed marker has 2 fixed labels under r and r².
-- New source quotient has 2 and 6 fixed dimensions, respectively.
quarterPhaseTraceTarget : 2 * 3 * 3 ≡ 18
quarterPhaseTraceTarget = refl

halfTurnPhaseTraceTarget : 2 * 3 * 3 * 3 * 3 * 3 * 3 ≡ 1458
halfTurnPhaseTraceTarget = refl

identityPhaseDimension : 10 * 6561 ≡ 65610
identityPhaseDimension = refl

record C4SteelmanBoundary : Set where
  constructor c4SteelmanBoundary
  field
    sourceOrientedEightCarrierReused : Bool
    sourceSixPairHeisenbergOwnerReused : Bool
    centreMultiplierQuarterTrivial : Bool
    centreMultiplierMirrorNegative : Bool
    originalGeometricD4ActionKept : Bool
    exactC4TargetTraceArithmetic : Bool
    fullGSpGroupLawKernelProved : Bool
    sourceCharacterIntertwinerKernelProved : Bool
    actualMonsterThreeBNormalizerIdentified : Bool
    actualSixSuzSelectedMultiplicityCharacterPaid : Bool

currentBoundary : C4SteelmanBoundary
currentBoundary =
  c4SteelmanBoundary
    true true true true false true false false false false
