module DASHI.Biology.IITJFineD4OrientationLineH4BypassExact where

------------------------------------------------------------------------
-- SOURCE OWNERS / ATTRIBUTION
-- Original nine-cell D4 action and its 2A1+B1+B2+2E shell:
--   DASHI.Biology.TernaryMonsterSymmetryCandidateExact
--   DASHI.Biology.IITJFineFourOneFourS3ZetaGaugeExact
-- Irrep orientation and finite C2 chart:
--   DASHI.Biology.D4IrrepFiniteFrickeEquivariantExact
-- Original six-pair Heisenberg multiplication, NOT redefined here:
--   DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact
--
-- New model: replace the natural axis-mirror sign on ONE B2
-- character line by the B1 sign, while preserving original D4 rotation.
-- The underlying 3^9 trit carrier is unchanged, but the action is NOT
-- the original literal 3x3-site reflection.
--
-- The exact source-sheet matrix inversion, rank-one mirror defect,
-- nondegenerate alternating pairing and D4-H4 group action are verified
-- by scripts/iit_jfine_d4_single_line_orientation_bypass.py.
-- Agda source here is an explicit TYPE-LEVEL MODEL, not an exact-head
-- Agda kernel proof of the matrix or 354294-state group law.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H6

record OrientedEight : Set where
  constructor orientedEight
  field
    phaseCentre : Trit
    edgeTrivial cornerTrivial : Trit
    edgeB1 cornerContrast : Trit
    edgeE0 edgeE1 cornerE0 cornerE1 : Trit
open OrientedEight public

-- source D4 quarter-turn: B1 and B2 both have r=-1, E has r^2=-I.
quarterSource : OrientedEight → OrientedEight
quarterSource (orientedEight c te tc be bc xe ye xc yc) =
  orientedEight c te tc (G.negate3 be) (G.negate3 bc)
    (G.negate3 ye) xe (G.negate3 yc) xc

-- ACTUAL source geometric mirror: corner contrast is B2 and flips.
mirrorGeometric : OrientedEight → OrientedEight
mirrorGeometric (orientedEight c te tc be bc xe ye xc yc) =
  orientedEight c te tc be (G.negate3 bc)
    xe (G.negate3 ye) xc (G.negate3 yc)

-- NEW source-carrier, different operator: bC has B1 mirror sign.
mirrorOriented : OrientedEight → OrientedEight
mirrorOriented (orientedEight c te tc be bc xe ye xc yc) =
  orientedEight c te tc be bc xe (G.negate3 ye) xc (G.negate3 yc)

-- Both operators fix the independent original balanced-value centre.
mirrorOrientedPreservesCentre :
  (q : OrientedEight) →
  phaseCentre (mirrorOriented q) ≡ phaseCentre q
mirrorOrientedPreservesCentre (orientedEight c te tc be bc xe ye xc yc) = refl

quarterPreservesCentre :
  (q : OrientedEight) →
  phaseCentre (quarterSource q) ≡ phaseCentre q
quarterPreservesCentre (orientedEight c te tc be bc xe ye xc yc) = refl

b2Witness : OrientedEight
b2Witness = orientedEight zer zer zer zer pos zer zer zer zer

-- This counterexample is the admission firewall:
-- The bypass does not silently preserve the ORIGINAL spatial mirror.
mirrorActionsDifferentAtB2Witness :
  mirrorGeometric b2Witness ≡ mirrorOriented b2Witness → ⊥
mirrorActionsDifferentAtB2Witness ()

-- Source-written concrete H4 into existing H6 first four Weyl pairs.
-- The source 8D coordinates are now paired as:
-- translations=(tC,bC,xC,yC), modulations=(tE,bE,xE,yE).
-- This is a genuine four-pair carrier, unlike the earlier D4-stable
-- degenerate source subgroup H3 x C3^2.
embedOrientedH4InExistingH6 : OrientedEight → H6.Heisenberg6
embedOrientedH4InExistingH6
  (orientedEight c te tc be bc xe ye xc yc) =
  H6.heisenberg6
    (H6.symplectic12
      (G.x6 tc bc xc yc zer zer)
      (G.x6 te be xe ye zer zer))
    c

projectFromExistingH6 : H6.Heisenberg6 → OrientedEight
projectFromExistingH6
  (H6.heisenberg6
    (H6.symplectic12
      (G.x6 tc bc xc yc t4 t5)
      (G.x6 te be xe ye m4 m5)) c) =
  orientedEight c te tc be bc xe ye xc yc

projectEmbed :
  (q : OrientedEight) →
  projectFromExistingH6 (embedOrientedH4InExistingH6 q) ≡ q
projectEmbed (orientedEight c te tc be bc xe ye xc yc) = refl

-- The H4 MODEL product is pulled back from the pre-existing H6
-- multiplication, NOT a new free-standing Heisenberg group definition.
orientedModelProduct : OrientedEight → OrientedEight → OrientedEight
orientedModelProduct x y =
  projectFromExistingH6
    (H6.compose (embedOrientedH4InExistingH6 x)
                (embedOrientedH4InExistingH6 y))

orientedCarrierCount : 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3 ≡ 19683
orientedCarrierCount = refl

record BypassAdmission : Set where
  constructor bypassAdmission
  field
    priorOriginalD4CarrierReused : Bool
    priorH6SourceProductReused : Bool
    newD4MirrorDiffersFromOriginalSource : Bool
    noNewTritCoordinates : Bool
    concreteH4InH6CarrierConstructed : Bool
    rankOneOriginalSheetOperatorProofKernelChecked : Bool
    fullD4H4AutomorphismLawKernelChecked : Bool
    literalMonster3BNormalizerSameObject : Bool

currentAdmission : BypassAdmission
currentAdmission =
  bypassAdmission true true true true true false false false
