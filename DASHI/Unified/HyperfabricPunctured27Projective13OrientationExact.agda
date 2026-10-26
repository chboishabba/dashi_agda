module DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact where

-- P0 same-CARRIER sequel to native #1249, not a new 27-site cube.
-- Source owners:
--   DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact (P3^3)
--   DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact
--     (the ACTUAL signed negation, involution and graph compatibility)
--   DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact
--     (origin+26 set chart, NOT Jordan multiplication)
--   DASHI.Wikimedia.IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact
--     (historical OEIS arithmetic owner)
-- Independent related branch #1261: Punctured27NineSheetBridgeExact
-- and 13=3+6+4 / B3 cubic-axis finite diagnostics.
-- The signed quotient 26↔13×Bool below is a REAL two-sided
-- reconstruction of native points, not merely 26=2*13 numerology.
--
-- PG(2,3) is classical projective geometry on the same underlying
-- F3^3 additive grades; Griess Jr. 1990 separately supplies a graded
-- exceptional Albert algebra and Moufang loop. Shared underlying
-- points do NOT identify these products, representations, or physical
-- diamond axes. In particular F4 tracezero Q^26 is a VECTOR SPACE
-- and the original 26 spatial nonzero points are a FINITE SET.
-- New source-written Agda, kernel NOT run; no postulates.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact as Native
import DASHI.Wikimedia.IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact as Ibrahim

-- Canonical orientation: FIRST nonzero coordinate is +1.
-- Each constructor is an actual projective grade line, not an
-- arbitrary Fin13 imported from a distinct 13-object.
data Axis13 : Set where
  axisX axisY axisZ : Axis13
  faceXYpp faceXYpm faceXZpp faceXZpm faceYZpp faceYZpm : Axis13
  cornerPPP cornerPPM cornerPMP cornerPMM : Axis13

representative : Axis13 → Cube.Ternary27Point
representative .axisX = Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero
representative .axisY = Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero
representative .axisZ = Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne
representative .faceXYpp = Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero
representative .faceXYpm = Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero
representative .faceXZpp = Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne
representative .faceXZpm = Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne
representative .faceYZpp = Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne
representative .faceYZpm = Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne
representative .cornerPPP = Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne
representative .cornerPPM = Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne
representative .cornerPMP = Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne
representative .cornerPMM = Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne

-- Nine + three + one is the explicit canonical projective chart,
-- while 3+6+4 is the cubic support stratification (different partition).
axisFirst : SSP.SSPTrit → SSP.SSPTrit → Axis13
axisFirst SSP.sspNegOne SSP.sspNegOne = .cornerPMM
axisFirst SSP.sspNegOne SSP.sspZero = .faceXYpm
axisFirst SSP.sspNegOne SSP.sspPosOne = .cornerPMP
axisFirst SSP.sspZero SSP.sspNegOne = .faceXZpm
axisFirst SSP.sspZero SSP.sspZero = .axisX
axisFirst SSP.sspZero SSP.sspPosOne = .faceXZpp
axisFirst SSP.sspPosOne SSP.sspNegOne = .cornerPPM
axisFirst SSP.sspPosOne SSP.sspZero = .faceXYpp
axisFirst SSP.sspPosOne SSP.sspPosOne = .cornerPPP

axisSecond : SSP.SSPTrit → Axis13
axisSecond SSP.sspNegOne = .faceYZpm
axisSecond SSP.sspZero = .axisY
axisSecond SSP.sspPosOne = .faceYZpp

-- Uses THE original native #1249 antipode rather than duplicating it.
flipBit : Bool → Bool
flipBit true = false
flipBit false = true

decode : Axis13 × Bool → Cube.Ternary27Point
decode (a , false) = representative a
decode (a , true) = Native.antipode (representative a)

-- Undefined precisely at the one removed origin, not on any
-- other nine-sheet centre. The missing site is never defaulted.
encode : Cube.Ternary27Point → Maybe (Axis13 × Bool)
encode (Cube.ternary27Point SSP.sspPosOne y z) =
  just (axisFirst y z , false)
encode (Cube.ternary27Point SSP.sspNegOne y z) =
  just (axisFirst (Native.negateTrit y) (Native.negateTrit z) , true)
encode (Cube.ternary27Point SSP.sspZero SSP.sspPosOne z) =
  just (axisSecond z , false)
encode (Cube.ternary27Point SSP.sspZero SSP.sspNegOne z) =
  just (axisSecond (Native.negateTrit z) , true)
encode (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) =
  just (axisZ , false)
encode (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) =
  just (axisZ , true)
encode (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) =
  nothing

originExcluded : encode Cube.origin ≡ nothing
originExcluded = refl

-- Every one of the thirteen axes has TWO actual canonical orientations.
-- The 26 reflexive computations establish one direction constructively.
decodeEncode : (a : Axis13) (bit : Bool) →
  encode (decode (a , bit)) ≡ just (a , bit)
decodeEncode .axisX false = refl
decodeEncode .axisX true = refl
decodeEncode .axisY false = refl
decodeEncode .axisY true = refl
decodeEncode .axisZ false = refl
decodeEncode .axisZ true = refl
decodeEncode .faceXYpp false = refl
decodeEncode .faceXYpp true = refl
decodeEncode .faceXYpm false = refl
decodeEncode .faceXYpm true = refl
decodeEncode .faceXZpp false = refl
decodeEncode .faceXZpp true = refl
decodeEncode .faceXZpm false = refl
decodeEncode .faceXZpm true = refl
decodeEncode .faceYZpp false = refl
decodeEncode .faceYZpp true = refl
decodeEncode .faceYZpm false = refl
decodeEncode .faceYZpm true = refl
decodeEncode .cornerPPP false = refl
decodeEncode .cornerPPP true = refl
decodeEncode .cornerPPM false = refl
decodeEncode .cornerPPM true = refl
decodeEncode .cornerPMP false = refl
decodeEncode .cornerPMP true = refl
decodeEncode .cornerPMM false = refl
decodeEncode .cornerPMM true = refl

-- The converse is a proof over the actual 27 native cube constructors.
-- It explicitly rejects the one absent site; neither 9-plane is
-- spuriously punctured at its own outer-sheet centre.
encodeSound : (p : Cube.Ternary27Point)
  (a : Axis13) (bit : Bool) →
  encode p ≡ just (a , bit) → decode (a , bit) ≡ p
encodeSound (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) a b ()
encodeSound (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) a b refl = refl
encodeSound (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) a b refl = refl

-- The true source antipode fixes the PROJECTIVE point and flips
-- the recoverable sign residual; contrast a false scalar quotient.
encodeAntipode : (p : Cube.Ternary27Point)
  (a : Axis13) (bit : Bool) →
  encode p ≡ just (a , bit) →
  encode (Native.antipode p) ≡ just (a , flipBit bit)
encodeAntipode (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) a b refl = refl
encodeAntipode (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) a b ()

supportSize : Axis13 → Nat
supportSize .axisX = 1
supportSize .axisY = 1
supportSize .axisZ = 1
supportSize .faceXYpp = 2
supportSize .faceXYpm = 2
supportSize .faceXZpp = 2
supportSize .faceXZpm = 2
supportSize .faceYZpp = 2
supportSize .faceYZpm = 2
supportSize .cornerPPP = 3
supportSize .cornerPPM = 3
supportSize .cornerPMP = 3
supportSize .cornerPMM = 3

exactThirteenBySupport : 13 ≡ 3 + 6 + 4
exactThirteenBySupport = refl

twoOrientedForEachUnoriented : 26 ≡ 2 * 13
twoOrientedForEachUnoriented = Ibrahim.twentySixAsTwoThirteen

puncturedThreeSheetCount : 26 ≡ 9 + 8 + 9
puncturedThreeSheetCount = refl

-- Still distinct: original graph edges and spatial XOR sign holonomy,
-- full PG(2,3) incidence and SL3 label normalizer, native Jordan
-- product/traceless-26 vector action, crystal NV Hamiltonian, Monster VOA.
-- Companion exact Python proves quotient graph 13v/24e and a
-- nontrivial four-cycle Z2 holonomy; no global all-edge oriented
-- quotient section is licensed by a 26↔13×2 set bijection.

-- Concrete actual-source four-cycle in the quotient spatial graph:
--  axisX -- faceXYpp -- axisY -- faceXYpm -- axisX.
-- Along the third edge only, the destination must be NEGATED.
-- These are native P3^3 graph adjacency witnesses from ORIGINAL Cube;
-- no synthetic edge relation has been invented.
edgeAxisXFacePP : Cube.HypervoxelAdjacent
  (representative axisX) (representative faceXYpp)
edgeAxisXFacePP = Cube.adjacentY Cube.zeroToPos

edgeFacePPAxisY : Cube.HypervoxelAdjacent
  (representative faceXYpp) (representative axisY)
edgeFacePPAxisY = Cube.adjacentX Cube.posToZero

edgeAxisYNegFacePM : Cube.HypervoxelAdjacent
  (representative axisY) (Native.antipode (representative faceXYpm))
edgeAxisYNegFacePM = Cube.adjacentX Cube.zeroToNeg

edgeFacePMAxisX : Cube.HypervoxelAdjacent
  (representative faceXYpm) (representative axisX)
edgeFacePMAxisX = Cube.adjacentY Cube.negToZero

-- This is the BINARY orientation/residual XOR, not an alternative
-- F3 addition, complex phases or a physical gauge field.
infixl 7 _xor_
_xor_ : Bool → Bool → Bool
false xor false = false
false xor true = true
true xor false = true
true xor true = false

-- All 16 possible global sign assignments to the four distinct
-- projective axes fail at least one SOURCE-SELECTED adjacency lift:
-- bits along the four quotient edges must be 0,0,1,0.
-- Their total holonomy is odd, so the signed 26-site covering
-- graph does NOT admit a globally edge-compatible orientation
-- section (despite a two-sided 26↔13×Bool POINT-SET bijection).
noEdgeCompatibleOrientation : (sX sPP sY sPM : Bool) →
  (sX xor sPP) ≡ false →
  (sPP xor sY) ≡ false →
  (sY xor sPM) ≡ true →
  (sPM xor sX) ≡ false → ⊥
noEdgeCompatibleOrientation false false false false h₀ h₁ () h₃
noEdgeCompatibleOrientation false false false true h₀ h₁ h₂ ()
noEdgeCompatibleOrientation false false true false h₀ () h₂ h₃
noEdgeCompatibleOrientation false false true true h₀ () h₂ h₃
noEdgeCompatibleOrientation false true false false () h₁ h₂ h₃
noEdgeCompatibleOrientation false true false true () h₁ h₂ h₃
noEdgeCompatibleOrientation false true true false () h₁ h₂ h₃
noEdgeCompatibleOrientation false true true true () h₁ h₂ h₃
noEdgeCompatibleOrientation true false false false () h₁ h₂ h₃
noEdgeCompatibleOrientation true false false true () h₁ h₂ h₃
noEdgeCompatibleOrientation true false true false () h₁ h₂ h₃
noEdgeCompatibleOrientation true false true true () h₁ h₂ h₃
noEdgeCompatibleOrientation true true false false h₀ () h₂ h₃
noEdgeCompatibleOrientation true true false true h₀ () h₂ h₃
noEdgeCompatibleOrientation true true true false h₀ h₁ h₂ ()
noEdgeCompatibleOrientation true true true true h₀ h₁ () h₃

-- The obstruction applies to the original P3^3 adjacency/gluing.
-- It is not a claim about actual physical diamond NV defects,
-- experimental vortices, a two-form gauge flux, full sheaf theory,
-- or the Griess rational Albert algebra/Monster VOA product.


-- 2026-10-26 P0: the XOR voltage constraints are DERIVED from
-- *actual native Cube.HypervoxelAdjacent* at each of the four
-- projective edges. Earlier noEdgeCompatibleOrientation was a
-- correct Boolean impossibility but did not itself discharge this
-- real-graph-to-Boolean acceptance join.
--
-- For a fixed canonical axis pair, TWO signs produce an actual native
-- path edge. The other TWO signs are definitionally impossible from
-- the source edge constructors; () eliminates those cases.  This is
-- the precise local-graph-cover voltage interpretation (Gross 1974,
-- Gross--Tucker 1977), no physical electromagnetic gauge claimed.

spatialEdgeBitXFacePP : (s t : Bool) →
  Cube.HypervoxelAdjacent (decode (axisX , s)) (decode (faceXYpp , t)) →
  (s xor t) ≡ false
spatialEdgeBitXFacePP false false _ = refl
spatialEdgeBitXFacePP false true ()
spatialEdgeBitXFacePP true false ()
spatialEdgeBitXFacePP true true _ = refl

spatialEdgeBitFacePPAxisY : (s t : Bool) →
  Cube.HypervoxelAdjacent (decode (faceXYpp , s)) (decode (axisY , t)) →
  (s xor t) ≡ false
spatialEdgeBitFacePPAxisY false false _ = refl
spatialEdgeBitFacePPAxisY false true ()
spatialEdgeBitFacePPAxisY true false ()
spatialEdgeBitFacePPAxisY true true _ = refl

spatialEdgeBitAxisYFacePM : (s t : Bool) →
  Cube.HypervoxelAdjacent (decode (axisY , s)) (decode (faceXYpm , t)) →
  (s xor t) ≡ true
spatialEdgeBitAxisYFacePM false false ()
spatialEdgeBitAxisYFacePM false true _ = refl
spatialEdgeBitAxisYFacePM true false _ = refl
spatialEdgeBitAxisYFacePM true true ()

spatialEdgeBitFacePMAxisX : (s t : Bool) →
  Cube.HypervoxelAdjacent (decode (faceXYpm , s)) (decode (axisX , t)) →
  (s xor t) ≡ false
spatialEdgeBitFacePMAxisX false false _ = refl
spatialEdgeBitFacePMAxisX false true ()
spatialEdgeBitFacePMAxisX true false ()
spatialEdgeBitFacePMAxisX true true _ = refl

-- This theorem now rejects an actual global sign SECTION that
-- preserves all four source-selected native adjacency edges.
-- No assumptions of an artificial P3^3 graph relation are supplied.
noSpatialSectionOnNativeFourCycle :
  (sX sPP sY sPM : Bool) →
  Cube.HypervoxelAdjacent
    (decode (axisX , sX)) (decode (faceXYpp , sPP)) →
  Cube.HypervoxelAdjacent
    (decode (faceXYpp , sPP)) (decode (axisY , sY)) →
  Cube.HypervoxelAdjacent
    (decode (axisY , sY)) (decode (faceXYpm , sPM)) →
  Cube.HypervoxelAdjacent
    (decode (faceXYpm , sPM)) (decode (axisX , sX)) →
  ⊥
noSpatialSectionOnNativeFourCycle sX sPP sY sPM e1 e2 e3 e4 =
  noEdgeCompatibleOrientation sX sPP sY sPM
    (spatialEdgeBitXFacePP sX sPP e1)
    (spatialEdgeBitFacePPAxisY sPP sY e2)
    (spatialEdgeBitAxisYFacePM sY sPM e3)
    (spatialEdgeBitFacePMAxisX sPM sX e4)

-- Agda source written only; kernel compilation pending. The four
-- native adjacency predicates and the explicit sign transitions
-- were independently enumerated in exact local Python.
