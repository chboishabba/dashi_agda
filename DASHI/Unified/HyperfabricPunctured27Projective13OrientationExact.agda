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
encodeSound Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero a b refl = refl
encodeSound Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero a b refl = refl
encodeSound Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero a b refl = refl
encodeSound Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero a b refl = refl
encodeSound Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero a b ()
encodeSound Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero a b refl = refl
encodeSound Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero a b refl = refl
encodeSound Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero a b refl = refl
encodeSound Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne a b refl = refl
encodeSound Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero a b refl = refl
encodeSound Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne a b refl = refl

-- The true source antipode fixes the PROJECTIVE point and flips
-- the recoverable sign residual; contrast a false scalar quotient.
encodeAntipode : (p : Cube.Ternary27Point)
  (a : Axis13) (bit : Bool) →
  encode p ≡ just (a , bit) →
  encode (Native.antipode p) ≡ just (a , flipBit bit)
encodeAntipode Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne a b refl = refl
encodeAntipode Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero a b ()

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
