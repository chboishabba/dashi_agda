module DASHI.Analysis.RHFourWindowC26NativeHyperfabricSquareExact where

-- Sourced finite hyperfabric / RH crosswalk, not new trit/cube/C13 owners.
-- True original native P3^3 grades and native 13-axis+orientation codec:
--  DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact
-- Original Griess grade word (e01,e12,e20):
--  DASHI.Moonshine.Griess1990MoufangCoherentSL3SectionSourceExact
-- Original RH full-source 4->3->5 trace:
--  DASHI.Analysis.RHFourWindowBiharmonicFiniteCubeExact
-- Original H05 8 vertices / 12 arrows / SIX face witness types:
--  DASHI.Core.GovernedIndexedResidualCubeExact
-- All 26 native cases are source-written, NOT AGDA KERNEL ACCEPTED.
-- This cube's third axis is a genuine nonidentity grade permutation,
-- but its action on RH Source4 is IDENTITY, with no actual zeta transport.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact as Native
import DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact as P
import DASHI.Moonshine.Griess1990MoufangCoherentSL3SectionSourceExact as Sah
import DASHI.Analysis.RHFourWindowBiharmonicFiniteCubeExact as RH
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Core.GovernedDiagramCore as Diagram

Code26 : Set
Code26 = P.Axis13 × Bool

-- Actual grade action, not the derived cycle on anonymous Fin 26.
gradeOrder13 : Cube.Ternary27Point → Cube.Ternary27Point
gradeOrder13 p =
  Sah.gradeShear Sah.e20
    (Sah.gradeShear Sah.e12 (Sah.gradeShear Sah.e01 p))

gradeOrder26 : Cube.Ternary27Point → Cube.Ternary27Point
gradeOrder26 p = Native.antipode (gradeOrder13 p)

-- Total native 26-case transport, computed from the original canonical
-- first-nonzero-positive projective-axis representatives.
codeStep : Code26 → Code26
codeStep (P.axisX , false) = P.faceXZpp , true
codeStep (P.axisX , true) = P.faceXZpp , false
codeStep (P.axisY , false) = P.cornerPPP , true
codeStep (P.axisY , true) = P.cornerPPP , false
codeStep (P.axisZ , false) = P.faceYZpp , true
codeStep (P.axisZ , true) = P.faceYZpp , false
codeStep (P.faceXYpp , false) = P.cornerPMP , false
codeStep (P.faceXYpp , true) = P.cornerPMP , true
codeStep (P.faceXYpm , false) = P.axisY , false
codeStep (P.faceXYpm , true) = P.axisY , true
codeStep (P.faceXZpp , false) = P.cornerPPM , true
codeStep (P.faceXZpp , true) = P.cornerPPM , false
codeStep (P.faceXZpm , false) = P.faceXYpm , true
codeStep (P.faceXZpm , true) = P.faceXYpm , false
codeStep (P.faceYZpp , false) = P.cornerPMM , true
codeStep (P.faceYZpp , true) = P.cornerPMM , false
codeStep (P.faceYZpm , false) = P.axisX , true
codeStep (P.faceYZpm , true) = P.axisX , false
codeStep (P.cornerPPP , false) = P.faceXYpp , false
codeStep (P.cornerPPP , true) = P.faceXYpp , true
codeStep (P.cornerPPM , false) = P.faceXZpm , false
codeStep (P.cornerPPM , true) = P.faceXZpm , true
codeStep (P.cornerPMP , false) = P.axisZ , true
codeStep (P.cornerPMP , true) = P.axisZ , false
codeStep (P.cornerPMM , false) = P.faceYZpm , true
codeStep (P.cornerPMM , true) = P.faceYZpm , false

-- The genuinely NONTRIVIAL commuting square:
-- encode o gradeOrder26 o decode = just o codeStep,
-- and decode o codeStep = gradeOrder26 o decode.
-- This preserves both axis and sign; a bare axis map does not suffice.
codeStepEncodeSource : (a : P.Axis13) (bit : Bool) →
  P.encode (gradeOrder26 (P.decode (a , bit))) ≡
    just (codeStep (a , bit))
codeStepEncodeSource P.axisX false = refl
codeStepEncodeSource P.axisX true = refl
codeStepEncodeSource P.axisY false = refl
codeStepEncodeSource P.axisY true = refl
codeStepEncodeSource P.axisZ false = refl
codeStepEncodeSource P.axisZ true = refl
codeStepEncodeSource P.faceXYpp false = refl
codeStepEncodeSource P.faceXYpp true = refl
codeStepEncodeSource P.faceXYpm false = refl
codeStepEncodeSource P.faceXYpm true = refl
codeStepEncodeSource P.faceXZpp false = refl
codeStepEncodeSource P.faceXZpp true = refl
codeStepEncodeSource P.faceXZpm false = refl
codeStepEncodeSource P.faceXZpm true = refl
codeStepEncodeSource P.faceYZpp false = refl
codeStepEncodeSource P.faceYZpp true = refl
codeStepEncodeSource P.faceYZpm false = refl
codeStepEncodeSource P.faceYZpm true = refl
codeStepEncodeSource P.cornerPPP false = refl
codeStepEncodeSource P.cornerPPP true = refl
codeStepEncodeSource P.cornerPPM false = refl
codeStepEncodeSource P.cornerPPM true = refl
codeStepEncodeSource P.cornerPMP false = refl
codeStepEncodeSource P.cornerPMP true = refl
codeStepEncodeSource P.cornerPMM false = refl
codeStepEncodeSource P.cornerPMM true = refl

codeStepDecodeSource : (a : P.Axis13) (bit : Bool) →
  P.decode (codeStep (a , bit)) ≡
    gradeOrder26 (P.decode (a , bit))
codeStepDecodeSource P.axisX false = refl
codeStepDecodeSource P.axisX true = refl
codeStepDecodeSource P.axisY false = refl
codeStepDecodeSource P.axisY true = refl
codeStepDecodeSource P.axisZ false = refl
codeStepDecodeSource P.axisZ true = refl
codeStepDecodeSource P.faceXYpp false = refl
codeStepDecodeSource P.faceXYpp true = refl
codeStepDecodeSource P.faceXYpm false = refl
codeStepDecodeSource P.faceXYpm true = refl
codeStepDecodeSource P.faceXZpp false = refl
codeStepDecodeSource P.faceXZpp true = refl
codeStepDecodeSource P.faceXZpm false = refl
codeStepDecodeSource P.faceXZpm true = refl
codeStepDecodeSource P.faceYZpp false = refl
codeStepDecodeSource P.faceYZpp true = refl
codeStepDecodeSource P.faceYZpm false = refl
codeStepDecodeSource P.faceYZpm true = refl
codeStepDecodeSource P.cornerPPP false = refl
codeStepDecodeSource P.cornerPPP true = refl
codeStepDecodeSource P.cornerPPM false = refl
codeStepDecodeSource P.cornerPPM true = refl
codeStepDecodeSource P.cornerPMP false = refl
codeStepDecodeSource P.cornerPMP true = refl
codeStepDecodeSource P.cornerPMM false = refl
codeStepDecodeSource P.cornerPMM true = refl

iterateCode : Nat → Code26 → Code26
iterateCode zero c = c
iterateCode (suc n) c = codeStep (iterateCode n c)

-- After thirteen genuine grade steps the axis returns, orientation
-- changes; after twenty-six it returns as an ORIENTED source.
thirteenStepsFlip : (a : P.Axis13) (bit : Bool) →
  iterateCode 13 (a , bit) ≡ (a , P.flipBit bit)
thirteenStepsFlip P.axisX false = refl
thirteenStepsFlip P.axisX true = refl
thirteenStepsFlip P.axisY false = refl
thirteenStepsFlip P.axisY true = refl
thirteenStepsFlip P.axisZ false = refl
thirteenStepsFlip P.axisZ true = refl
thirteenStepsFlip P.faceXYpp false = refl
thirteenStepsFlip P.faceXYpp true = refl
thirteenStepsFlip P.faceXYpm false = refl
thirteenStepsFlip P.faceXYpm true = refl
thirteenStepsFlip P.faceXZpp false = refl
thirteenStepsFlip P.faceXZpp true = refl
thirteenStepsFlip P.faceXZpm false = refl
thirteenStepsFlip P.faceXZpm true = refl
thirteenStepsFlip P.faceYZpp false = refl
thirteenStepsFlip P.faceYZpp true = refl
thirteenStepsFlip P.faceYZpm false = refl
thirteenStepsFlip P.faceYZpm true = refl
thirteenStepsFlip P.cornerPPP false = refl
thirteenStepsFlip P.cornerPPP true = refl
thirteenStepsFlip P.cornerPPM false = refl
thirteenStepsFlip P.cornerPPM true = refl
thirteenStepsFlip P.cornerPMP false = refl
thirteenStepsFlip P.cornerPMP true = refl
thirteenStepsFlip P.cornerPMM false = refl
thirteenStepsFlip P.cornerPMM true = refl

twentySixStepsReturn : (a : P.Axis13) (bit : Bool) →
  iterateCode 26 (a , bit) ≡ (a , bit)
twentySixStepsReturn P.axisX false = refl
twentySixStepsReturn P.axisX true = refl
twentySixStepsReturn P.axisY false = refl
twentySixStepsReturn P.axisY true = refl
twentySixStepsReturn P.axisZ false = refl
twentySixStepsReturn P.axisZ true = refl
twentySixStepsReturn P.faceXYpp false = refl
twentySixStepsReturn P.faceXYpp true = refl
twentySixStepsReturn P.faceXYpm false = refl
twentySixStepsReturn P.faceXYpm true = refl
twentySixStepsReturn P.faceXZpp false = refl
twentySixStepsReturn P.faceXZpp true = refl
twentySixStepsReturn P.faceXZpm false = refl
twentySixStepsReturn P.faceXZpm true = refl
twentySixStepsReturn P.faceYZpp false = refl
twentySixStepsReturn P.faceYZpp true = refl
twentySixStepsReturn P.faceYZpm false = refl
twentySixStepsReturn P.faceYZpm true = refl
twentySixStepsReturn P.cornerPPP false = refl
twentySixStepsReturn P.cornerPPP true = refl
twentySixStepsReturn P.cornerPPM false = refl
twentySixStepsReturn P.cornerPPM true = refl
twentySixStepsReturn P.cornerPMP false = refl
twentySixStepsReturn P.cornerPMP true = refl
twentySixStepsReturn P.cornerPMM false = refl
twentySixStepsReturn P.cornerPMM true = refl

-- The genuine Griess order26 grade actor satisfies its irreducible
-- GF(3) cubic X³-X+1 on the SAME original 27-point carrier.
-- Finite-field interpretation uses a cyclic basis: the source is
-- GF(27)^× as a regular C26 permutation, not the original P3^3 metric.
-- The native GF(3) arithmetic owner is the original Griess module.
import DASHI.Moonshine.Griess1990Moufang81IbrahimProjective13Exact as Griess
import DASHI.Foundations.SSPTritCarrier as SSP

addGrade : Cube.Ternary27Point → Cube.Ternary27Point → Cube.Ternary27Point
addGrade (Cube.ternary27Point x y z) (Cube.ternary27Point a b c) =
  Cube.ternary27Point (Griess.add3 x a) (Griess.add3 y b) (Griess.add3 z c)

subGrade : Cube.Ternary27Point → Cube.Ternary27Point → Cube.Ternary27Point
subGrade (Cube.ternary27Point x y z) (Cube.ternary27Point a b c) =
  Cube.ternary27Point (Griess.sub3 x a) (Griess.sub3 y b) (Griess.sub3 z c)

sourceFieldPolynomial : (x y z : SSP.SSPTrit) →
  addGrade
    (subGrade
      (gradeOrder26 (gradeOrder26
        (gradeOrder26 (Cube.ternary27Point x y z))))
      (gradeOrder26 (Cube.ternary27Point x y z)))
    (Cube.ternary27Point x y z)
  ≡ Cube.origin
sourceFieldPolynomial SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne = refl
sourceFieldPolynomial SSP.sspNegOne SSP.sspNegOne SSP.sspZero = refl
sourceFieldPolynomial SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne = refl
sourceFieldPolynomial SSP.sspNegOne SSP.sspZero SSP.sspNegOne = refl
sourceFieldPolynomial SSP.sspNegOne SSP.sspZero SSP.sspZero = refl
sourceFieldPolynomial SSP.sspNegOne SSP.sspZero SSP.sspPosOne = refl
sourceFieldPolynomial SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne = refl
sourceFieldPolynomial SSP.sspNegOne SSP.sspPosOne SSP.sspZero = refl
sourceFieldPolynomial SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne = refl
sourceFieldPolynomial SSP.sspZero SSP.sspNegOne SSP.sspNegOne = refl
sourceFieldPolynomial SSP.sspZero SSP.sspNegOne SSP.sspZero = refl
sourceFieldPolynomial SSP.sspZero SSP.sspNegOne SSP.sspPosOne = refl
sourceFieldPolynomial SSP.sspZero SSP.sspZero SSP.sspNegOne = refl
sourceFieldPolynomial SSP.sspZero SSP.sspZero SSP.sspZero = refl
sourceFieldPolynomial SSP.sspZero SSP.sspZero SSP.sspPosOne = refl
sourceFieldPolynomial SSP.sspZero SSP.sspPosOne SSP.sspNegOne = refl
sourceFieldPolynomial SSP.sspZero SSP.sspPosOne SSP.sspZero = refl
sourceFieldPolynomial SSP.sspZero SSP.sspPosOne SSP.sspPosOne = refl
sourceFieldPolynomial SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne = refl
sourceFieldPolynomial SSP.sspPosOne SSP.sspNegOne SSP.sspZero = refl
sourceFieldPolynomial SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne = refl
sourceFieldPolynomial SSP.sspPosOne SSP.sspZero SSP.sspNegOne = refl
sourceFieldPolynomial SSP.sspPosOne SSP.sspZero SSP.sspZero = refl
sourceFieldPolynomial SSP.sspPosOne SSP.sspZero SSP.sspPosOne = refl
sourceFieldPolynomial SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne = refl
sourceFieldPolynomial SSP.sspPosOne SSP.sspPosOne SSP.sspZero = refl
sourceFieldPolynomial SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne = refl

-- Exact tensor-like source interface; no erased residual/source coordinates.
Raw : Set
Raw = Code26 × RH.Source4

Fold : Set
Fold = Code26 × RH.TracedFold

Five : Set
Five = Code26 × RH.TracedFive

project : Raw → Fold
project (code , raw) = code , RH.projectWithSource raw

direct : Raw → Five
direct (code , raw) = code , RH.directWithSource raw

unfold : Fold → Five
unfold (code , folded) = code , RH.unfoldWithSource folded

moveRaw : Raw → Raw
moveRaw (code , raw) = codeStep code , raw

moveFold : Fold → Fold
moveFold (code , folded) = codeStep code , folded

moveFive : Five → Five
moveFive (code , five) = codeStep code , five

-- H05 z-axis is NOW NONIDENTITY: actual signed 26-cycle. Each
-- x/y square is the actual RH traced projection-unfolding identity.
-- x/z and y/z are naturality of RH with the grade phase action.
-- No analytic RH zeros/mu/FarExact are acted on here.
nativeC26H05Cube : Q.Cube
nativeC26H05Cube = record
  { A = Raw ; B = Fold ; C = Five ; D = Five
  ; E = Raw ; F = Fold ; H = Five ; I = Five
  ; x00 = project ; x10 = λ x → x
  ; x01 = project ; x11 = λ x → x
  ; y00 = direct ; y10 = unfold
  ; y01 = direct ; y11 = unfold
  ; z00 = moveRaw ; z10 = moveFold
  ; z01 = moveFive ; z11 = moveFive
  }

nativeC26ResidualFaces : Q.Faces nativeC26H05Cube
nativeC26ResidualFaces = record
  { Rxy0 = λ _ → ⊤ ; Rxz0 = λ _ → ⊤ ; Ryz0 = λ _ → ⊤
  ; Rxy1 = λ _ → ⊤ ; Rxz1 = λ _ → ⊤ ; Ryz1 = λ _ → ⊤
  }

nativeC26ExactFaces :
  Q.ExactFaces nativeC26H05Cube nativeC26ResidualFaces
nativeC26ExactFaces = record
  { pxy0 = Diagram.commutingSquareWitness
      (λ { (code , RH.source4 c l r cancel inner outer) → refl })
  ; pxz0 = Diagram.commutingSquareWitness (λ _ → refl)
  ; pyz0 = Diagram.commutingSquareWitness (λ _ → refl)
  ; pxy1 = Diagram.commutingSquareWitness
      (λ { (code , RH.source4 c l r cancel inner outer) → refl })
  ; pxz1 = Diagram.commutingSquareWitness (λ _ → refl)
  ; pyz1 = Diagram.commutingSquareWitness (λ _ → refl)
  }

nativeC26SixPathAgreement : (state : Raw) →
  Q.xyz nativeC26H05Cube state ≡
    Q.zyx nativeC26H05Cube state
nativeC26SixPathAgreement =
  Q.xyz-zyx nativeC26ExactFaces

-- Backward recoverability. The true grade changes, while the WHOLE
-- source with raw pi/3 cancellation record is retained as stored.
recoverRaw : Five → Raw
recoverRaw (c , five) = c , RH.originalFiveSource five

recoverAfterDirect : (state : Raw) →
  recoverRaw (direct state) ≡ state
recoverAfterDirect (c , RH.source4 a l r cancel inner outer) = refl

recoverAfterFold : (state : Raw) →
  recoverRaw (unfold (project state)) ≡ state
recoverAfterFold (c , RH.source4 a l r cancel inner outer) = refl

recoverAfterMove : (state : Raw) →
  recoverRaw (moveFive (direct state)) ≡ moveRaw state
recoverAfterMove (c , RH.source4 a l r cancel inner outer) = refl

-- The H05 index, sign, residual, mode and observed-zero tags are
-- independently typed, unchanged by the native C26 grade action.
indexedMove :
  ∀ {Index Sign Residual Mode Observation : Set} →
  RH.IndexedSource Index Sign Residual Mode Observation Raw →
  RH.IndexedSource Index Sign Residual Mode Observation Raw
indexedMove = RH.mapIndexedPayload moveRaw

indexedPreservesMetadata :
  ∀ {Index Sign Residual Mode Observation : Set}
  (record : RH.IndexedSource Index Sign Residual Mode Observation Raw) →
  RH.index (indexedMove record) ≡ RH.index record
indexedPreservesMetadata (RH.indexedSource k s r m o x) = refl

indexedPreservesSign :
  ∀ {Index Sign Residual Mode Observation : Set}
  (record : RH.IndexedSource Index Sign Residual Mode Observation Raw) →
  RH.sign (indexedMove record) ≡ RH.sign record
indexedPreservesSign (RH.indexedSource k s r m o x) = refl

indexedPreservesResidual :
  ∀ {Index Sign Residual Mode Observation : Set}
  (record : RH.IndexedSource Index Sign Residual Mode Observation Raw) →
  RH.residual (indexedMove record) ≡ RH.residual record
indexedPreservesResidual (RH.indexedSource k s r m o x) = refl

indexedPreservesObservation :
  ∀ {Index Sign Residual Mode Observation : Set}
  (record : RH.IndexedSource Index Sign Residual Mode Observation Raw) →
  RH.observation (indexedMove record) ≡ RH.observation record
indexedPreservesObservation (RH.indexedSource k s r m o x) = refl

-- Source example uses nonzero (24,24) cancellation, NOT empty pi/3.
nativeExample : Raw
nativeExample = (P.axisX , false) , RH.sampleFour

nativeExampleMoves :
  moveRaw nativeExample ≡
    ((P.faceXZpp , true) , RH.sampleFour)
nativeExampleMoves = refl

nativeThirteenExample :
  iterateCode 13 (P.axisX , false) ≡ (P.axisX , true)
nativeThirteenExample = thirteenStepsFlip P.axisX false

-- NOT PAID: true nine-DOF H07 chart/isometry, native P3^3 graph
-- adjacency transport, signed FarExact analytic generator, original
-- zeta zero/mu compensation or any RH/GRH terminal.
