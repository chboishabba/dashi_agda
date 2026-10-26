module DASHI.Moonshine.Griess1990MoufangCoherentSL3SectionSourceExact where

-- Direct SAME-OWNER Agda model of the constructed Griess M81 source
-- SL3(3) complement, *NOT* a new 81-point carrier or invented action.
--
-- Original mathematical priority: Chih-Han Sah, J Algebra 29 (1974),
-- 255--302 (Griess credits prior work); R. L. Griess Jr,
-- Pacific J Math 63 (1976) 405--409, DOI 10.2140/pjm.1976.63.405;
-- Robert L. Griess Jr, J Algebra 131 (1990) 281--293,
-- DOI 10.1016/0021-8693(90)90176-O, source g and Jordan product.
--
-- Locally executed exact finite certificate: 18 F3 variables,
-- rank15, 5616 grade transforms, 33696 generator transitions,
-- 758187 exact linear equations, 27 kernel-conjugate solutions;
-- six corrected source lifts generate EXACT subgroup of order5616
-- in Aut(the ORIGINAL Griess 81-loop), and preserve all 6×729
-- original tau-real Albert Jordan basis products. No claimed
-- Agda/Lake kernel proof, selected Monster VOA or physical graph.
--
-- The finite 81-case same-row relation below is SOURCE WRITTEN,
-- not an Agda kernel execution receipt.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Moonshine.Griess1990Moufang81IbrahimProjective13Exact as Griess

data Shear : Set where
  e01 e02 e10 e12 e20 e21 : Shear

gradeShear : Shear → Griess.V27 → Griess.V27
gradeShear e01 (Cube.ternary27Point x y z) =
  Cube.ternary27Point (Griess.add3 x y) y z
gradeShear e02 (Cube.ternary27Point x y z) =
  Cube.ternary27Point (Griess.add3 x z) y z
gradeShear e10 (Cube.ternary27Point x y z) =
  Cube.ternary27Point x (Griess.add3 y x) z
gradeShear e12 (Cube.ternary27Point x y z) =
  Cube.ternary27Point x (Griess.add3 y z) z
gradeShear e20 (Cube.ternary27Point x y z) =
  Cube.ternary27Point x y (Griess.add3 z x)
gradeShear e21 (Cube.ternary27Point x y z) =
  Cube.ternary27Point x y (Griess.add3 z y)

sourcePhase : Shear → Griess.V27 → Griess.F3
sourcePhase e01 (Cube.ternary27Point x y z) =
  Griess.mul3 z (Griess.sub3 SSP.sspPosOne (Griess.mul3 y y))
sourcePhase e02 _ = SSP.sspZero
sourcePhase e10 (Cube.ternary27Point x y z) =
  Griess.mul3 z (Griess.sub3 SSP.sspPosOne (Griess.mul3 x x))
sourcePhase e12 (Cube.ternary27Point x y z) =
  Griess.mul3 x (Griess.sub3 (Griess.mul3 z z) SSP.sspPosOne)
sourcePhase e20 _ = SSP.sspZero
sourcePhase e21 (Cube.ternary27Point x y z) =
  Griess.mul3 x (Griess.sub3 (Griess.mul3 y y) SSP.sspPosOne)

-- EXACT solver-produced left-kernel characters; coordinates x,y,z:
-- e01 (0,0,0), e02 (0,-1,0), e10 (0,0,+1),
-- e12 (-1,0,0), e20 (0,+1,0), e21 (0,0,0).
sectionCharacter : Shear → Griess.V27
sectionCharacter e01 = Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero
sectionCharacter e02 = Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero
sectionCharacter e10 = Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne
sectionCharacter e12 = Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero
sectionCharacter e20 = Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero
sectionCharacter e21 = Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero

dot3 : Griess.V27 → Griess.V27 → Griess.F3
dot3 p q =
  Griess.add3 (Griess.mul3 (Cube.x p) (Cube.x q))
    (Griess.add3 (Griess.mul3 (Cube.y p) (Cube.y q))
      (Griess.mul3 (Cube.z p) (Cube.z q)))

coherentLift : Shear → Griess.M81 → Griess.M81
coherentLift s (p , c) =
  (gradeShear s p ,
   Griess.add3 c
     (Griess.add3 (sourcePhase s p)
       (dot3 (sectionCharacter s) (gradeShear s p))))

coherentInverse : Shear → Griess.M81 → Griess.M81
coherentInverse s m = coherentLift s (coherentLift s m)

unitFixed01 : coherentLift e01 Griess.moufangIdentity ≡ Griess.moufangIdentity
unitFixed01 = refl

unitFixed20 : coherentLift e20 Griess.moufangIdentity ≡ Griess.moufangIdentity
unitFixed20 = refl

-- Example separating the NEW coherent e20 from the older e20 with
-- zero phase: the unchanged grade y-axis acquires central +1.
coherentE20CentralPhase :
  coherentLift e20 (Griess.yAxis , SSP.sspZero) ≡
    (Griess.yAxis , SSP.sspPosOne)
coherentE20CentralPhase = refl

coherentE02CentralPhase :
  coherentLift e02 (Griess.yAxis , SSP.sspZero) ≡
    (Griess.yAxis , SSP.sspNegOne)
coherentE02CentralPhase = refl

-- Full source-same action commutation relation: e01 e02 = e02 e01
-- checked constructively by 81 native constructor reductions.
sameRowCommutes : (x y z c : Griess.F3) →
  coherentLift e01
    (coherentLift e02 (Cube.ternary27Point x y z , c)) ≡
  coherentLift e02
    (coherentLift e01 (Cube.ternary27Point x y z , c))
sameRowCommutes SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne SSP.sspZero = refl
sameRowCommutes SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspNegOne SSP.sspZero SSP.sspNegOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspNegOne SSP.sspZero SSP.sspZero = refl
sameRowCommutes SSP.sspNegOne SSP.sspNegOne SSP.sspZero SSP.sspPosOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne SSP.sspZero = refl
sameRowCommutes SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspZero SSP.sspNegOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspZero SSP.sspNegOne SSP.sspZero = refl
sameRowCommutes SSP.sspNegOne SSP.sspZero SSP.sspNegOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspZero SSP.sspZero SSP.sspNegOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspZero SSP.sspZero SSP.sspZero = refl
sameRowCommutes SSP.sspNegOne SSP.sspZero SSP.sspZero SSP.sspPosOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspZero SSP.sspPosOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspZero SSP.sspPosOne SSP.sspZero = refl
sameRowCommutes SSP.sspNegOne SSP.sspZero SSP.sspPosOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne SSP.sspZero = refl
sameRowCommutes SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspPosOne SSP.sspZero SSP.sspNegOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspPosOne SSP.sspZero SSP.sspZero = refl
sameRowCommutes SSP.sspNegOne SSP.sspPosOne SSP.sspZero SSP.sspPosOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne SSP.sspZero = refl
sameRowCommutes SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspZero SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspZero SSP.sspNegOne SSP.sspNegOne SSP.sspZero = refl
sameRowCommutes SSP.sspZero SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspZero SSP.sspNegOne SSP.sspZero SSP.sspNegOne = refl
sameRowCommutes SSP.sspZero SSP.sspNegOne SSP.sspZero SSP.sspZero = refl
sameRowCommutes SSP.sspZero SSP.sspNegOne SSP.sspZero SSP.sspPosOne = refl
sameRowCommutes SSP.sspZero SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspZero SSP.sspNegOne SSP.sspPosOne SSP.sspZero = refl
sameRowCommutes SSP.sspZero SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspZero SSP.sspZero SSP.sspNegOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspZero SSP.sspZero SSP.sspNegOne SSP.sspZero = refl
sameRowCommutes SSP.sspZero SSP.sspZero SSP.sspNegOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspZero SSP.sspZero SSP.sspZero SSP.sspNegOne = refl
sameRowCommutes SSP.sspZero SSP.sspZero SSP.sspZero SSP.sspZero = refl
sameRowCommutes SSP.sspZero SSP.sspZero SSP.sspZero SSP.sspPosOne = refl
sameRowCommutes SSP.sspZero SSP.sspZero SSP.sspPosOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspZero SSP.sspZero SSP.sspPosOne SSP.sspZero = refl
sameRowCommutes SSP.sspZero SSP.sspZero SSP.sspPosOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspZero SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspZero SSP.sspPosOne SSP.sspNegOne SSP.sspZero = refl
sameRowCommutes SSP.sspZero SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspZero SSP.sspPosOne SSP.sspZero SSP.sspNegOne = refl
sameRowCommutes SSP.sspZero SSP.sspPosOne SSP.sspZero SSP.sspZero = refl
sameRowCommutes SSP.sspZero SSP.sspPosOne SSP.sspZero SSP.sspPosOne = refl
sameRowCommutes SSP.sspZero SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspZero SSP.sspPosOne SSP.sspPosOne SSP.sspZero = refl
sameRowCommutes SSP.sspZero SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne SSP.sspZero = refl
sameRowCommutes SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspNegOne SSP.sspZero SSP.sspNegOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspNegOne SSP.sspZero SSP.sspZero = refl
sameRowCommutes SSP.sspPosOne SSP.sspNegOne SSP.sspZero SSP.sspPosOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne SSP.sspZero = refl
sameRowCommutes SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspZero SSP.sspNegOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspZero SSP.sspNegOne SSP.sspZero = refl
sameRowCommutes SSP.sspPosOne SSP.sspZero SSP.sspNegOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspZero SSP.sspZero SSP.sspNegOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspZero SSP.sspZero SSP.sspZero = refl
sameRowCommutes SSP.sspPosOne SSP.sspZero SSP.sspZero SSP.sspPosOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspZero SSP.sspPosOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspZero SSP.sspPosOne SSP.sspZero = refl
sameRowCommutes SSP.sspPosOne SSP.sspZero SSP.sspPosOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne SSP.sspZero = refl
sameRowCommutes SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspPosOne SSP.sspZero SSP.sspNegOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspPosOne SSP.sspZero SSP.sspZero = refl
sameRowCommutes SSP.sspPosOne SSP.sspPosOne SSP.sspZero SSP.sspPosOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne = refl
sameRowCommutes SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne SSP.sspZero = refl
sameRowCommutes SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne = refl

-- Remaining Steinberg relations and 5616-element group enumeration
-- have exact local independent Python receipts, not a postulated
-- Agda group isomorphism. 26-site spatial adjacency and Monster VOA
-- remain separately owned and source-typed.
