module DASHI.Moonshine.Griess1990Moufang81IbrahimProjective13Exact where

-- REUSE FIRST OWNERS, not a new cube/trit or exceptional-algebra carrier.
-- External ORIGINAL mathematical author:
-- Robert L. Griess Jr., J. Algebra 131 (1990), 281-293,
-- DOI 10.1016/0021-8693(90)90176-O.
-- Original source's g on F3^3 defines a commutative Moufang quotient M81,
-- exponent 3, with associator δg = det_F3^3.
--
-- This file reuses the exact existing SSP trit and original Cube27
-- *point carrier* but NOT the cube P3^3 adjacency, which is NOT invariant
-- under all affine F3^3 source actions.
-- The Ibrahim 13/52/78 arithmetic owner and Chen--Lam--Shimakura
-- distinct actual Moonshine-VOA Z3 phase owner are retained.
--
-- The explicit source g, associator and two witnesses below are Agda
-- SOURCE-WRITTEN only: the Agda kernel has not been invoked here.
-- Finite exhaustive independent Python over all 27^3 grade triples
-- established associator=det with counts (8451,5616,5616),
-- and the order-81 commutative exponent-3 Moufang loop identity.
-- No same-VOA selected 3B, physical graph, F4/E6 action, or RH result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Wikimedia.IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact as Ibrahim
import DASHI.Wikimedia.IbrahimMonster3BZ3OrbifoldPhaseRecognitionSnowballExact as Orbifold

-- Identify F3 with the EXISTING typed balanced trits; signed labels are
-- a bijective choice, not a claim about which spatial edges are local.
F3 : Set
F3 = SSP.SSPTrit

neg3 : F3 → F3
neg3 SSP.sspNegOne = SSP.sspPosOne
neg3 SSP.sspZero = SSP.sspZero
neg3 SSP.sspPosOne = SSP.sspNegOne

add3 : F3 → F3 → F3
add3 SSP.sspNegOne SSP.sspNegOne = SSP.sspPosOne
add3 SSP.sspNegOne SSP.sspZero = SSP.sspNegOne
add3 SSP.sspNegOne SSP.sspPosOne = SSP.sspZero
add3 SSP.sspZero x = x
add3 SSP.sspPosOne SSP.sspNegOne = SSP.sspZero
add3 SSP.sspPosOne SSP.sspZero = SSP.sspPosOne
add3 SSP.sspPosOne SSP.sspPosOne = SSP.sspNegOne

mul3 : F3 → F3 → F3
mul3 SSP.sspZero _ = SSP.sspZero
mul3 SSP.sspNegOne SSP.sspZero = SSP.sspZero
mul3 SSP.sspNegOne SSP.sspNegOne = SSP.sspPosOne
mul3 SSP.sspNegOne SSP.sspPosOne = SSP.sspNegOne
mul3 SSP.sspPosOne SSP.sspZero = SSP.sspZero
mul3 SSP.sspPosOne SSP.sspNegOne = SSP.sspNegOne
mul3 SSP.sspPosOne SSP.sspPosOne = SSP.sspPosOne

sub3 : F3 → F3 → F3
sub3 x y = add3 x (neg3 y)

-- The ACTUAL original 27-point F3^3 group carrier, independent of edges.
V27 : Set
V27 = Cube.Ternary27Point

addV : V27 → V27 → V27
addV x y = Cube.ternary27Point
  (add3 (Cube.x x) (Cube.x y))
  (add3 (Cube.y x) (Cube.y y))
  (add3 (Cube.z x) (Cube.z y))

-- Published Griess source phase:
-- g(x,y) = -x0*x1*y2 - x2*y0*y1 + x1*x2*y0 + x0*y1*y2.
g : V27 → V27 → F3
g x y =
  add3
    (sub3
      (neg3 (mul3 (mul3 (Cube.x x) (Cube.y x)) (Cube.z y)))
      (mul3 (mul3 (Cube.z x) (Cube.x y)) (Cube.y y)))
    (add3
      (mul3 (mul3 (Cube.y x) (Cube.z x)) (Cube.x y))
      (mul3 (mul3 (Cube.x x) (Cube.y y)) (Cube.z y)))

-- The 81-element finite central extension *as an actual carrier and
-- multiplication*, not 81 as an abstract integer.
M81 : Set
M81 = V27 × F3

moufangProduct : M81 → M81 → M81
moufangProduct (x , a) (y , b) =
  (addV x y , add3 (add3 a b) (g x y))

moufangIdentity : M81
moufangIdentity = (Cube.origin , SSP.sspZero)

associator : V27 → V27 → V27 → F3
associator x y z =
  sub3 (add3 (g x y) (g (addV x y) z))
       (add3 (g y z) (g x (addV y z)))

det3 : V27 → V27 → V27 → F3
det3 x y z =
  add3
    (sub3
      (mul3 (Cube.x x)
        (sub3 (mul3 (Cube.y y) (Cube.z z))
              (mul3 (Cube.z y) (Cube.y z))))
      (mul3 (Cube.y x)
        (sub3 (mul3 (Cube.x y) (Cube.z z))
              (mul3 (Cube.z y) (Cube.x z)))))
    (mul3 (Cube.z x)
      (sub3 (mul3 (Cube.x y) (Cube.y z))
            (mul3 (Cube.y y) (Cube.x z))))

xAxis yAxis zAxis : V27
xAxis = Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero
yAxis = Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero
zAxis = Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne

-- Concrete original-source sign and orientation acceptance tests.
orientedDetIsOne : det3 xAxis yAxis zAxis ≡ SSP.sspPosOne
orientedDetIsOne = refl

orientedAssociatorIsOne :
  associator xAxis yAxis zAxis ≡ SSP.sspPosOne
orientedAssociatorIsOne = refl

-- Ibrahim's 13 is a TYPED same-integer witness, but distinct
-- incidence/projective/action recognition remains a separate requirement.
projectiveThirteenMatchesIbrahimInteger : 13 ≡ Ibrahim.evenPrefix
projectiveThirteenMatchesIbrahimInteger = refl

fourTimesThirteenMatchesIbrahimF4Arithmetic : 52 ≡ 4 * 13
fourTimesThirteenMatchesIbrahimF4Arithmetic =
  Ibrahim.fiftyTwoAsFourThirteen

sixTimesThirteenMatchesIbrahimE6Arithmetic : 78 ≡ 6 * 13
sixTimesThirteenMatchesIbrahimE6Arithmetic =
  Ibrahim.seventyEightAsSixThirteen

griessLoopCardinalityArithmetic : 81 ≡ 3 * Cube.hypervoxelStateCount
griessLoopCardinalityArithmetic = refl

-- The full 19,683-triple universal determinant identity and Moufang
-- identity have LOCAL EXACT Python receipts, not Agda kernel receipts.
-- The genuine projective PG(2,3) incidence counts 13,52,78 are
-- only source-derived *incidence* counts, not F4/E6 equivariance.
record SourceCut : Set where
  constructor source-cut
  field
    originalM81MultiplicationWritten : Bool
    basisAssociatorWitnessWritten : Bool
    exhaustiveIndependentPythonPassed : Bool
    exactPG23IncidencePythonPassed : Bool
    selectedMonsterVOAModeIntertwinerPaid : Bool
    F4E6ActionIntertwinerPaid : Bool
    agdaKernelChecked : Bool

canonicalSourceCut : SourceCut
canonicalSourceCut =
  source-cut true true true true false false false
