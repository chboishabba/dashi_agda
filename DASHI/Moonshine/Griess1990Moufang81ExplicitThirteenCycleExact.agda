module DASHI.Moonshine.Griess1990Moufang81ExplicitThirteenCycleExact where

-- 2026-10-25 highest-value Griess-M81 -> old-240 vs E8 same-action cut.
-- Original external mathematical owner: R. L. Griess Jr.,
-- J. Algebra 131 (1990) 281-293,
-- DOI 10.1016/0021-8693(90)90176-O.
-- Source g, nonassociative Moufang loop and original degree-3 action
-- are not originally DASHI inventions.
--
-- Reuses Griess1990Moufang81IbrahimProjective13Exact (literal M81)
-- and the PREEXISTING Kernel5↔M81×Trit chart, NOT a second T5/E8.
--
-- Corrected source-automorphism word: shear 01; shear 12; shear 20.
-- Its grade matrix (over F3) is [[1,1,0],[0,1,1],[1,1,1]].
-- Exact local Python: 81 = 3 fixed + 6×13-cycles;
-- old original240 = 6 fixed + 18×13-cycles.
-- W(E8) root automorphism group has 696729600 elements and
-- 696729600 % 13 = 8: NO equivalent Weyl-root action for this
-- particular 240-point Griess source automorphism.
-- This is NOT a claim of all E8 automorphism/no physical action.
--
-- The Agda exhaustive constructor proof below is SOURCE WRITTEN;
-- Agda kernel has NOT been run in the authoring environment.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Product using (_×_; _,_)

open import DASHI.Algebra.Trit using (neg; zer; pos)
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Moonshine.Griess1990Moufang81IbrahimProjective13Exact as Griess
import DASHI.Moonshine.Griess1990OriginalKernel5M81243240ChartExact as Chart

F3 : Set
F3 = SSP.SSPTrit

-- The three ORIGINAL cocycle-corrected shears, not naive linear maps.
e01 : Griess.M81 → Griess.M81
e01 (Cube.ternary27Point x y z , c) =
  (Cube.ternary27Point (Griess.add3 x y) y z ,
   Griess.add3 c (Griess.mul3 z
     (Griess.sub3 SSP.sspPosOne (Griess.mul3 y y))))

e12 : Griess.M81 → Griess.M81
e12 (Cube.ternary27Point x y z , c) =
  (Cube.ternary27Point x (Griess.add3 y z) z ,
   Griess.add3 c (Griess.mul3 x
     (Griess.sub3 (Griess.mul3 z z) SSP.sspPosOne)))

e20 : Griess.M81 → Griess.M81
e20 (Cube.ternary27Point x y z , c) =
  (Cube.ternary27Point x y (Griess.add3 z x) , c)

shortOrder13 : Griess.M81 → Griess.M81
shortOrder13 m = e20 (e12 (e01 m))

iterate : Nat → Griess.M81 → Griess.M81
iterate zero m = m
iterate (suc n) m = shortOrder13 (iterate n m)

-- Full 81-case constructor elimination, requiring no assumed axiom or
-- externally chosen Bool to stand in for the universal order-13 law.
order13All : (x y z c : F3) →
  iterate 13 (Cube.ternary27Point x y z , c) ≡
    (Cube.ternary27Point x y z , c)
order13All SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne = refl
order13All SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne SSP.sspZero = refl
order13All SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne = refl
order13All SSP.sspNegOne SSP.sspNegOne SSP.sspZero SSP.sspNegOne = refl
order13All SSP.sspNegOne SSP.sspNegOne SSP.sspZero SSP.sspZero = refl
order13All SSP.sspNegOne SSP.sspNegOne SSP.sspZero SSP.sspPosOne = refl
order13All SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne = refl
order13All SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne SSP.sspZero = refl
order13All SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne = refl
order13All SSP.sspNegOne SSP.sspZero SSP.sspNegOne SSP.sspNegOne = refl
order13All SSP.sspNegOne SSP.sspZero SSP.sspNegOne SSP.sspZero = refl
order13All SSP.sspNegOne SSP.sspZero SSP.sspNegOne SSP.sspPosOne = refl
order13All SSP.sspNegOne SSP.sspZero SSP.sspZero SSP.sspNegOne = refl
order13All SSP.sspNegOne SSP.sspZero SSP.sspZero SSP.sspZero = refl
order13All SSP.sspNegOne SSP.sspZero SSP.sspZero SSP.sspPosOne = refl
order13All SSP.sspNegOne SSP.sspZero SSP.sspPosOne SSP.sspNegOne = refl
order13All SSP.sspNegOne SSP.sspZero SSP.sspPosOne SSP.sspZero = refl
order13All SSP.sspNegOne SSP.sspZero SSP.sspPosOne SSP.sspPosOne = refl
order13All SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne = refl
order13All SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne SSP.sspZero = refl
order13All SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne = refl
order13All SSP.sspNegOne SSP.sspPosOne SSP.sspZero SSP.sspNegOne = refl
order13All SSP.sspNegOne SSP.sspPosOne SSP.sspZero SSP.sspZero = refl
order13All SSP.sspNegOne SSP.sspPosOne SSP.sspZero SSP.sspPosOne = refl
order13All SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne = refl
order13All SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne SSP.sspZero = refl
order13All SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne = refl
order13All SSP.sspZero SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne = refl
order13All SSP.sspZero SSP.sspNegOne SSP.sspNegOne SSP.sspZero = refl
order13All SSP.sspZero SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne = refl
order13All SSP.sspZero SSP.sspNegOne SSP.sspZero SSP.sspNegOne = refl
order13All SSP.sspZero SSP.sspNegOne SSP.sspZero SSP.sspZero = refl
order13All SSP.sspZero SSP.sspNegOne SSP.sspZero SSP.sspPosOne = refl
order13All SSP.sspZero SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne = refl
order13All SSP.sspZero SSP.sspNegOne SSP.sspPosOne SSP.sspZero = refl
order13All SSP.sspZero SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne = refl
order13All SSP.sspZero SSP.sspZero SSP.sspNegOne SSP.sspNegOne = refl
order13All SSP.sspZero SSP.sspZero SSP.sspNegOne SSP.sspZero = refl
order13All SSP.sspZero SSP.sspZero SSP.sspNegOne SSP.sspPosOne = refl
order13All SSP.sspZero SSP.sspZero SSP.sspZero SSP.sspNegOne = refl
order13All SSP.sspZero SSP.sspZero SSP.sspZero SSP.sspZero = refl
order13All SSP.sspZero SSP.sspZero SSP.sspZero SSP.sspPosOne = refl
order13All SSP.sspZero SSP.sspZero SSP.sspPosOne SSP.sspNegOne = refl
order13All SSP.sspZero SSP.sspZero SSP.sspPosOne SSP.sspZero = refl
order13All SSP.sspZero SSP.sspZero SSP.sspPosOne SSP.sspPosOne = refl
order13All SSP.sspZero SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne = refl
order13All SSP.sspZero SSP.sspPosOne SSP.sspNegOne SSP.sspZero = refl
order13All SSP.sspZero SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne = refl
order13All SSP.sspZero SSP.sspPosOne SSP.sspZero SSP.sspNegOne = refl
order13All SSP.sspZero SSP.sspPosOne SSP.sspZero SSP.sspZero = refl
order13All SSP.sspZero SSP.sspPosOne SSP.sspZero SSP.sspPosOne = refl
order13All SSP.sspZero SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne = refl
order13All SSP.sspZero SSP.sspPosOne SSP.sspPosOne SSP.sspZero = refl
order13All SSP.sspZero SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne = refl
order13All SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne = refl
order13All SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne SSP.sspZero = refl
order13All SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne = refl
order13All SSP.sspPosOne SSP.sspNegOne SSP.sspZero SSP.sspNegOne = refl
order13All SSP.sspPosOne SSP.sspNegOne SSP.sspZero SSP.sspZero = refl
order13All SSP.sspPosOne SSP.sspNegOne SSP.sspZero SSP.sspPosOne = refl
order13All SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne = refl
order13All SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne SSP.sspZero = refl
order13All SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne = refl
order13All SSP.sspPosOne SSP.sspZero SSP.sspNegOne SSP.sspNegOne = refl
order13All SSP.sspPosOne SSP.sspZero SSP.sspNegOne SSP.sspZero = refl
order13All SSP.sspPosOne SSP.sspZero SSP.sspNegOne SSP.sspPosOne = refl
order13All SSP.sspPosOne SSP.sspZero SSP.sspZero SSP.sspNegOne = refl
order13All SSP.sspPosOne SSP.sspZero SSP.sspZero SSP.sspZero = refl
order13All SSP.sspPosOne SSP.sspZero SSP.sspZero SSP.sspPosOne = refl
order13All SSP.sspPosOne SSP.sspZero SSP.sspPosOne SSP.sspNegOne = refl
order13All SSP.sspPosOne SSP.sspZero SSP.sspPosOne SSP.sspZero = refl
order13All SSP.sspPosOne SSP.sspZero SSP.sspPosOne SSP.sspPosOne = refl
order13All SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne = refl
order13All SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne SSP.sspZero = refl
order13All SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne = refl
order13All SSP.sspPosOne SSP.sspPosOne SSP.sspZero SSP.sspNegOne = refl
order13All SSP.sspPosOne SSP.sspPosOne SSP.sspZero SSP.sspZero = refl
order13All SSP.sspPosOne SSP.sspPosOne SSP.sspZero SSP.sspPosOne = refl
order13All SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne = refl
order13All SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne SSP.sspZero = refl
order13All SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne = refl

selectedWitness : Griess.M81
selectedWitness =
  (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero ,
   SSP.sspZero)

-- The phase must be -1 (=2 mod3); naive grade-only lift fails.
selectedWitnessFirstImage :
  shortOrder13 selectedWitness ≡
  (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne ,
   SSP.sspNegOne)
selectedWitnessFirstImage = refl

selectedWitnessThirteen :
  iterate 13 selectedWitness ≡ selectedWitness
selectedWitnessThirteen =
  order13All SSP.sspPosOne SSP.sspZero SSP.sspZero SSP.sspZero

-- A genuinely constructed operation on the ORIGINAL five-trit kernel,
-- via its ACTUAL bijection to M81×Trit. Preserves the extra coordinate.
actOnOriginalKernel5 : Chart.Kernel5 → Chart.Kernel5
actOnOriginalKernel5 z with Chart.kernel5ToM81 z
... | (m , t) = Chart.m81ToKernel5 (shortOrder13 m , t)

-- The selected chart action fixes all three diagonal states.
diagonalNegFixed :
  actOnOriginalKernel5 (Chart.diagonalKernel5 neg) ≡
    Chart.diagonalKernel5 neg
diagonalNegFixed = refl

diagonalZeroFixed :
  actOnOriginalKernel5 (Chart.diagonalKernel5 zer) ≡
    Chart.diagonalKernel5 zer
diagonalZeroFixed = refl

diagonalPosFixed :
  actOnOriginalKernel5 (Chart.diagonalKernel5 pos) ≡
    Chart.diagonalKernel5 pos
diagonalPosFixed = refl

-- These are three concrete witnesses only; the full old240 dependent
-- action restriction, cycle enumeration and the numerical E8 no-go
-- retain their independent Python and Lean proof-status ledgers.

-- Exact finite Weyl-order residue. This is a literal arithmetic
-- certificate, NOT a constructed Agda W(E8) action or proof that any
-- proposed representation must preserve the selected root system.
-- E8 root-system W order is classical; modern source discussion:
-- R. Winter & R. van Luijk (2021),
-- DOI 10.1007/s00373-021-02315-8.
weylE8Order : Nat
weylE8Order = 696729600

wE8OrderDivisionWitness : weylE8Order ≡ 13 * 53594584 + 8
wE8OrderDivisionWitness = refl

thirteenTimesSixPlusThree : 81 ≡ 6 * 13 + 3
thirteenTimesSixPlusThree = refl

thirteenTimesEighteenPlusSix : 240 ≡ 18 * 13 + 6
thirteenTimesEighteenPlusSix = refl

-- The original finite source action and full E8 root-system action
-- must be separately represented as SAME objects before equivariance
-- can be claimed. Classical Lagrange's theorem blocks that specific
-- action matching since W(E8) cannot have an order-13 automorphism.
