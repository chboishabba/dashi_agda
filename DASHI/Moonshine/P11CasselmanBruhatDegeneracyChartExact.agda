module DASHI.Moonshine.P11CasselmanBruhatDegeneracyChartExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Ralf Schmidt,
-- "Some remarks on local newforms for GL(2)",
-- J. Ramanujan Math. Soc. 17 (2002), 115--147.
-- Lemma 2.1.1 gives the n=2 compact cells gamma_0,gamma_1,gamma_2,
-- with gamma_i characterized by v(c)=i for i<n and the terminal cell at n.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", GTM 228, Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- EXECUTABLE FINITE CHECK
-- scripts/verify_p11_casselman_bruhat_chart.py deterministically reduces the
-- Schmidt representatives modulo 4 inside B(Z/4)\GL_2(Z/4) and verifies
--
--   gamma_0 -> wide  orbit  {0,1,2,3}
--   gamma_1 -> right singleton {5}
--   gamma_2 -> left  singleton {4}.
--
-- Therefore the Bruhat3 coordinate order is
--
--   (wide,left,right) = (valuation0,terminal2,valuation1),
--
-- NOT (valuation0,valuation1,terminal2).
--
-- DASHI CONTRIBUTION
--
-- Tie the analytic degeneracy basis d=1,2,4 to the source-backed Casselman cell
-- order by the exact chart
--
--   (x1,x2,x4) |-> bruhat3 x1 x4 x2.
--
-- This is a coordinate realization of the classical K_0(4) oldspace, not a
-- comparison with the distinct principal full-level-2 fixed space.
--
-- Transport the already-derived classical U2 through this chart.  In Bruhat
-- coordinates the exact operator is
--
--   U2(w,l,r) = (-2w+r, 0, -2w+l).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
import Data.Integer.Tactic.RingSolver as ℤRing

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Old
import DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact as K0
import DASHI.Moonshine.P11Level44BadPrimeOperatorSeparationExact as Bad

------------------------------------------------------------------------
-- Exact analytic <-> Casselman/Bruhat coordinate chart.
------------------------------------------------------------------------

analyticToK0 : Old.Old3 → K0.Bruhat3
analyticToK0 v = K0.bruhat3 (Old.x1 v) (Old.x4 v) (Old.x2 v)

k0ToAnalytic : K0.Bruhat3 → Old.Old3
k0ToAnalytic v = Old.old3 (K0.wide v) (K0.right v) (K0.left v)

analyticAfterK0 :
  (v : K0.Bruhat3) → analyticToK0 (k0ToAnalytic v) ≡ v
analyticAfterK0 (K0.bruhat3 w l r) = refl

k0AfterAnalytic :
  (v : Old.Old3) → k0ToAnalytic (analyticToK0 v) ≡ v
k0AfterAnalytic (Old.old3 x1 x2 x4) = refl

analyticBasis1IsValuation0 :
  analyticToK0 Old.oldBasis1 ≡ K0.bruhat3 (+ 1) (+ 0) (+ 0)
analyticBasis1IsValuation0 = refl

analyticBasis2IsValuation1 :
  analyticToK0 Old.oldBasis2 ≡ K0.bruhat3 (+ 0) (+ 0) (+ 1)
analyticBasis2IsValuation1 = refl

analyticBasis4IsTerminal2 :
  analyticToK0 Old.oldBasis4 ≡ K0.bruhat3 (+ 0) (+ 1) (+ 0)
analyticBasis4IsTerminal2 = refl

------------------------------------------------------------------------
-- Classical U2 in the actual Bruhat/Casselman coordinate order.
------------------------------------------------------------------------

analyticU2OnK0 : K0.Bruhat3 → K0.Bruhat3
analyticU2OnK0 v = K0.bruhat3
  (((-[1+ 1 ]) *ℤ K0.wide v) +ℤ K0.right v)
  (+ 0)
  (((-[1+ 1 ]) *ℤ K0.wide v) +ℤ K0.left v)

u2ChartIntertwines :
  (v : Old.Old3) →
  analyticToK0 (Bad.analyticU2 v)
  ≡ analyticU2OnK0 (analyticToK0 v)
u2ChartIntertwines (Old.old3 x1 x2 x4) = refl

u2ChartIntertwinesBack :
  (v : K0.Bruhat3) →
  k0ToAnalytic (analyticU2OnK0 v)
  ≡ Bad.analyticU2 (k0ToAnalytic v)
u2ChartIntertwinesBack (K0.bruhat3 w l r) = refl

------------------------------------------------------------------------
-- Concrete U2 images of the three Casselman cells.
------------------------------------------------------------------------

valuation0Basis : K0.Bruhat3
valuation0Basis = K0.bruhat3 (+ 1) (+ 0) (+ 0)

valuation1Basis : K0.Bruhat3
valuation1Basis = K0.bruhat3 (+ 0) (+ 0) (+ 1)

terminal2Basis : K0.Bruhat3
terminal2Basis = K0.bruhat3 (+ 0) (+ 1) (+ 0)

u2OnValuation0 :
  analyticU2OnK0 valuation0Basis
  ≡ K0.bruhat3 (-[1+ 1 ]) (+ 0) (-[1+ 1 ])
u2OnValuation0 = refl

u2OnValuation1 :
  analyticU2OnK0 valuation1Basis ≡ valuation0Basis
u2OnValuation1 = refl

u2OnTerminal2 :
  analyticU2OnK0 terminal2Basis ≡ valuation1Basis
u2OnTerminal2 = refl

------------------------------------------------------------------------
-- Kernel generator in Casselman coordinates.  The analytic vector (1,2,2)
-- remains (wide,left,right)=(1,2,2), hence it lies on the common-plane side
-- left=right.
------------------------------------------------------------------------

k0KernelGenerator : K0.Bruhat3
k0KernelGenerator = K0.bruhat3 (+ 1) (+ 2) (+ 2)

analyticKernelChartsToK0Kernel :
  analyticToK0 Bad.analyticU2KernelVector ≡ k0KernelGenerator
analyticKernelChartsToK0Kernel = refl

k0KernelKilled :
  analyticU2OnK0 k0KernelGenerator ≡ K0.bruhat3 (+ 0) (+ 0) (+ 0)
k0KernelKilled = refl

record P11CasselmanBruhatDegeneracyChartBoundary : Set where
  field
    schmidtCellOrderingPinnedByFiniteVerifier : Bool
    bruhatOrderValuation0Terminal2Valuation1 : Bool
    analyticDegeneracyChartConstructed : Bool
    chartTwoSided : Bool
    classicalU2TransportedToBruhatCoordinates : Bool
    kernelGeneratorTransported : Bool
    principalFullLevel2ComparisonClaimed : Bool

canonicalP11CasselmanBruhatDegeneracyChartBoundary :
  P11CasselmanBruhatDegeneracyChartBoundary
canonicalP11CasselmanBruhatDegeneracyChartBoundary = record
  { schmidtCellOrderingPinnedByFiniteVerifier = true
  ; bruhatOrderValuation0Terminal2Valuation1 = true
  ; analyticDegeneracyChartConstructed = true
  ; chartTwoSided = true
  ; classicalU2TransportedToBruhatCoordinates = true
  ; kernelGeneratorTransported = true
  ; principalFullLevel2ComparisonClaimed = false
  }
