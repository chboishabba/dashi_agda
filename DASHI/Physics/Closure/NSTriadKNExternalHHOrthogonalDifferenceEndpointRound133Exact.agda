module DASHI.Physics.Closure.NSTriadKNExternalHHOrthogonalDifferenceEndpointRound133Exact where

------------------------------------------------------------------------
-- ROUND133 / THE COMPLEMENTARY HH ENDPOINT: RADIAL GAP VANISHES EXACTLY
--
-- Companion Lean result:
--   RequestProject/NavierStokes/WaleffeHighHighOutputGain.lean
--
-- Round132 removed the collinear extremal endpoint of HH->low by proving that
-- the actual projected cross interaction vanishes there.  The square-gap
-- identity exposes the complementary endpoint just as sharply.
--
-- Write
--
--   d = q-p,        Delta_2 = |q|^2-|p|^2.
--
-- Round125 already proves, on every physical resonant incidence,
--
--   Delta_2 = k.d.
--
-- Hence if the difference direction is transverse to the low output,
--
--   k.d = 0,
--
-- then the radial SQUARED multiplier gap vanishes identically:
--
--   Delta_2 = 0.
--
-- Combining this with Round128 gives the exact complementary saturation law
--
--   |k x d|^2 = |k|^2 (2|p|^2 + 2|q|^2 - |k|^2).
--
-- Thus the two geometric endpoints are now separated without an inequality:
--
--   collinear d     -> angular/Plucker part = 0;
--   output-orthogonal d -> radial square gap = 0.
--
-- The unresolved HH critical contribution is therefore genuinely an
-- intermediate-angle phenomenon.  No square root, division, norm estimate,
-- shell count, absolute value, or cutoff factor is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _*_; _+_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plane
import DASHI.Physics.Closure.NSTriadKNExternalHHEuclideanSquareGapFactorRound125Exact as R125
import DASHI.Physics.Closure.NSTriadKNExternalHHSquareGapGramRound128Exact as R128

module RingZ = NR IntRS.ring

record OutputOrthogonalDifference
    (tau : Physical.PhysicalTriadIncidence) : Set where
  constructor output-orthogonal-difference
  field
    differenceOrthogonalToOutput :
      Plane.dotMode
        (Physical.k tau)
        (R125.subtractMode (Physical.q tau) (Physical.p tau))
      ≡ + 0

open OutputOrthogonalDifference public

orthogonalDifferenceForcesSquareGapZero :
  (tau : Physical.PhysicalTriadIncidence) →
  OutputOrthogonalDifference tau →
  R125.squareGap (Physical.p tau) (Physical.q tau) ≡ + 0
orthogonalDifferenceForcesSquareGapZero tau O =
  trans
    (R125.resonantSquareGapFactorsThroughOutput tau)
    (differenceOrthogonalToOutput O)

orthogonalDifferenceSaturatesPluckerBudget :
  (tau : Physical.PhysicalTriadIncidence) →
  OutputOrthogonalDifference tau →
  let d = R125.subtractMode (Physical.q tau) (Physical.p tau)
      nk = Plane.modeNormSquared (Physical.k tau)
      np = Plane.modeNormSquared (Physical.p tau)
      nq = Plane.modeNormSquared (Physical.q tau)
  in
  Plane.pluckerNormSquared (Physical.k tau) d
  ≡ nk * (R128.two * np + R128.two * nq - nk)
orthogonalDifferenceSaturatesPluckerBudget tau O =
  let
    d = R125.subtractMode (Physical.q tau) (Physical.p tau)
    nk = Plane.modeNormSquared (Physical.k tau)
    np = Plane.modeNormSquared (Physical.p tau)
    nq = Plane.modeNormSquared (Physical.q tau)
    gapZero = orthogonalDifferenceForcesSquareGapZero tau O
    full = R128.hhSquareGapLowHighIdentity tau
    zeroed :
      (+ 0) * (+ 0) + Plane.pluckerNormSquared (Physical.k tau) d
      ≡ nk * (R128.two * np + R128.two * nq - nk)
    zeroed =
      subst
        (λ delta →
          delta * delta + Plane.pluckerNormSquared (Physical.k tau) d
          ≡ nk * (R128.two * np + R128.two * nq - nk))
        gapZero
        full
  in
  trans
    (RingZ.solve 1
      (λ angular →
        ( angular
        , (+ 0) * (+ 0) + angular))
      refl
      (Plane.pluckerNormSquared (Physical.k tau) d))
    zeroed

round133OutputOrthogonalDifferenceSquareGapZeroClosed : Bool
round133OutputOrthogonalDifferenceSquareGapZeroClosed = true

round133OutputOrthogonalDifferencePluckerSaturationClosed : Bool
round133OutputOrthogonalDifferencePluckerSaturationClosed = true

round133SquareRootOrDivisionIntroduced : Bool
round133SquareRootOrDivisionIntroduced = false

round133IntermediateAngleSignedCriticalPaymentClosed : Bool
round133IntermediateAngleSignedCriticalPaymentClosed = false

round133CriticalHHPaymentClosed : Bool
round133CriticalHHPaymentClosed = false

round133OutputOrthogonalDifferenceSquareGapZeroClosedIsTrue :
  round133OutputOrthogonalDifferenceSquareGapZeroClosed ≡ true
round133OutputOrthogonalDifferenceSquareGapZeroClosedIsTrue = refl

round133OutputOrthogonalDifferencePluckerSaturationClosedIsTrue :
  round133OutputOrthogonalDifferencePluckerSaturationClosed ≡ true
round133OutputOrthogonalDifferencePluckerSaturationClosedIsTrue = refl

round133SquareRootOrDivisionIntroducedIsFalse :
  round133SquareRootOrDivisionIntroduced ≡ false
round133SquareRootOrDivisionIntroducedIsFalse = refl

round133CriticalHHPaymentClosedIsFalse :
  round133CriticalHHPaymentClosed ≡ false
round133CriticalHHPaymentClosedIsFalse = refl
