{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVSelectedLatticeAcousticKKFlatControlExact where

------------------------------------------------------------------------
-- S01-S04 -> S05-S06 EXACT SCOPED CONSTRUCTION / GOLDEN CANDIDATE.
--
-- Build a specific rational 3+1 acoustic principal quadratic, NOT a
-- freely given Signature31 mask or a constant ShiftArrow. Source:
-- local linear-response probes on a 3-direction nearest-neighbour
-- harmonic lattice, with continuum Klein--Gordon wave principal
--   Q(omega,k) = kx^2 + ky^2 + kz^2 - omega^2 (c=1 units).
--
-- The original spatial 3-neighbour directions are CHOSEN by this
-- scoped source, not emergently deduced from an arbitrary history.
-- The actual retarded Green distribution and the continuum/volume
-- limit of the quantum observer are NOT constructed in Agda here.
--
-- This file gives the actual FOUR tangent carrier and rational
-- selected acoustic metric, and uses the ORIGINAL
-- TSVFVKKSelectedHorizontalMetricSchurExact.KK5Bilinear to construct
-- a 5D nonzero-connection KK bilinear, with pointwise exact SAME-g4
-- horizontal equality and nonzero mixed circle coupling.
--
-- The 5D metric's chosen constant coefficients can be tested as a
-- flat vacuum Einstein solution in the independent exact SymPy
-- reference; there is NO Agda covariant derivative, Ricci or
-- Einstein field equation proved in this file.
--
-- Physical intent is explicitly a scoped FREE SCALAR / FLAT KK
-- control and NOT actual original physical TSVF branch, interacting
-- Yang--Mills/Clay OS Hamiltonian, or observed universal (3,1).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Physics.Foundations.TSFVKKSelectedHorizontalMetricSchurExact as KK

-- Coordinates are clock t and three *source-selected* lattice spatial
-- axes. The induced continuum metric will have c=1 in these
-- dimensionless rational-chart coordinates.
AcousticTangent4 : Set
AcousticTangent4 = ℚ × (ℚ × (ℚ × ℚ))

sourceAcousticFourMetric :
  AcousticTangent4 → AcousticTangent4 → ℚ
sourceAcousticFourMetric
    (t , (x , (y , z))) (u , (p , (q , r))) =
  ((((- t) * u) + (x * p)) + (y * q)) + (z * r)

-- The independently calculable continuum source response has
-- principal Q(k) = g4^{-1}(k,k) with c=1; here source Q on
-- rational covectors has the same explicit chosen diagonal.
sourceMeasuredWavePrincipal :
  ℚ → ℚ → ℚ → ℚ → ℚ
sourceMeasuredWavePrincipal omega kx ky kz =
  ((((- omega) * omega) + (kx * kx)) +
     (ky * ky)) + (kz * kz)

sameSelectedAcousticPrincipalAsFourMetric :
  ∀ omega kx ky kz →
  sourceMeasuredWavePrincipal omega kx ky kz ≡
  sourceAcousticFourMetric
    (omega , (kx , (ky , kz)))
    (omega , (kx , (ky , kz)))
sameSelectedAcousticPrincipalAsFourMetric omega kx ky kz = refl

-- Nonzero KK connection A = dx in the chart, already built from
-- the SAME source carrier. It may be locally pure gauge; do NOT
-- attribute a nontrivial 5D electromagnetic stress to it.
sourceSelectedKKConnection :
  AcousticTangent4 → ℚ
sourceSelectedKKConnection (t , (x , (y , z))) = x

sourceSelectedKKRadiusSquared : ℚ
sourceSelectedKKRadiusSquared = 1ℚ

sourceSelectedFiveMetric :
  AcousticTangent4 → ℚ →
  AcousticTangent4 → ℚ → ℚ
sourceSelectedFiveMetric =
  KK.KK5Bilinear
    sourceAcousticFourMetric
    sourceSelectedKKConnection
    sourceSelectedKKRadiusSquared

-- This is pointwise identity of the ORIGINAL chosen acoustic
-- principal metric and the ORIGINAL KK horizontal reduction;
-- not an equality of disconnected four-metric labels.
sourceSelectedFiveMetricHorizontalIsMeasuredFourMetric :
  ∀ v w →
  sourceSelectedFiveMetric
    v (KK.horizontalCircleComponent sourceSelectedKKConnection v)
    w (KK.horizontalCircleComponent sourceSelectedKKConnection w)
  ≡
  sourceAcousticFourMetric v w
sourceSelectedFiveMetricHorizontalIsMeasuredFourMetric v w =
  KK.actualKKHorizontalReductionIsOriginalFourMetric
    sourceAcousticFourMetric
    sourceSelectedKKConnection
    sourceSelectedKKRadiusSquared
    v w

-- Mixed coordinate circle projection retains a cross-term even when
-- the four-metric's horizontal projection has removed it.
sourceSelectedFiveMetricFrozenCircleRetainsConnection :
  ∀ v w →
  sourceSelectedFiveMetric v 0ℚ w 0ℚ
  ≡
  sourceAcousticFourMetric v w +
  sourceSelectedKKRadiusSquared *
    (sourceSelectedKKConnection v * sourceSelectedKKConnection w)
sourceSelectedFiveMetricFrozenCircleRetainsConnection v w =
  KK.naivelyFrozenFibreHasAdditionalConnectionTerm
    sourceAcousticFourMetric
    sourceSelectedKKConnection
    sourceSelectedKKRadiusSquared
    v w

-- Strong scope warning: the exact rational target has been
-- CONSTRUCTED, not empirically measured; the original physical
-- history-to-observer sensor and 5D Einstein-matter action source
-- remain open in #1460 and are not established by this example.
