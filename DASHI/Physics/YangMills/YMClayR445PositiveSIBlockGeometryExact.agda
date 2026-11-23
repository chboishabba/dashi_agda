module DASHI.Physics.YangMills.YMClayR445PositiveSIBlockGeometryExact where

------------------------------------------------------------------------
-- P0: CORRECT THE SI PHYSICAL-LENGTH DIRECTION FOR ORIGINAL R445.
--
-- A strictly positive path length [metre] and its reciprocal dimension
-- [metre^-1] are DISTINCT. A negative EXPONENT on a unit is NOT a
-- negative geometric distance. The genuine selected R445 native bond
-- traverses TWO (not eight) original positive fine axial links.
--
-- Donors (no replacement physical theory):
-- YMClayR445OriginalAxialBondParityInjectiveExact, existing Base2/369
-- all-1024 original bond codec, YMClayPhysicalCubeDobrushinFromGibbsExact
-- original normalized Gibbs physical-cube positivity and calibration,
-- YangMillsSIScalingEndpointExact and BIPM SI.
--
-- The existing physical-cube source has a strict spacing-positive field.
-- From that source hypothesis this module ACTUALLY derives 0<2*a.
-- The stronger nonnegative-plus-reciprocal law also mathematically
-- forces a>0, but is not turned into an unsupported original Wilson
-- analytic source theorem here.
--
-- This proves source-index geometry and ordered rational arithmetic.
-- It does not construct original Wilson D1 common q, a positive
-- finite continuum correlation length or same-H OS mass gap.
-- Source-written; no Agda kernel run.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact as Scale
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as Native
import DASHI.Physics.YangMills.YMClayR445Base2ThreeAxis369FibreBIDIExact as Binary
import DASHI.Physics.YangMills.YMClayPhysicalCubeDobrushinFromGibbsExact as GibbsCube

-- Same original source positive bond, not 128 independent Wilson links.
sameOriginalSelectedPositiveBond :
  (C : Native.CoarseBond) (phase : Native.Bit) →
  Binary.encodeOriginalFine
    (Binary.originalAddress C phase Binary.zeroTransverse)
  ≡ Native.originalR445SelectedFineBond C phase
sameOriginalSelectedPositiveBond = Binary.selectedZeroSheetIsOriginalR445

-- Geometry does not require a scalar inverse or a logarithm:
-- the positive original native path length is exactly a+a.
fineLength : ℚ → Scale.SIIndexedQuantity ℚ SI.Length
fineLength a = Scale.siQuantity a

nativeTwoFineLinkLength : ℚ → Scale.SIIndexedQuantity ℚ SI.Length
nativeTwoFineLinkLength a = Scale.siQuantity (a + a)

nativeLengthIsTwoFineLengths :
  ∀ a →
  Scale.magnitude (nativeTwoFineLinkLength a)
    ≡ Scale.magnitude (fineLength a) + Scale.magnitude (fineLength a)
nativeLengthIsTwoFineLengths a = refl

-- Crucial positivity theorem, consuming the exact strict rational
-- spacing witness from the actual ORIGINAL physical-cube source.
-- Positivity is not merely a SI type tag: SIIndexedQuantity by itself
-- permits zero/negative scalar magnitudes.
twoFineLinkLengthStrictlyPositive :
  (a : ℚ) → 0ℚ < a → 0ℚ < Scale.magnitude (nativeTwoFineLinkLength a)
twoFineLinkLengthStrictlyPositive a aPositive =
  subst
    (λ left → left < a + a)
    (ℚP.+-identityʳ 0ℚ)
    (ℚP.+-mono-< aPositive aPositive)

-- Direct reuse of the ORIGINAL source's physically selected Gibbs
-- family: it ALREADY demands positive spacing at every cutoff.
-- We consume that field and conclude that the R445 *geometric*
-- two-fine-link SI path would be strictly positive at that cutoff.
-- No claim is made that the selected physical cube is always just
-- two fine cells at all changing cutoffs.
originalGibbsEveryCutoffTwoLinkPositive :
  ∀ {Cutoff Volume : Set}
    {Local : Cutoff → Set}
    {BoundaryState : (cutoff : Cutoff) → Volume → Set}
    {AdmissiblePerturbation :
      (cutoff : Cutoff) (volume : Volume) →
      BoundaryState cutoff volume →
      BoundaryState cutoff volume → Set}
  (source : GibbsCube.OriginalPhysicalCubeConditionals
    Cutoff Volume Local BoundaryState AdmissiblePerturbation)
  (cutoff : Cutoff) →
  0ℚ <
    Scale.magnitude
      (nativeTwoFineLinkLength (GibbsCube.latticeSpacing source cutoff))
originalGibbsEveryCutoffTwoLinkPositive source cutoff =
  twoFineLinkLengthStrictlyPositive
    (GibbsCube.latticeSpacing source cutoff)
    (GibbsCube.latticeSpacingPositive source cutoff)

------------------------------------------------------------------------
-- PHYSICAL GAP FRONTIER, NOT A CONSTRUCTION:
--
-- To solve POSITIVE PHYSICAL CORRELATION LENGTH for original full
-- Wilson two-J covariance: at a fixed positive physical block side L,
-- prove |Cov(F,G)| <= A q^d using SAME original finite Gibbs source,
-- uniform in cutoff/volume, with a real q in [0,1).
--
-- If q=0 use qbar=(1+q)/2 in (0,1), still q^d<=qbar^d.
-- Then xi_BOUND=L/(-log qbar)>0 [metre] and
-- |Cov|<=A exp(-L*d/xi_BOUND).
-- This is an UPPER ENVELOPE length, not automatically the actual
-- lightest spectral correlation length. Source log and monotonicity
-- must be implemented over the ORIGINAL real-analytic ℝ owner.
--
-- Original physical cube positivity does not prove this q-bound.
-- Original 128 selected links do not jointly factorize over 896
-- spectators (384 original plaquettes contain two selected links).
--
-- OS same-H time transport, dense observable closure, continuum
-- nontriviality and hbar/c SI conversion still require independent
-- proofs. Do not use equality of bare numerical magnitudes [m^-1]
-- and [kg] from a dimension-erasing projection as physical identity.
------------------------------------------------------------------------
