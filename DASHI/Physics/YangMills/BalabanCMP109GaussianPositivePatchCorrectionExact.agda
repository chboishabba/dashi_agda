module DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact where

------------------------------------------------------------------------
-- ROW A1 GAUSSIAN CORRECTION: POSITIVE-MEASURE PATCH, NOT ONE MODE
--
-- PRIMARY / CONVENTION SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Martin Luescher and Peter Weisz,
-- "Efficient Numerical Techniques for Perturbative Lattice Gauge Theory
-- Computations", Nuclear Physics B 266 (1986), 309--356.
-- DOI: 10.1016/0550-3213(86)90094-5.
-- Relationship: standard Wilson-action lattice vertex conventions and automatic
-- generation of gluon vertices.  It is used here only as a perturbative
-- convention/cross-check; the physical source carrier remains CMP109/CMP99.
--
-- CORRECTION
--
-- The previous source cutset used one discrete corner momentum
-- q=(0,1/2,0,0) as a sufficient Gaussian-floor witness.  Two independent
-- source/convention checks show that this is too aggressive physically:
--
--   * the first background derivative of the Wilson Hessian is a cubic gluon
--     vertex.  In the standard Wilson lattice vertex, all-equal Lorentz
--     components cancel, and at the Brillouin boundary the relevant sine factors
--     can vanish.  Therefore a diagonal corner component must not be assumed
--     nonzero without deriving the exact CMP99/CMP109 index convention;
--
--   * a single discrete Fourier mode has vanishing normalized measure in a
--     thermodynamic/continuum limit.  A cutoff/volume-uniform beta floor must be
--     supplied by a positive-measure momentum patch (or an equivalent family of
--     modes whose normalized weight stays positive), not merely one point.
--
-- Highest-alpha corrected route:
--
--   literal CMP99/CMP109 first background variation
--      -> choose a mixed Lorentz/color component away from a lattice-vertex zero
--      -> certify it on ONE fixed positive-volume momentum box
--      -> use paramagnetic/seagull nonnegativity on the complement
--      -> obtain a uniform Gaussian floor.
--
-- This reuses the repository's existing configured Brillouin box carrier.  It
-- does NOT restore a global near/far estimate: only one positive patch needs a
-- quantitative lower enclosure; the complement needs only nonnegativity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral

------------------------------------------------------------------------
-- Pure rational patch arithmetic
------------------------------------------------------------------------

patchLowerIsLowerForPatchPlusNonnegativeRest :
  (patch : Integral.BoxIntegralEnclosure)
  (rest : List Integral.BoxIntegralEnclosure) →
  0ℚ ≤ Integral.boxLowerSum rest →
  Integral.lowerContribution patch
  ≤ Integral.boxLowerSum (patch ∷ rest)
patchLowerIsLowerForPatchPlusNonnegativeRest patch rest restNN =
  subst
    (λ left → left ≤
      Integral.lowerContribution patch + Integral.boxLowerSum rest)
    (ℚP.+-identityʳ (Integral.lowerContribution patch))
    (ℚP.+-monoʳ-≤ (Integral.lowerContribution patch) restNN)

------------------------------------------------------------------------
-- Source-facing positive patch
------------------------------------------------------------------------

record CMP109LiteralGaussianPositivePatch : Set₁ where
  field
    patch : Integral.BoxIntegralEnclosure
    complement : List Integral.BoxIntegralEnclosure

    -- The box is part of the SAME normalized Fourier trace obtained from the
    -- constrained CMP109 Gaussian / CMP99 background operator.
    patchIsLiteralCMP109GaussianTrace : Set
    complementIsLiteralSameGaussianTrace : Set

    -- The selected box has fixed positive normalized measure and avoids zeros of
    -- the relevant mixed Wilson/background cubic vertex component.
    patchHasCutoffVolumeUniformPositiveMeasure : Set
    mixedLorentzColorVertexComponentUsed : Set
    patchAvoidsLatticeVertexZeroSet : Set

    -- The lowerContribution already includes box volume and quadrature error.
    patchLowerPositive : Set

    -- Paramagnetic/seagull sign is sufficient on every other box; no sharp
    -- global lower estimate is required there.
    complementLowerSumNonnegative :
      0ℚ ≤ Integral.boxLowerSum complement

open CMP109LiteralGaussianPositivePatch public

globalGaussianLowerFromOnePatch :
  (dataSet : CMP109LiteralGaussianPositivePatch) →
  Integral.lowerContribution (patch dataSet)
  ≤ Integral.boxLowerSum (patch dataSet ∷ complement dataSet)
globalGaussianLowerFromOnePatch dataSet =
  patchLowerIsLowerForPatchPlusNonnegativeRest
    (patch dataSet)
    (complement dataSet)
    (complementLowerSumNonnegative dataSet)

------------------------------------------------------------------------
-- Current source target
------------------------------------------------------------------------

record CMP109GaussianPatchSourceTarget : Set₁ where
  field
    positivePatch : CMP109LiteralGaussianPositivePatch

    -- CMP109 (1.5) delegates H_{1,j}, Delta_1 to Sect. D of reference [13];
    -- reference [13] is the CMP99 background-propagator paper.  The first
    -- background variation must therefore differentiate the SAME CMP99 Delta(U)
    -- plus the averaging/gauge-fixing constraint dependence entering the
    -- constrained Gaussian, not a continuum surrogate.
    cmp99DeltaFirstVariationDerived : Set
    cmp98AveragingFirstVariationDerived : Set
    constrainedProjectionFirstVariationDerived : Set

    -- A fixed patch around a non-boundary momentum with a nonzero mixed vertex
    -- component is the preferred witness.  Exact rational/trigonometric box
    -- endpoints belong in the existing box evaluator.
    sourceCoherentMixedVertexPatchEnclosed : Set

open CMP109GaussianPatchSourceTarget public

------------------------------------------------------------------------
-- Authority boundary
------------------------------------------------------------------------

positivePatchArithmeticLevel : ProofLevel
positivePatchArithmeticLevel = machineChecked

-- Physical/source work still required.
cmp109LiteralGaussianPositivePatchLevel : ProofLevel
cmp109LiteralGaussianPositivePatchLevel = conditional

cmp109CMP99FirstVariationLevel : ProofLevel
cmp109CMP99FirstVariationLevel = conditional

cmp109GaussianPatchSourceTargetLevel : ProofLevel
cmp109GaussianPatchSourceTargetLevel = conditional

-- The earlier single-corner scalar remains useful as a finite-data regression,
-- but is no longer the authoritative cutoff/volume-uniform physical witness.
