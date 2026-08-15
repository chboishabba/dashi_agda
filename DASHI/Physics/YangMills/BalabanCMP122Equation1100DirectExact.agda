module DASHI.Physics.YangMills.BalabanCMP122Equation1100DirectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- DIRECT LOCATOR
--
-- Equation (1.100), p. 390 in the journal pagination.  After the exponentiated
-- cluster expansion (1.98), Bałaban divides R'^(k)(X) into boundary terms and
-- the basic R-terms.  For the latter the localization domain is disjoint from
-- the large-field region, c1 = exp(-p0(g_k)), and the paper states the sharper
-- bound
--
--   |R^(k)(X,(U,J))|
--      <= exp(-p0(g_k)) exp(-kappa d_k(X)).
--
-- The paragraph immediately before (1.100) states that the analytic extension
-- is defined on the corresponding U_k(X,...) domain; the right hand side is
-- independent of the boundary/background variables.  Thus (1.100) is the
-- boundary-uniform pointwise input needed by the DASHI rooted-shell lane.
--
-- CMP119, Sect. 2, equation (2.31), gives the corresponding inductive R-term
-- hypothesis with an arbitrarily large decay constant kappa_0 (after the other
-- parameters are fixed appropriately).  That flexibility is precisely what
-- permits entropy to consume only part of the source decay.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- A literal typed carrier for the numerical content of (1.100).  The values
-- p0Suppression and diameterDecay denote the two exponentials appearing on the
-- right hand side, rather than a newly chosen DASHI majorant.
record CMP122Equation1100Pointwise
    (Scale Polymer Boundary : Set) : Set₁ where
  field
    rNorm : Scale → Polymer → Boundary → ℚ
    p0Suppression : Scale → ℚ
    diameterDecay : Scale → Polymer → ℚ

    equation1100 : ∀ scale polymer boundary →
      rNorm scale polymer boundary
      ≤ p0Suppression scale * diameterDecay scale polymer

open CMP122Equation1100Pointwise public

cmp122Equation1100BoundaryUniform :
  ∀ {Scale Polymer Boundary}
    (source : CMP122Equation1100Pointwise Scale Polymer Boundary)
    scale polymer boundary →
  rNorm source scale polymer boundary
  ≤ p0Suppression source scale * diameterDecay source scale polymer
cmp122Equation1100BoundaryUniform source = equation1100 source

-- Primary-paper authority for the pointwise inequality itself.  What remains
-- conditional is the representation dictionary identifying the repository's
-- concrete R-expression norm and distance with these literal source objects.
cmp122Equation1100PrimarySourceLevel : ProofLevel
cmp122Equation1100PrimarySourceLevel = standardImported

cmp122Equation1100RepositoryRepresentationLevel : ProofLevel
cmp122Equation1100RepositoryRepresentationLevel = conditional

-- CMP119 (2.31): the R-term decay constant may be chosen arbitrarily large
-- after the remaining constructive parameters are fixed appropriately.  This
-- is source authority, not a claim that a particular DASHI constant has already
-- been matched to that choice.
cmp119Equation231ArbitraryDecayReserveLevel : ProofLevel
cmp119Equation231ArbitraryDecayReserveLevel = standardImported
