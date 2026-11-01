module DASHI.Physics.YangMills.CompactSimpleBiInvariantRicciReserveExact where

------------------------------------------------------------------------
-- ROUND74: COMPACT-SIMPLE BI-INVARIANT METRIC HAS A POSITIVE RICCI RESERVE
--
-- PRIMARY SOURCE
--
-- John Milnor,
-- "Curvatures of Left Invariant Metrics on Lie Groups",
-- Advances in Mathematics 21 (1976), 293--329.
-- DOI: 10.1016/S0001-8708(76)80002-3.
--
-- For a compact semisimple Lie algebra the Killing form B is negative definite.
-- With the canonical bi-invariant metric g = -B, the standard bi-invariant
-- curvature formula gives
--
--     Ric = -(1/4) B = (1/4) g.
--
-- More generally, after any fixed positive rescaling of the bi-invariant
-- metric on a compact SIMPLE factor, there is a fixed rho_G > 0 such that
--
--     Ric_G >= rho_G g_G.
--
-- The product metric on G^E has block-diagonal Ricci tensor.  Therefore the
-- SAME rho_G works on every finite product G^E: the lower bound does not decay
-- with the number of lattice edges.
--
-- This is stronger than the nonnegative-Ricci compiler in
-- `CompactLieBiInvariantRicciNonnegativeExact`: it supplies the positive
-- geometric reserve needed for the heat/Doob LSI argument at large heat time.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record RicciReserveScalar : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    LessEqual StrictLess : Scalar → Scalar → Set
    scale : Scalar → Scalar → Scalar

open RicciReserveScalar public

record CompactSimpleRicciReserveData (S : RicciReserveScalar) : Set₁ where
  field
    Tangent : Set
    metricQuadratic ricciQuadratic : Tangent → Scalar S
    reserve : Scalar S

    reservePositive : StrictLess S (zero S) reserve
    factorRicciReserve : ∀ X →
      LessEqual S
        (scale S reserve (metricQuadratic X))
        (ricciQuadratic X)

open CompactSimpleRicciReserveData public

-- Standard Riemannian product geometry is represented directly at its useful
-- theorem boundary: the product metric and Ricci tensor are block diagonal, so
-- a common factorwise reserve survives unchanged on every finite lattice.
record FiniteProductRicciReserve
    (S : RicciReserveScalar)
    (factor : CompactSimpleRicciReserveData S) : Set₁ where
  field
    ProductTangent : Set
    productMetricQuadratic productRicciQuadratic : ProductTangent → Scalar S

    productRicciReserve : ∀ X →
      LessEqual S
        (scale S (reserve factor) (productMetricQuadratic X))
        (productRicciQuadratic X)

open FiniteProductRicciReserve public

canonicalKillingMetricRicciQuarterLevel : ProofLevel
canonicalKillingMetricRicciQuarterLevel = standardImported

compactSimplePositiveRicciReserveLevel : ProofLevel
compactSimplePositiveRicciReserveLevel = standardImported

finiteProductPreservesRicciReserveLevel : ProofLevel
finiteProductPreservesRicciReserveLevel = standardImported

-- Physical seam is only normalization: the metric used by the literal heat
-- semigroup on each classified compact-simple G must be the same fixed
-- bi-invariant metric whose rho_G is supplied here.  No lattice-size estimate
-- remains after that identification.
physicalHeatMetricHasCompactSimpleRicciReserveLevel : ProofLevel
physicalHeatMetricHasCompactSimpleRicciReserveLevel = conditional
