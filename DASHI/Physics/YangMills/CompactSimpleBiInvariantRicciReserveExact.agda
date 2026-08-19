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

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record RicciReserveScalar : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    add : Scalar → Scalar → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set

    addMono : ∀ {a b c d} →
      LessEqual a b → LessEqual c d → LessEqual (add a c) (add b d)
    addZeroLeft : ∀ x → add zero x ≡ x

open RicciReserveScalar public

record CompactSimpleRicciReserveData (S : RicciReserveScalar) : Set₁ where
  field
    Tangent : Set
    metricQuadratic ricciQuadratic : Tangent → Scalar S
    reserve : Scalar S

    reservePositive : StrictLess S (zero S) reserve
    factorRicciReserve : ∀ X →
      LessEqual S
        (scaleReserve reserve (metricQuadratic X))
        (ricciQuadratic X)

    -- Multiplication by the positive reserve is kept abstract because this
    -- module is geometric/carrier-level and does not choose a scalar model.
    scaleReserve : Scalar S → Scalar S → Scalar S

open CompactSimpleRicciReserveData public

record ProductRicciReserveData
    (S : RicciReserveScalar)
    (factor : CompactSimpleRicciReserveData S) : Set₁ where
  field
    Site : Set
    productTangent : Set
    component : productTangent → Site → Tangent factor
    sites : List Site

    productMetric productRicci : productTangent → Scalar S

    productMetricIsSum : ∀ X →
      productMetric X ≡ sumMetric X sites
    productRicciIsSum : ∀ X →
      productRicci X ≡ sumRicci X sites

  sumMetric : productTangent → List Site → Scalar S
  sumMetric X [] = zero S
  sumMetric X (site ∷ rest) =
    add S (metricQuadratic factor (component X site)) (sumMetric X rest)

  sumRicci : productTangent → List Site → Scalar S
  sumRicci X [] = zero S
  sumRicci X (site ∷ rest) =
    add S (ricciQuadratic factor (component X site)) (sumRicci X rest)

open ProductRicciReserveData public

-- The product-reserve implication is standard Riemannian product geometry.
-- We deliberately keep scalar multiplication/distributivity in that standard
-- boundary instead of rebuilding an ordered-field hierarchy here.
record ProductReserveWitness
    {S : RicciReserveScalar}
    {factor : CompactSimpleRicciReserveData S}
    (product : ProductRicciReserveData S factor) : Set₁ where
  field
    productRicciReserve : ∀ X →
      LessEqual S
        (scaleReserve factor (reserve factor) (productMetric product X))
        (productRicci product X)

open ProductReserveWitness public

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
