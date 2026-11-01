module DASHI.Physics.YangMills.CompactLieBiInvariantSkewLangevinExact where

------------------------------------------------------------------------
-- ROUND72: BI-INVARIANT COMPACT-LIE METRIC -> ZERO CONNECTION ENERGY GROWTH
--
-- PRIMARY GEOMETRIC SOURCE
--
-- John Milnor,
-- "Curvatures of Left Invariant Metrics on Lie Groups",
-- Advances in Mathematics 21 (1976), 293--329.
-- DOI: 10.1016/S0001-8708(76)80002-3.
--
-- Standard compact-Lie fact used here: a compact Lie group admits an
-- Ad-invariant inner product (average any inner product over Haar measure),
-- hence a bi-invariant Riemannian metric.  For such a metric ad_Z is
-- skew-adjoint:
--
--   <[Z,X],Y> + <X,[Z,Y]> = 0.
--
-- DASHI CONTRIBUTION
--
-- The compact-group Langevin derivative equation contains an onsite
-- connection/ad term.  Its contribution to the quadratic derivative-energy
-- identity is exactly the paired expression above.  Therefore it vanishes
-- SITE BY SITE.  Summing over lattice sites still gives exactly zero: there is
-- no symmetric growth constant and no lattice-volume loss to budget.
--
-- This is the geometric reason the Round72 weighted propagation theorem only
-- needs the symmetric Hessian/influence row from the physical effective
-- action.  It is group-parametric and not SU(2)-specific.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record BiInvariantLieMetricData : Set₁ where
  field
    Scalar Lie : Set
    zero : Scalar
    add : Scalar → Scalar → Scalar
    inner : Lie → Lie → Scalar
    bracket : Lie → Lie → Lie

    addZeroLeft : ∀ x → add zero x ≡ x

    -- Infinitesimal Ad-invariance / skew-adjointness of ad_Z.
    adSkew : ∀ Z X Y →
      add (inner (bracket Z X) Y)
          (inner X (bracket Z Y))
      ≡ zero

open BiInvariantLieMetricData public

connectionPairedEnergy :
  (D : BiInvariantLieMetricData) →
  Lie D → Lie D → Lie D → Scalar D
connectionPairedEnergy D Z X Y =
  add D
    (inner D (bracket D Z X) Y)
    (inner D X (bracket D Z Y))

connectionPairedEnergyCancels :
  (D : BiInvariantLieMetricData) →
  ∀ Z X Y →
  connectionPairedEnergy D Z X Y ≡ zero D
connectionPairedEnergyCancels D = adSkew D

connectionQuadraticEnergy :
  (D : BiInvariantLieMetricData) →
  Lie D → Lie D → Scalar D
connectionQuadraticEnergy D Z X = connectionPairedEnergy D Z X X

connectionQuadraticEnergyCancels :
  (D : BiInvariantLieMetricData) →
  ∀ Z X →
  connectionQuadraticEnergy D Z X ≡ zero D
connectionQuadraticEnergyCancels D Z X = adSkew D Z X X

sumConnectionQuadratic :
  {Site : Set} →
  (D : BiInvariantLieMetricData) →
  (connection gradient : Site → Lie D) →
  List Site → Scalar D
sumConnectionQuadratic D connection gradient [] = zero D
sumConnectionQuadratic D connection gradient (site ∷ sites) =
  add D
    (connectionQuadraticEnergy D (connection site) (gradient site))
    (sumConnectionQuadratic D connection gradient sites)

finiteLatticeConnectionEnergyCancels :
  {Site : Set} →
  (D : BiInvariantLieMetricData) →
  (connection gradient : Site → Lie D) →
  ∀ sites →
  sumConnectionQuadratic D connection gradient sites ≡ zero D
finiteLatticeConnectionEnergyCancels D connection gradient [] = refl
finiteLatticeConnectionEnergyCancels D connection gradient (site ∷ sites)
  rewrite connectionQuadraticEnergyCancels D (connection site) (gradient site)
        | finiteLatticeConnectionEnergyCancels D connection gradient sites =
  addZeroLeft D (zero D)

biInvariantSkewConnectionCancellationLevel : ProofLevel
biInvariantSkewConnectionCancellationLevel = machineChecked

-- Standard geometry boundary: every compact Lie group admits an Ad-invariant
-- inner product / bi-invariant metric.  The theorem above then applies to every
-- compact-simple Clay gauge group.  The remaining Yang--Mills-specific work is
-- to identify the actual covariant derivative equation's connection term with
-- this `ad` contribution; no independent positive connection-growth estimate
-- is required afterwards.
compactLieBiInvariantMetricExistenceLevel : ProofLevel
compactLieBiInvariantMetricExistenceLevel = standardImported

physicalLangevinConnectionIsBiInvariantAdTermLevel : ProofLevel
physicalLangevinConnectionIsBiInvariantAdTermLevel = conditional
