module DASHI.Physics.YangMills.BalabanYM4DifferentiatedMinimizerRemoteLocalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Michel Combes and Lawrence Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the linear RG1d composition on the literal side-four physical carrier.
-- If differentiation of the selected minimizer gives
--
--       deltaA(root) = - sum_y G(root,y) s(y)
--
-- and the source is supported where the CT geometric weight is at most q_R,
-- the already-proved physical response theorem yields immediately
--
--       |deltaA(root)| <= 64 q_R ||s||_1.
--
-- Thus after this module the remaining RG1d producer is not a Green-function
-- estimate.  It is exactly the physical differentiated-minimizer/source-support
-- identification and the later integration along an admissible background path.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; -_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33CombesThomasCoercivitySurvivalExact as Survival
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasPromotionExact as CT
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasResponseLocalityExact as Response

record PhysicalDifferentiatedMinimizerResponse
    (hessian green : CT.PhysicalMatrix) : Set₁ where
  field
    resolvent : CT.PhysicalCombesThomasResolvent hessian green
    deltaA source : Physical.PhysicalSU2Coordinate4 → ℚ

    differentiatedGreenIdentity :
      deltaA (CT.root (CT.geometry resolvent))
      ≡ - Response.rootGreenResponse resolvent source

open PhysicalDifferentiatedMinimizerResponse public

absoluteNegateExact : ∀ value → ∣ - value ∣ ≡ ∣ value ∣
absoluteNegateExact value = ℚP.∣-p∣≡∣p∣ value

physicalDifferentiatedMinimizerRemoteUpper :
  ∀ {hessian green}
    (data : PhysicalDifferentiatedMinimizerResponse hessian green)
    q →
  (∀ target →
    source data target ≡ + 0 / 1
    ⊎ CT.physicalWeight (CT.geometry (resolvent data)) target ≤ q) →
  ∣ deltaA data (CT.root (CT.geometry (resolvent data))) ∣
  ≤ (Survival.p33InverseScale * q) * Response.sourceL1 (source data)
physicalDifferentiatedMinimizerRemoteUpper data q support =
  let
    response = Response.rootGreenResponseRemoteUpper
      (resolvent data) (source data) q support
  in
  subst
    (λ lower → lower
      ≤ (Survival.p33InverseScale * q) * Response.sourceL1 (source data))
    (trans
      (congAbs (differentiatedGreenIdentity data))
      (absoluteNegateExact (Response.rootGreenResponse
        (resolvent data) (source data))))
    response
  where
  congAbs : ∀ {left right : ℚ} → left ≡ right → ∣ left ∣ ≡ ∣ right ∣
  congAbs refl = refl

ym4DifferentiatedMinimizerRemoteCTCompositionLevel : ProofLevel
ym4DifferentiatedMinimizerRemoteCTCompositionLevel = machineChecked

ym4DifferentiatedMinimizerPhysicalSupportIdentificationLevel : ProofLevel
ym4DifferentiatedMinimizerPhysicalSupportIdentificationLevel = conditional
