module DASHI.Physics.YangMills.BalabanCMP109Federbush011Equation38Quadratic32Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Collapse the two quantitative constants on the literal equation-(0.11)
-- path.  CMP98 equation (38) gives
--
--   ||r_source||_1 <= 24 ||dU||_1^2,
--
-- while the already-proved quarter reopening gives
--
--   ||e||_1 <= (4/3) ||r_source||_1.
--
-- Therefore the nonlinear Federbush correction satisfies the exact composed
-- estimate
--
--   ||e||_1 <= 32 ||dU||_1^2.
--
-- This is the same literal source remainder owned by equation (0.11); no
-- independent derivative or residual object is introduced.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanCMP109FederbushFrechetReopeningExact as Frechet
import DASHI.Physics.YangMills.BalabanCMP109Federbush011Equation38PhysicalFirstOrderExact as Physical
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38

composedQuadraticConstant : ℚ
composedQuadraticConstant = + 32 / 1

equation38FederbushPhysicalErrorQuadratic32 :
  ∀ {Index} (equation : Frechet.FederbushFrechetErrorEquation Index)
    inputMagnitude sourceMagnitude →
  Physical.Equation38FederbushSourceData
    Index equation inputMagnitude sourceMagnitude →
  L1.vectorL1
      (Frechet.coordinates equation)
      (Frechet.error equation)
    ≤ (composedQuadraticConstant * inputMagnitude) * inputMagnitude
equation38FederbushPhysicalErrorQuadratic32
    equation inputMagnitude sourceMagnitude data =
  let
    raw = Physical.equation38FederbushPhysicalErrorLittleO
      equation inputMagnitude sourceMagnitude
      (Eq38.sourceQuadraticConstant * inputMagnitude)
      data
      (ℚRing.solve-∀ Eq38.sourceQuadraticConstant inputMagnitude)
  in
  subst
    (λ upper →
      L1.vectorL1
        (Frechet.coordinates equation)
        (Frechet.error equation)
      ≤ upper)
    (ℚRing.solve-∀ inputMagnitude)
    raw

cmp109Federbush011Equation38Quadratic32Level : ProofLevel
cmp109Federbush011Equation38Quadratic32Level = machineChecked
