module DASHI.Physics.YangMills.BalabanReducedFaddeevPopovRelativePerturbationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Put the background ghost operator into the exact relative form needed by a
-- finite trace-log expansion, using the concrete Round61 reduced inverse.
-- For a colourwise mean-zero ghost source s and anchor x0 define
--
--   R_A s = M_A (M_0^{-1} s) - s.
--
-- Since M_0 M_0^{-1} s = s exactly, the identity background has R_1 = 0 and
-- the literal background operator satisfies on this reduced source carrier
--
--   M_A M_0^{-1} s = s + R_A s.
--
-- This is an actual same-carrier normalization of the determinant problem.
-- No determinant, logarithm, convergence, or continuum limit is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovGreenInverseExact as Inverse

relativeFaddeevPopovPerturbation :
  Physical.RationalSU2Background4 → Periodic.Site4 →
  FP.SiteGaugeParameter4 → FP.SiteGaugeParameter4
relativeFaddeevPopovPerturbation background anchor source coordinate =
  FP.faddeevPopovApply background
      (Inverse.reducedFlatGreenInverse source anchor) coordinate
  - source coordinate

relativeFaddeevPopovNormalizationExact :
  ∀ background anchor source coordinate →
  FP.faddeevPopovApply background
      (Inverse.reducedFlatGreenInverse source anchor) coordinate
  ≡ source coordinate
      + relativeFaddeevPopovPerturbation background anchor source coordinate
relativeFaddeevPopovNormalizationExact background anchor source coordinate =
  ℚRing.solve-∀
    (FP.faddeevPopovApply background
      (Inverse.reducedFlatGreenInverse source anchor) coordinate)
    (source coordinate)

relativeFaddeevPopovIdentityZero :
  ∀ source anchor →
  Inverse.ColourwiseMeanZero source →
  ∀ coordinate site →
  relativeFaddeevPopovPerturbation
      Physical.identityBackground anchor source (pair coordinate site)
  ≡ 0ℚ
relativeFaddeevPopovIdentityZero source anchor meanZero coordinate site =
  trans
    (cong
      (λ selected → selected - source (pair coordinate site))
      (FP.identityFaddeevPopovIsFlat
        (Inverse.reducedFlatGreenInverse source anchor)
        coordinate site))
    (trans
      (cong
        (λ selected → selected - source (pair coordinate site))
        (Inverse.reducedFlatGreenRightInverse
          source anchor meanZero coordinate site))
      (ℚRing.solve-∀ (source (pair coordinate site))))

reducedRelativeFaddeevPopovNormalizationLevel : ProofLevel
reducedRelativeFaddeevPopovNormalizationLevel = machineChecked

reducedRelativeFaddeevPopovIdentityZeroLevel : ProofLevel
reducedRelativeFaddeevPopovIdentityZeroLevel = machineChecked

-- Remaining analytic bridge: expand this SAME finite relative operator in the
-- chosen small background/coupling parameter, define the reduced finite trace,
-- and identify the trace-log jet with log det' M_A - log det' M_0.
literalReducedFaddeevPopovTraceLogIdentificationLevel : ProofLevel
literalReducedFaddeevPopovTraceLogIdentificationLevel = conditional
