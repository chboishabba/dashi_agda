module DASHI.Physics.YangMills.BalabanP33RationalInverseNorm32Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Specialize the repository's finite spectral inverse theorem to the exact P33
-- floor 1/32.  Once a physical finite Hessian supplies its spectral realization
-- and uses ordinary rational reciprocal/order, the conclusion is literally
--
--   ||H_A^-1|| <= 32.
--
-- No new inverse estimate is assumed: the only semantic inputs identify the
-- physical spectral carrier with the already existing abstract theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _≤_; _/_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4FiniteCoercivityInverseNormExact as Spectral
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

thirtyTwo : ℚ
thirtyTwo = + 32 / 1

p33InverseNormAtMostThirtyTwo :
  ∀ {Index}
    (dataSet : Spectral.FiniteSpectralCoercivityInverseNorm Index ℚ)
    index →
  Spectral.LessEqual dataSet ≡ _≤_ →
  Spectral.coercivityConstant dataSet index ≡ P33.p33PhysicalFloor →
  Spectral.reciprocal dataSet P33.p33PhysicalFloor ≡ thirtyTwo →
  Spectral.inverseOperatorNorm dataSet index ≤ thirtyTwo
p33InverseNormAtMostThirtyTwo
    dataSet index orderMeaning coercivityMeaning reciprocalMeaning =
  subst
    (λ upper → Spectral.inverseOperatorNorm dataSet index ≤ upper)
    (trans
      (cong (Spectral.reciprocal dataSet) coercivityMeaning)
      reciprocalMeaning)
    (subst
      (λ relation → relation
        (Spectral.inverseOperatorNorm dataSet index)
        (Spectral.reciprocal dataSet
          (Spectral.coercivityConstant dataSet index)))
      orderMeaning
      (Spectral.inverseNormBelowReciprocalCoercivity dataSet index))

p33ExactReciprocalTargetLevel : ProofLevel
p33ExactReciprocalTargetLevel = machineChecked

p33SpectralInverseNorm32ReductionLevel : ProofLevel
p33SpectralInverseNorm32ReductionLevel = machineChecked
