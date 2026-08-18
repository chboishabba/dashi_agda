module DASHI.Physics.YangMills.BalabanClayOSPullbackBlockingBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", Communications in Mathematical
-- Physics 31 (1973), 83--112. DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- Pietro Menotti and Andrea Pelissetto,
-- "General Proof of Osterwalder-Schrader Positivity for the Wilson Action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251.
--
-- DASHI CONTRIBUTION
--
-- Unify two previously parallel repository interfaces:
--
--   BalabanClayExactOSPullbackRecombinationExact.ExactOSPullbackData
--   ReflectionPositiveBlocking.ReflectionPositiveBlocking.
--
-- Once the original OS form is the same fine reflection-positive form, the
-- exact physical pullback identity canonically IS a reflection-positive
-- blocking.  Therefore the existing blocking-composition theorem applies to
-- the recombination-aware Balaban route without introducing another positivity
-- hypothesis or requiring labelled RG pieces to be positive separately.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.FiniteReflectionPositivity as RP
import DASHI.Physics.YangMills.ReflectionPositiveBlocking as Block
import DASHI.Physics.YangMills.BalabanClayExactOSPullbackRecombinationExact as Pullback

record PullbackMatchesFineOS
    {Original Blocked Scalar : Set}
    (scalar : RP.PositiveAdditiveScalar Scalar)
    (fine : RP.FiniteReflectionPositive Original Scalar scalar)
    (dataSet : Pullback.ExactOSPullbackData Original Blocked Scalar) : Set₁ where
  field
    originalFormIsFineForm : ∀ original →
      Pullback.originalOSForm dataSet original ≡ RP.osForm fine original
    sameNonnegative : ∀ value →
      Pullback.Nonnegative dataSet value ≡ RP.Nonnegative scalar value

open PullbackMatchesFineOS public

exactPullbackAsReflectionPositiveBlocking :
  ∀ {Original Blocked Scalar : Set}
    {scalar : RP.PositiveAdditiveScalar Scalar}
    {fine : RP.FiniteReflectionPositive Original Scalar scalar}
    (dataSet : Pullback.ExactOSPullbackData Original Blocked Scalar) →
  PullbackMatchesFineOS scalar fine dataSet →
  Block.ReflectionPositiveBlocking Original Blocked Scalar scalar fine
exactPullbackAsReflectionPositiveBlocking dataSet match = record
  { Block.ReflectionPositiveBlocking.liftObservable =
      Pullback.pullback dataSet
  ; Block.ReflectionPositiveBlocking.coarseOSForm =
      Pullback.blockedOSForm dataSet
  ; Block.ReflectionPositiveBlocking.coarseFormPullback = λ blocked →
      Agda.Builtin.Equality.trans
        (Pullback.exactPullbackIdentity dataSet blocked)
        (originalFormIsFineForm match (Pullback.pullback dataSet blocked))
  }

exactPullbackProducesBlockedReflectionPositive :
  ∀ {Original Blocked Scalar : Set}
    {scalar : RP.PositiveAdditiveScalar Scalar}
    {fine : RP.FiniteReflectionPositive Original Scalar scalar}
    (dataSet : Pullback.ExactOSPullbackData Original Blocked Scalar)
    (match : PullbackMatchesFineOS scalar fine dataSet) →
  RP.FiniteReflectionPositive Blocked Scalar scalar
exactPullbackProducesBlockedReflectionPositive dataSet match =
  Block.blockedReflectionPositive
    (exactPullbackAsReflectionPositiveBlocking dataSet match)

pullbackBlockingBridgeLevel : ProofLevel
pullbackBlockingBridgeLevel = machineChecked

-- The remaining source-facing input is not positivity itself.  It is the exact
-- same-carrier identification between the literal Bałaban blocked OS form and
-- the pullback/recombination data, plus preservation of positive-time support.
literalBalabanBlockedOSPullbackIdentificationLevel : ProofLevel
literalBalabanBlockedOSPullbackIdentificationLevel = conditional
