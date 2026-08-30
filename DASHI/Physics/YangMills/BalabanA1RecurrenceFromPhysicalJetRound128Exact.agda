{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1RecurrenceFromPhysicalJetRound128Exact where

------------------------------------------------------------------------
-- ROUND128 A1 BIDI: (5.42) ALREADY OWNS THE RECURRENCE COEFFICIENT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as ℕ
open import Data.Rational.Base using (-_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact as Jet
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Real

record PhysicalJetOnCutoffDynamics (K : Nat) : Set₁ where
  field
    dynamics : BetaLaw.BalabanCutoffCouplingDynamics K
    embedding : Real.OrderedRationalRealEmbedding
    jetData : ∀ k → k ℕ.< K → Jet.CMP109OffDiagonalSecondJetData

    vacuumDerivativeIsEmbeddedPhysicalJet :
      ∀ k (k<K : k ℕ.< K) →
      BetaLaw.negativeOffDiagonalSecondMomentumDerivative
        (BetaLaw.vacuumPolarisationCoefficient dynamics) k
      ≡ Real.embed embedding
          (- Jet.mixedDerivativeCoefficient
              (Jet.fullOffDiagonalTwoJet (jetData k k<K)))

open PhysicalJetOnCutoffDynamics public

recurrenceCorrectionIsEmbeddedPhysicalJet :
  ∀ {K} (dataSet : PhysicalJetOnCutoffDynamics K)
    k (k<K : k ℕ.< K) →
  Trajectory.betaCorrection (BetaLaw.step (dynamics dataSet)) (suc k)
  ≡ Real.embed (embedding dataSet)
      (- Jet.mixedDerivativeCoefficient
          (Jet.fullOffDiagonalTwoJet (jetData dataSet k k<K)))
recurrenceCorrectionIsEmbeddedPhysicalJet dataSet k k<K =
  trans
    (BetaLaw.betaFromVacuumPolarisation
      (BetaLaw.vacuumPolarisationCoefficient (dynamics dataSet)) k k<K)
    (vacuumDerivativeIsEmbeddedPhysicalJet dataSet k k<K)

recurrenceCorrectionIsEmbeddedJetBeta :
  ∀ {K} (dataSet : PhysicalJetOnCutoffDynamics K)
    k (k<K : k ℕ.< K) →
  Trajectory.betaCorrection (BetaLaw.step (dynamics dataSet)) (suc k)
  ≡ Real.embed (embedding dataSet) (Jet.beta (jetData dataSet k k<K))
recurrenceCorrectionIsEmbeddedJetBeta dataSet k k<K =
  trans
    (recurrenceCorrectionIsEmbeddedPhysicalJet dataSet k k<K)
    (cong (Real.embed (embedding dataSet))
      (Jet.cmp109MixedDerivativeExtractsBeta (jetData dataSet k k<K)))

a1RecurrenceFromPhysicalJetRound128Level : ProofLevel
a1RecurrenceFromPhysicalJetRound128Level = machineChecked

-- A1.3 is therefore not an independent source theorem after the same-jet weld:
-- it is already encoded by `betaFromVacuumPolarisation` in the literal cutoff
-- dynamics and follows by transitivity.
