{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1RecurrenceFromPhysicalJetRound128Exact where

------------------------------------------------------------------------
-- ROUND128 A1 BIDI: (5.42) ALREADY OWNS THE RECURRENCE COEFFICIENT
--
-- `BalabanCutoffBetaLaw` does not merely name a beta sequence.  Its literal
-- vacuum-polarisation coefficient already states, for every physical shell,
--
--   betaCorrection_{k+1}
--     = negativeOffDiagonalSecondMomentumDerivative_k.
--
-- Consequently A1 does NOT need another source lemma identifying the recurrence
-- coefficient after the physical Eq.(5.1)/(5.42) jet has been welded to that
-- derivative.  The equality below is pure transitivity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as ℕ
open import Data.Rational.Base using (-_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
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

    -- The only physical weld needed here: the literal vacuum-polarisation
    -- derivative stored by the dynamics is this exact Eq.(5.1) two-jet.
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
  where
    open import Relation.Binary.PropositionalEquality using (cong)

a1RecurrenceFromPhysicalJetRound128Level : ProofLevel
a1RecurrenceFromPhysicalJetRound128Level = machineChecked

-- Therefore the old A1.3 wording, "actual recurrence coefficient is the
-- physical jet", is not an independent mathematical source lemma.  It follows
-- from the already literal `betaFromVacuumPolarisation` field plus A1's same-jet
-- identification.  The surviving source work is A1.1/A1.2.
