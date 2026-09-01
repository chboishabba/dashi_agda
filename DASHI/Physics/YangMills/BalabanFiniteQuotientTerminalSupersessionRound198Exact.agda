{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteQuotientTerminalSupersessionRound198Exact where

------------------------------------------------------------------------
-- ROUND198 BIDI TERMINAL SUPERSESSION
--
-- Older Sprint110/111 carrier ledgers correctly recorded that no concrete
-- finite gauge-quotient representative-independence theorem was then present.
-- R196 now constructs such a carrier from the actual rooted gauge section.
-- R197 adds an exact finite selected-ensemble rational L2 pairing whose norm is
-- literally the existing finite-selector norm and is pointwise definite.
--
-- This owner updates theorem authority WITHOUT rewriting historical Bool
-- ledgers. It states exactly which old finite blockers are superseded and which
-- analytic/continuum obligations remain live.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base using (0ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact as R196
import DASHI.Physics.YangMills.BalabanFiniteRootedGaugeQuotientL2Round197Exact as R197
import DASHI.Physics.Closure.YMSprint111GaugeQuotientPhysicalSectorCompatibility as S111

record FiniteQuotientTerminalReplacement
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base) : Set₂ where
  field
    quotientCarrier : Set₁
    quotientCarrierIsRootedPhysical :
      quotientCarrier ≡ R196.FiniteRootedGaugeQuotientCarrier group base paths

    normalize :
      Covariance.DirectedGaugeField4 N group → quotientCarrier

    normalizedRepresentative :
      quotientCarrier → Covariance.DirectedGaugeField4 N group

    selectedEnsemble :
      R197.FiniteRootedQuotientEnsemble group base paths

    selectedPairingDefinite :
      ∀ observable →
      R197.finiteQuotientNormSq selectedEnsemble observable ≡ 0ℚ →
      ∀ state → observable state ≡ 0ℚ

open FiniteQuotientTerminalReplacement public

finiteQuotientTerminalReplacement :
  ∀ {N} {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (ensemble : R197.FiniteRootedQuotientEnsemble group base paths) →
  FiniteQuotientTerminalReplacement group base paths
finiteQuotientTerminalReplacement group base paths ensemble = record
  { quotientCarrier =
      R196.FiniteRootedGaugeQuotientCarrier group base paths
  ; quotientCarrierIsRootedPhysical = refl
  ; normalize =
      R196.normalizeToFiniteRootedGaugeQuotient group base paths
  ; normalizedRepresentative =
      R196.representativeField
  ; selectedEnsemble = ensemble
  ; selectedPairingDefinite =
      R197.finiteQuotientNormZeroPointwise ensemble
  }

-- Historical metadata remains historical.  We do not flip its Bool.  The new
-- theorem carrier supersedes only the narrower claim that no concrete finite
-- representative carrier/independence theorem exists in the repository.
historicalSprint111FiniteCompatibilityFlagRemainsFalse :
  S111.FiniteQuotientInput.compatibilityProvedHere S111.canonicalFiniteQuotientInput
  ≡ false
historicalSprint111FiniteCompatibilityFlagRemainsFalse = refl

finiteGaugeOrbitRepresentativeCarrierNowConstructedRound198Level : ProofLevel
finiteGaugeOrbitRepresentativeCarrierNowConstructedRound198Level = machineChecked

finiteSelectedEnsemblePairingNowDefiniteRound198Level : ProofLevel
finiteSelectedEnsemblePairingNowDefiniteRound198Level = machineChecked

-- Still-live leaves. R196/R197 intentionally do not prove these.
literalPhysicalInvariantHaarGibbsMeasureRound198Level : ProofLevel
literalPhysicalInvariantHaarGibbsMeasureRound198Level = conditional

literalPhysicalGaugeQuotientL2HilbertCompletionRound198Level : ProofLevel
literalPhysicalGaugeQuotientL2HilbertCompletionRound198Level = conditional

literalFiniteHamiltonianDescentToRootedQuotientRound198Level : ProofLevel
literalFiniteHamiltonianDescentToRootedQuotientRound198Level = conditional

literalFiniteToContinuumPhysicalCarrierMapsRound198Level : ProofLevel
literalFiniteToContinuumPhysicalCarrierMapsRound198Level = conditional

literalPhysicalProjectionAndVacuumSectorCompatibilityRound198Level : ProofLevel
literalPhysicalProjectionAndVacuumSectorCompatibilityRound198Level = conditional
