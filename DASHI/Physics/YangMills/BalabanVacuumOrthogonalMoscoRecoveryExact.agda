module DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Umberto Mosco,
-- "Convergence of Convex Sets and of Solutions of Variational
-- Inequalities", Advances in Mathematics 3 (1969), 510--585.
-- DOI: 10.1016/0001-8708(69)90009-7.
--
-- Kazuhiro Kuwae; Takashi Shioya,
-- "Convergence of Spectral Structures: A Functional Analytic Theory and Its
-- Applications to Spectral Geometry", Communications in Analysis and
-- Geometry 11 (2003), 599--673.
-- DOI: 10.4310/cag.2003.v11.n4.a1.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the one-vector recovery inequality to the exact vacuum-orthogonal
-- theorem shape needed by the Clay-facing Yang--Mills path.  The theorem does
-- not ask for trace-norm convergence of the whole transfer operator.  For each
-- limiting vector u orthogonal to the limiting vacuum it asks only for one
-- finite cutoff/depth representative u_n which is orthogonal to the finite
-- vacuum and satisfies
--
--   ||u||^2 <= ||u_n||^2,
--   m ||u_n||^2 <= Q_n(u_n),
--   Q_n(u_n) <= Q_infinity(u).
--
-- The already checked Mosco-upper/recovery algebra then yields directly
--
--   m ||u||^2 <= Q_infinity(u).
--
-- This is the precise lower-gap-preservation theorem behind the shorter
-- recovery route.  Constructing the physical recovery map and proving these
-- inequalities for the actual cutoff Yang--Mills measures remains an analytic
-- producer; no boolean or authority token can inhabit the witness below.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanMoscoRecoveryGapTransferExact as Recovery

record VacuumOrthogonalRecoverySystem : Set₁ where
  field
    FiniteIndex : Set
    FiniteVector : FiniteIndex → Set
    LimitVector : Set

    finiteNormSq : (index : FiniteIndex) → FiniteVector index → ℚ
    finiteEnergy : (index : FiniteIndex) → FiniteVector index → ℚ
    limitNormSq : LimitVector → ℚ
    limitEnergy : LimitVector → ℚ

    finiteVacuumOrthogonal :
      (index : FiniteIndex) → FiniteVector index → Set
    limitVacuumOrthogonal : LimitVector → Set

    gapConstant : ℚ
    gapConstantNonnegative : 0ℚ ≤ gapConstant

    recoveryIndex : LimitVector → FiniteIndex
    recoveryVector :
      (limit : LimitVector) → FiniteVector (recoveryIndex limit)

    recoveryVacuumOrthogonal : ∀ limit →
      limitVacuumOrthogonal limit →
      finiteVacuumOrthogonal
        (recoveryIndex limit) (recoveryVector limit)

    recoveryNormDominates : ∀ limit →
      limitVacuumOrthogonal limit →
      limitNormSq limit
      ≤ finiteNormSq (recoveryIndex limit) (recoveryVector limit)

    finiteGapOnVacuumComplement :
      ∀ index finite →
      finiteVacuumOrthogonal index finite →
      gapConstant * finiteNormSq index finite
      ≤ finiteEnergy index finite

    recoveryEnergyUpper : ∀ limit →
      limitVacuumOrthogonal limit →
      finiteEnergy (recoveryIndex limit) (recoveryVector limit)
      ≤ limitEnergy limit
open VacuumOrthogonalRecoverySystem public

vacuumOrthogonalRecoveryStep :
  (system : VacuumOrthogonalRecoverySystem) →
  (limit : LimitVector system) →
  limitVacuumOrthogonal system limit →
  Recovery.UniformGapRecoveryStep
vacuumOrthogonalRecoveryStep system limit orthogonal =
  record
    { Recovery.UniformGapRecoveryStep.gapConstant =
        gapConstant system
    ; Recovery.UniformGapRecoveryStep.gapConstantNonnegative =
        gapConstantNonnegative system
    ; Recovery.UniformGapRecoveryStep.limitOrthogonalNormSq =
        limitNormSq system limit
    ; Recovery.UniformGapRecoveryStep.recoveryOrthogonalNormSq =
        finiteNormSq system
          (recoveryIndex system limit) (recoveryVector system limit)
    ; Recovery.UniformGapRecoveryStep.recoveryEnergy =
        finiteEnergy system
          (recoveryIndex system limit) (recoveryVector system limit)
    ; Recovery.UniformGapRecoveryStep.limitEnergy =
        limitEnergy system limit
    ; Recovery.UniformGapRecoveryStep.normRecovered =
        recoveryNormDominates system limit orthogonal
    ; Recovery.UniformGapRecoveryStep.finiteUniformGap =
        finiteGapOnVacuumComplement system
          (recoveryIndex system limit)
          (recoveryVector system limit)
          (recoveryVacuumOrthogonal system limit orthogonal)
    ; Recovery.UniformGapRecoveryStep.recoveryEnergyUpper =
        recoveryEnergyUpper system limit orthogonal
    }

vacuumOrthogonalRecoveryTransfersUniformGap :
  (system : VacuumOrthogonalRecoverySystem) →
  (limit : LimitVector system) →
  limitVacuumOrthogonal system limit →
  gapConstant system * limitNormSq system limit
  ≤ limitEnergy system limit
vacuumOrthogonalRecoveryTransfersUniformGap system limit orthogonal =
  Recovery.recoveryStepTransfersUniformGap
    (vacuumOrthogonalRecoveryStep system limit orthogonal)

record PhysicalVacuumGapAfterRecovery
    (system : VacuumOrthogonalRecoverySystem) : Set₁ where
  field
    limitGap : ∀ limit →
      limitVacuumOrthogonal system limit →
      gapConstant system * limitNormSq system limit
      ≤ limitEnergy system limit
open PhysicalVacuumGapAfterRecovery public

physicalVacuumGapAfterRecovery :
  (system : VacuumOrthogonalRecoverySystem) →
  PhysicalVacuumGapAfterRecovery system
physicalVacuumGapAfterRecovery system = record
  { limitGap = vacuumOrthogonalRecoveryTransfersUniformGap system }

-- Deliberately left conditional until a pinned Agda-2.9 kernel run is observed
-- for the cumulative Round-42 root.  The theorem term above is explicit; this
-- metadata must not outrun validation.
vacuumOrthogonalMoscoRecoveryLevel : ProofLevel
vacuumOrthogonalMoscoRecoveryLevel = conditional

physicalVacuumRecoveryProducerLevel : ProofLevel
physicalVacuumRecoveryProducerLevel = conditional
