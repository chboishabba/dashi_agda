{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinFiniteModeGaussianProjectionExact where

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact as FinitePlaquette
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinRationalGaussianProjectionExact as Projection
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinFiniteModeDecompositionExact as Decomposition
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- RICH BRILLOUIN SHELL -> FINITE-MODE GAUSSIAN -> LITERAL PLAQUETTE beta_Z
--
-- The second edge is already owned by FiniteModePlaquetteBetaSameObject.
-- Hence the preferred projection source theorem need only identify the rich
-- shell scalar with the finite-mode Gaussian beta_Z computed from the same
-- literal Brillouin calculation.
------------------------------------------------------------------------

record RichBrillouinFiniteModeGaussianSameObject
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    (finiteMode :
      FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom)
    (oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat)
    (remainder : Plaquette.PlaquetteRemainderData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₁ where
  field
    finiteModePlaquette :
      FinitePlaquette.FiniteModePlaquetteBetaSameObject
        finiteMode oneLoop remainder

    decompositionAt :
      ∀ step →
      Decomposition.RichBrillouinFiniteModeDecomposition
        (FiniteMode.gaussianAt finiteMode step) rich step

open RichBrillouinFiniteModeGaussianSameObject public

asRichBrillouinRationalGaussianProjection :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder rich}
    (sameObject : RichBrillouinFiniteModeGaussianSameObject
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      finiteMode oneLoop remainder rich) →
  Projection.RichBrillouinRationalGaussianProjection
    (Constructor.asPhysicalRunningCouplingData
      (FinitePlaquette.asCMP109LiteralPlaquetteCoefficientWeld
        (finiteModePlaquette sameObject)))
    rich
asRichBrillouinRationalGaussianProjection
    {finiteMode = finiteMode} sameObject = record
  { Projection.RichBrillouinRationalGaussianProjection.coefficientSameLiteralGaussian =
      λ step →
        BishopP.≃-trans
          (Decomposition.richCoefficientSameFiniteModeBetaZ
            (decompositionAt sameObject step))
          (subst
            (λ selected →
              Bishop._≃_
                (UV.embed
                  (Local.betaZ (FiniteMode.gaussianAt finiteMode step)))
                (UV.embed selected))
            (FinitePlaquette.gaussianBetaZSame
              (finiteModePlaquette sameObject) step)
            BishopP.≃-refl)
  }

richBrillouinFiniteModeProjectionCompilerLevel : ProofLevel
richBrillouinFiniteModeProjectionCompilerLevel = machineChecked

richCoefficientFiniteModeGaussianSameObjectLevel : ProofLevel
richCoefficientFiniteModeGaussianSameObjectLevel = machineChecked

richShellFiniteUniversalSameObjectLevel : ProofLevel
richShellFiniteUniversalSameObjectLevel = conditional

richRegularMatchingFiniteEpsilonSameObjectLevel : ProofLevel
richRegularMatchingFiniteEpsilonSameObjectLevel = conditional
