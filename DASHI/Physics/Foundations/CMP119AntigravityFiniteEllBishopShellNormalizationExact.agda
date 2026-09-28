{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityFiniteEllBishopShellNormalizationExact where

open import Agda.Builtin.Nat using (Nat; suc)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact as Pi
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as Running
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopRichBrillouinUVEdgeExact as RichNorm
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- FINITE ell -> EXISTING ANALYTIC BRILLOUIN SHELL
--
-- The rich shell theorem is already owned.  The finite-mode side only needs
-- to identify its rational ell with the normalized physical shell coordinate
-- pi^{-2} log L on the corresponding successor P3 node.
------------------------------------------------------------------------

record FiniteEllBishopShellNormalization
    {Mode : Set}
    (gaussian : Local.FiniteGaussianModeEnclosure Mode)
    (running : Running.CanonicalBishopSU2RunningInputs Nat)
    (edge : Nat) : Set₁ where
  field
    finiteEllIsNormalizedPhysicalLog :
      Bishop._≃_
        (UV.embed (Local.ell gaussian))
        (Bishop._*_
          Pi.inversePiSquared
          (Running.logBlocking running (suc edge)))

open FiniteEllBishopShellNormalization public

embeddedFiniteUniversalTermIsCanonicalShellFormula :
  ∀ {Mode gaussian running edge} →
  FiniteEllBishopShellNormalization gaussian running edge →
  Bishop._≃_
    (UV.embed (Local.oneLoopSU2Factor * Local.ell gaussian))
    (Bishop._*_
      (Bishop._*_
        (Embed.embed
          (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
        Pi.inversePiSquared)
      (Running.logBlocking running (suc edge)))
embeddedFiniteUniversalTermIsCanonicalShellFormula
    {gaussian = gaussian} {running = running} {edge = edge} normalization =
  BishopP.≃-trans
    (Embed.embedMul Local.oneLoopSU2Factor (Local.ell gaussian))
    (BishopP.≃-trans
      (BishopP.*-cong
        (UV.embedEqualityFromRational
          Local.oneLoopSU2Factor
          (SU2.su2InverseCouplingCoefficientExact))
        (finiteEllIsNormalizedPhysicalLog normalization))
      (BishopP.≃-symm
        (BishopP.*-assoc
          (Embed.embed
            (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
          Pi.inversePiSquared
          (Running.logBlocking running (suc edge)))))

finiteEllBishopShellNormalizationCompilerLevel : ProofLevel
finiteEllBishopShellNormalizationCompilerLevel = machineChecked

finiteEllPhysicalLogSameObjectLevel : ProofLevel
finiteEllPhysicalLogSameObjectLevel = conditional
