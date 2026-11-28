module DASHI.Moonshine.CM163BishopOriginalSameSourceClosureExact where

-- SOURCE-WRITTEN, NOT YET KERNEL-CHECKED.
-- This is a single original-source boundary, not a new numerical CM
-- point or freely selected E4, j, H, J1, or pi.
-- Consume original CM root + native factorial hypergeometric square,
-- one common chain derivative and the ACTUAL reciprocal signed two-jet.
-- Each field below is deliberately a producer obligation, not a postulate.

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
open R using (ℝ; _≃_; _*_; _-_; _⋆)
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as Reduction
import DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact as Disk
import DASHI.Moonshine.JInvariantBishopCM163E4JetPeriodExact as Jet
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as Norm
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as End
import DASHI.Foundations.BishopChudnovskyNativeRealExact as Native
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact as Raw
import DASHI.Foundations.BishopChudnovskySignedCrossReflectionExact as Cross

-- a,b are first/second original q Euler derivatives of the *same* j.
-- s,t,u,v are S2,S3,P2,P3 of the *same* original Hecke product.
-- l is a derivative of the *same* hypergeometric family H.
module At (a b s t u v l : ℝ) where

  record OriginalCMProducers : Set where
    field
      -- The actual selected guarded q point and literal signed root.
      cmRoot : Reduction.CMRoot

      -- The actual existing factorial series limits, not newly chosen H,J1.
      hyperSquare : Reduction.HyperSquare
      chainZ : (Reduction.X * l) ≃ (Reduction.Y * Reduction.E.J₁)
      chainSquare : (Norm.six * Reduction.E.H * l) ≃ Reduction.U

      -- Do not replace true apartness by a negated equality or finite scan.
      firstApart : R._≄0 (Disk.A Reduction.p a)
      packetApart : R._≄0 s

      -- Both actual original q jets and the literal Hecke packet ratios.
      firstQ : Reduction.FirstQJet a
      secondQ : Reduction.SecondQJet b
      ratioP2 : (((+ 41 / 1) ⋆) * u) ≃ (((+ 163 / 1) ⋆) * s)
      ratioP3 : ((((+ 41 / 1) ⋆) * v) -
        (((+ 326 / 1) ⋆) * t)) ≃
        ((((+ 163 / 1) ⋆) * Reduction.κ) * s)

      -- Original (not arbitrary surrogate) analytic Hecke cross
      -- differentiated at the actual reciprocal fixed point.
      crossResidual :
        Disk.literalResidual (Disk.A Reduction.p a)
          (Disk.diskB Reduction.p a b) s t u v ≃ R.0ℝ

  open OriginalCMProducers

  -- Previously separate producer branches weld here, coarse -> fine.
  clearedHyperJet : (w : OriginalCMProducers) → Reduction.ClearedHyperJet
  clearedHyperJet w =
    Reduction.clearedFromChain l (chainZ w) (chainSquare w)

  actualSignedJet : (w : OriginalCMProducers) → Reduction.SignedJet
  actualSignedJet w =
    Disk.signedJetFromLiteral a b s t u v
      (firstApart w) (packetApart w) (firstQ w) (secondQ w)
      (ratioP2 w) (ratioP3 w) (crossResidual w)

  -- Existing theorem supplies all terminal algebra; no new period axiom.
  nativePeriod : (w : OriginalCMProducers) → End.NativePeriod
  nativePeriod w = Reduction.periodFromThree
    (cmRoot w) (hyperSquare w) (clearedHyperJet w) (actualSignedJet w)

  -- Identical ORIGINAL Bishop reals, not a new series-defined pi.
  sameReal : (w : OriginalCMProducers) →
    R._≃_ Native.chudnovskyReal Machin.bishopMachinPi
  sameReal w = End.periodToSameReal (nativePeriod w)

  universalExpandedCross : (w : OriginalCMProducers) →
    (k : Nat) → Cross.ExpandedCross k
  universalExpandedCross w = End.periodToExpanded (nativePeriod w)

  universalRawCross : (w : OriginalCMProducers) →
    (k : Nat) → Raw.RawCross k
  universalRawCross w = Reduction.rawFromThree
    (cmRoot w) (hyperSquare w) (clearedHyperJet w) (actualSignedJet w)

  -- Bidirectional local geometry: under the SAME cubic, the signed jet
  -- and terminal correction are interconvertible, with no new division
  -- and no choice of a conjugate sign.
  cubic : (w : OriginalCMProducers) → Reduction.Cubic
  cubic w = Guard.Root.rootToCubic (cmRoot w)

  correction : (w : OriginalCMProducers) → Jet.Correction
  correction w = Reduction.correctionFromSigned (cubic w) (actualSignedJet w)

  signedFromCorrection : (w : OriginalCMProducers) →
    Jet.Correction → Reduction.SignedJet
  signedFromCorrection w = Reduction.signedFromCorrection (cubic w)

  correctionFromSigned : (w : OriginalCMProducers) →
    Reduction.SignedJet → Jet.Correction
  correctionFromSigned w = Reduction.correctionFromSigned (cubic w)
