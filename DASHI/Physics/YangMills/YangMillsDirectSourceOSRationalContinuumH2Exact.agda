{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSRationalContinuumH2Exact where

------------------------------------------------------------------------
-- H2(i,iii) SOURCE-FIRST CONTINUUM/OS CONSTRUCTION ON THE RATIONAL CARRIER.
--
-- The selected Wilson covariance/mass-gap lane is rational-valued.  Keeping a
-- generic unrelated Scalar in the continuum bridge allowed H3 to choose a
-- second OS system and merely map both systems to the same endpoint Schwinger
-- family.  This owner fixes Scalar = ℚ and constructs the exact OS system that
-- H3 must consume.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YMClayContinuumConstructionSameObjectBridgeExact as Generic
import DASHI.Physics.YangMills.BalabanInfiniteVolumeContinuumLimits as IV
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

record RationalLiteralContinuumSameObjectBridge
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    : Set₂ where
  field
    continuumData :
      ∀ G →
      IV.InfiniteVolumeContinuumData
        (Top.Cutoff C) (Top.Observable C) (Top.Position C) ℚ

    topology :
      ∀ G → IV.DistributionTopology (continuumData G)

  generatedSystem :
    ∀ G →
    OS.ContinuumSchwingerSystem
      (Top.Observable C) (Top.Position C) ℚ
  generatedSystem G =
    IV.continuumSchwingerSystem (continuumData G) (topology G)

  generatedConvergence :
    ∀ G → IV.ContinuumLimitUnique (continuumData G) (topology G)
  generatedConvergence G =
    IV.convergesToContinuumWitness (continuumData G) (topology G)

  field
    systemToLiteralSchwinger :
      ∀ G →
      OS.ContinuumSchwingerSystem
        (Top.Observable C) (Top.Position C) ℚ →
      Top.SchwingerFamily C

    generatedSystemIsLiteralSchwinger :
      ∀ G →
      systemToLiteralSchwinger G (generatedSystem G)
      ≡ Top.schwinger Y G

    convergenceMeansLiteralContinuumLimit :
      ∀ G →
      IV.ContinuumLimitUnique (continuumData G) (topology G) →
      Top.IsContinuumLimitOf S G
        (Top.finiteMeasure Y G)
        (Top.continuumMeasure Y G)

    generatedSchwingerBelongsToLiteralMeasure :
      ∀ G →
      IV.ContinuumLimitUnique (continuumData G) (topology G) →
      Top.SchwingerBelongsToMeasure S
        (Top.continuumMeasure Y G)
        (systemToLiteralSchwinger G (generatedSystem G))

    generatedOSAxiomsMeanAcceptedLiteralAxioms :
      ∀ G →
      Top.SatisfiesAcceptedWightmanOrOSAxioms S G
        (systemToLiteralSchwinger G (generatedSystem G))

    reconstruction :
      ∀ G →
      OS.OSReconstructionAuthority
        (Top.Observable C) (Top.Position C) ℚ
        (generatedSystem G)

    hilbertToLiteral :
      ∀ G →
      OS.HilbertSpace (reconstruction G) →
      Top.HilbertSpace C

    hamiltonianToLiteral :
      ∀ G →
      OS.Hamiltonian (reconstruction G) →
      Top.Hamiltonian C

    reconstructedHilbertMeansLiteral :
      ∀ G →
      hilbertToLiteral G (OS.hilbertSpace (reconstruction G))
      ≡ Top.hilbertSpace Y G

    reconstructedHamiltonianMeansLiteral :
      ∀ G →
      hamiltonianToLiteral G (OS.hamiltonian (reconstruction G))
      ≡ Top.hamiltonian Y G

    generatedReconstructionMeansLiteralHilbert :
      ∀ G →
      Top.IsReconstructedHilbertSpace S G
        (systemToLiteralSchwinger G (generatedSystem G))
        (hilbertToLiteral G (OS.hilbertSpace (reconstruction G)))

    generatedReconstructionMeansPositiveSelfAdjoint :
      ∀ G →
      Top.IsPositiveSelfAdjointHamiltonian S
        (hilbertToLiteral G (OS.hilbertSpace (reconstruction G)))
        (hamiltonianToLiteral G (OS.hamiltonian (reconstruction G)))

open RationalLiteralContinuumSameObjectBridge public

asGenericContinuumBridge :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  RationalLiteralContinuumSameObjectBridge Y →
  Generic.LiteralContinuumSameObjectBridge Y
asGenericContinuumBridge bridge = record
  { Generic.LiteralContinuumSameObjectBridge.Scalar = ℚ
  ; Generic.LiteralContinuumSameObjectBridge.continuumData =
      continuumData bridge
  ; Generic.LiteralContinuumSameObjectBridge.topology =
      topology bridge
  ; Generic.LiteralContinuumSameObjectBridge.systemToLiteralSchwinger =
      systemToLiteralSchwinger bridge
  ; Generic.LiteralContinuumSameObjectBridge.generatedSystemIsLiteralSchwinger =
      generatedSystemIsLiteralSchwinger bridge
  ; Generic.LiteralContinuumSameObjectBridge.convergenceMeansLiteralContinuumLimit =
      convergenceMeansLiteralContinuumLimit bridge
  ; Generic.LiteralContinuumSameObjectBridge.generatedSchwingerBelongsToLiteralMeasure =
      generatedSchwingerBelongsToLiteralMeasure bridge
  ; Generic.LiteralContinuumSameObjectBridge.generatedOSAxiomsMeanAcceptedLiteralAxioms =
      generatedOSAxiomsMeanAcceptedLiteralAxioms bridge
  ; Generic.LiteralContinuumSameObjectBridge.reconstruction =
      reconstruction bridge
  ; Generic.LiteralContinuumSameObjectBridge.hilbertToLiteral =
      hilbertToLiteral bridge
  ; Generic.LiteralContinuumSameObjectBridge.hamiltonianToLiteral =
      hamiltonianToLiteral bridge
  ; Generic.LiteralContinuumSameObjectBridge.reconstructedHilbertMeansLiteral =
      reconstructedHilbertMeansLiteral bridge
  ; Generic.LiteralContinuumSameObjectBridge.reconstructedHamiltonianMeansLiteral =
      reconstructedHamiltonianMeansLiteral bridge
  ; Generic.LiteralContinuumSameObjectBridge.generatedReconstructionMeansLiteralHilbert =
      generatedReconstructionMeansLiteralHilbert bridge
  ; Generic.LiteralContinuumSameObjectBridge.generatedReconstructionMeansPositiveSelfAdjoint =
      generatedReconstructionMeansPositiveSelfAdjoint bridge
  }

asUnifiedContinuumYM :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  RationalLiteralContinuumSameObjectBridge Y →
  Five.UnifiedContinuumYMConstruction Y
asUnifiedContinuumYM bridge =
  Generic.unifiedContinuumYMFromSameObjectBridge
    (asGenericContinuumBridge bridge)

directRationalContinuumCompilerLevel : ProofLevel
directRationalContinuumCompilerLevel =
  Generic.continuumOSConstructionCompilerLevel

directRationalContinuumPhysicalInstantiationLevel : ProofLevel
directRationalContinuumPhysicalInstantiationLevel =
  Generic.literalContinuumSameObjectAttachmentLevel
