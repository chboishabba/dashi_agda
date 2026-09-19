module DASHI.Physics.YangMills.YMClayContinuumConstructionSameObjectBridgeExact where

------------------------------------------------------------------------
-- Literal A / continuum-construction same-object bridge.
--
-- The generic continuum machinery already constructs a genuine
-- ContinuumSchwingerSystem from:
--
--   uniform Schwinger bounds
--   -> precompactness
--   -> subsequence extraction
--   -> uniqueness
--   -> OS0--OS5 closure.
--
-- This module does not add another continuum theorem.  It compiles that
-- existing constructed OS object into the literal Clay
-- UnifiedContinuumYMConstruction on ONE LiteralYangMillsConstruction Y.
--
-- The remaining fields are deliberately only semantic/same-object attachments:
-- the generic continuum convergence witness must mean the literal
-- IsContinuumLimitOf predicate, the constructed OS system must denote the
-- literal Schwinger family, and the OS reconstruction's Hilbert/Hamiltonian
-- values must be the literal Y values.  No unrelated continuum family or
-- Hamiltonian can be paired beside Y.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanInfiniteVolumeContinuumLimits as IV
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

record LiteralContinuumSameObjectBridge
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₂ where
  field
    Scalar : Set

    continuumData :
      ∀ G →
      IV.InfiniteVolumeContinuumData
        (Top.Cutoff C) (Top.Observable C) (Top.Position C) Scalar

    topology :
      ∀ G → IV.DistributionTopology (continuumData G)

  generatedSystem :
    ∀ G → OS.ContinuumSchwingerSystem
      (Top.Observable C) (Top.Position C) Scalar
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
        (Top.Observable C) (Top.Position C) Scalar →
      Top.SchwingerFamily C

    generatedSystemIsLiteralSchwinger :
      ∀ G →
      systemToLiteralSchwinger G (generatedSystem G)
      ≡ Top.schwinger Y G

    convergenceMeansLiteralContinuumLimit :
      ∀ G →
      IV.ContinuumLimitUnique (continuumData G) (topology G) →
      Top.IsContinuumLimitOf S G
        (Top.finiteMeasure Y G) (Top.continuumMeasure Y G)

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
        (Top.Observable C) (Top.Position C) Scalar (generatedSystem G)

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

open LiteralContinuumSameObjectBridge public

literalSchwingerBelongs :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  (bridge : LiteralContinuumSameObjectBridge Y) →
  ∀ G →
  Top.SchwingerBelongsToMeasure S
    (Top.continuumMeasure Y G) (Top.schwinger Y G)
literalSchwingerBelongs bridge G =
  subst
    (λ schwingerFamily →
      Top.SchwingerBelongsToMeasure _
        (Top.continuumMeasure _ G) schwingerFamily)
    (generatedSystemIsLiteralSchwinger bridge G)
    (generatedSchwingerBelongsToLiteralMeasure bridge G
      (generatedConvergence bridge G))

literalAcceptedOSAxioms :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  (bridge : LiteralContinuumSameObjectBridge Y) →
  ∀ G →
  Top.SatisfiesAcceptedWightmanOrOSAxioms S G (Top.schwinger Y G)
literalAcceptedOSAxioms bridge G =
  subst
    (λ schwingerFamily →
      Top.SatisfiesAcceptedWightmanOrOSAxioms _ G schwingerFamily)
    (generatedSystemIsLiteralSchwinger bridge G)
    (generatedOSAxiomsMeanAcceptedLiteralAxioms bridge G)

literalReconstructedHilbert :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  (bridge : LiteralContinuumSameObjectBridge Y) →
  ∀ G →
  Top.IsReconstructedHilbertSpace S G
    (Top.schwinger Y G) (Top.hilbertSpace Y G)
literalReconstructedHilbert bridge G =
  subst
    (λ hilbert →
      Top.IsReconstructedHilbertSpace _
        G (Top.schwinger _ G) hilbert)
    (reconstructedHilbertMeansLiteral bridge G)
    (subst
      (λ schwingerFamily →
        Top.IsReconstructedHilbertSpace _
          G schwingerFamily
          (hilbertToLiteral bridge G
            (OS.hilbertSpace (reconstruction bridge G))))
      (generatedSystemIsLiteralSchwinger bridge G)
      (generatedReconstructionMeansLiteralHilbert bridge G))

literalPositiveSelfAdjointHamiltonian :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  (bridge : LiteralContinuumSameObjectBridge Y) →
  ∀ G →
  Top.IsPositiveSelfAdjointHamiltonian S
    (Top.hilbertSpace Y G) (Top.hamiltonian Y G)
literalPositiveSelfAdjointHamiltonian bridge G =
  subst
    (λ hamiltonian →
      Top.IsPositiveSelfAdjointHamiltonian _
        (Top.hilbertSpace _ G) hamiltonian)
    (reconstructedHamiltonianMeansLiteral bridge G)
    (subst
      (λ hilbert →
        Top.IsPositiveSelfAdjointHamiltonian _
          hilbert
          (hamiltonianToLiteral bridge G
            (OS.hamiltonian (reconstruction bridge G))))
      (reconstructedHilbertMeansLiteral bridge G)
      (generatedReconstructionMeansPositiveSelfAdjoint bridge G))

unifiedContinuumYMFromSameObjectBridge :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralContinuumSameObjectBridge Y →
  Five.UnifiedContinuumYMConstruction Y
unifiedContinuumYMFromSameObjectBridge bridge = record
  { continuumLimit =
      λ G →
        convergenceMeansLiteralContinuumLimit bridge G
          (generatedConvergence bridge G)
  ; schwingerBelongsToContinuumMeasure =
      literalSchwingerBelongs bridge
  ; acceptedWightmanOrOSAxioms =
      literalAcceptedOSAxioms bridge
  ; reconstructedHilbertSpace =
      literalReconstructedHilbert bridge
  ; positiveSelfAdjointHamiltonian =
      literalPositiveSelfAdjointHamiltonian bridge
  }

continuumOSConstructionCompilerLevel : ProofLevel
continuumOSConstructionCompilerLevel = machineChecked

literalContinuumSameObjectAttachmentLevel : ProofLevel
literalContinuumSameObjectAttachmentLevel = conditional
