module DASHI.Physics.CondensedMatter.YbSbTwoMajoranaQuantumComputerBridgeExact where

------------------------------------------------------------------------
-- ATTRIBUTION / CROSS-POLLINATION
--
-- SOURCE — Kataria et al.:
-- the effective YbSb2 INT BdG model supports a modeled surface branch
-- interpreted as Majorana.
--
-- EXISTING DASHI OWNERS REUSED HERE:
-- * DASHI.Physics.QFT.BraidingMorphismReceipt:
--   the current finite prime-lane braiding surface is only the symmetric
--   bosonic swap; no non-Abelian braid intertwiner is constructed.
-- * DASHI.Programmes.QuantumExecutablePromotionReceiptExact:
--   runtime acceptance is not, by itself, physical-theory promotion.
-- * DASHI.Physics.QFT.AnyonicSectorPhysicsReceipt:
--   anyonic sectors and their dimensional/physical identification are kept
--   behind explicit promotion boundaries.
--
-- DASHI CONTRIBUTION HERE:
-- introduce the exact seam between a Majorana surface-mode witness and a
-- topological quantum-computer claim.  A modeled Majorana branch is not a
-- qubit; a qubit is not a braid representation; a braid representation is
-- not universal computation; runtime execution is not physical validation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.CondensedMatter.YbSbTwoBdGSymmetryBoundaryExact as BdG
import DASHI.Physics.QFT.BraidingMorphismReceipt as Braid
import DASHI.Physics.QFT.AnyonicSectorPhysicsReceipt as Anyon
import DASHI.Programmes.QuantumExecutablePromotionReceiptExact as QExec

record MajoranaPhysicalPlatform : Set₁ where
  field
    surfaceModeWitness : BdG.MajoranaSurfaceWitness

    IsolatedDefectMode : Set
    isolatedDefectModeWitness : IsolatedDefectMode

    FermionParityProtected : Set
    fermionParityProtectedWitness : FermionParityProtected

open MajoranaPhysicalPlatform public

record MajoranaLogicalEncoding
    (platform : MajoranaPhysicalPlatform) : Set₁ where
  field
    LogicalBasis : Set
    encode : LogicalBasis → Set

    parityEncodingIsPhysical : Set
    parityEncodingWitness : parityEncodingIsPhysical

open MajoranaLogicalEncoding public

record MajoranaBraidGateLayer
    {platform : MajoranaPhysicalPlatform}
    (encoding : MajoranaLogicalEncoding platform) : Set₁ where
  field
    BraidWord : Set
    LogicalGate : Set

    interpretBraid : BraidWord → LogicalGate

    NonAbelianRepresentation : Set
    nonAbelianRepresentationWitness : NonAbelianRepresentation

    PreservesCodeSpace : Set
    preservesCodeSpaceWitness : PreservesCodeSpace

open MajoranaBraidGateLayer public

record MajoranaComputationLayer
    {platform : MajoranaPhysicalPlatform}
    {encoding : MajoranaLogicalEncoding platform}
    (braids : MajoranaBraidGateLayer encoding) : Set₁ where
  field
    Circuit : Set
    runCircuit : Circuit → Set

    FaultProtectedLogicalAction : Set
    faultProtectedLogicalActionWitness :
      FaultProtectedLogicalAction

open MajoranaComputationLayer public

------------------------------------------------------------------------
-- Universality boundary.
--
-- Ising/Majorana braiding alone is not promoted here to universal quantum
-- computation.  Universality requires an independently supplied completion
-- resource (for example a non-topological gate, measurement-assisted
-- operation, magic-state resource, or another independently justified
-- completion mechanism).
------------------------------------------------------------------------

record UniversalCompletion
    {platform : MajoranaPhysicalPlatform}
    {encoding : MajoranaLogicalEncoding platform}
    {braids : MajoranaBraidGateLayer encoding}
    (computation : MajoranaComputationLayer braids) : Set₁ where
  field
    ExtraResource : Set
    extraResourceWitness : ExtraResource

    UniversalGateSet : Set
    universalGateSetWitness : UniversalGateSet

open UniversalCompletion public

------------------------------------------------------------------------
-- Existing DASHI braid receipt cannot discharge the Majorana non-Abelian
-- braid obligation.
------------------------------------------------------------------------

canonicalPrimeLaneHasNoNonAbelianIntertwiner :
  Braid.nonAbelianBraidingIntertwinerConstructed
    Braid.canonicalBraidingMorphismReceipt
  ≡ false
canonicalPrimeLaneHasNoNonAbelianIntertwiner =
  Braid.finitePrimeLaneBraidingDoesNotConstructNonAbelianIntertwiners

canonicalPrimeLaneCannotWitnessNonAbelianMajoranaBraiding :
  Braid.nonAbelianBraidingIntertwinerConstructed
    Braid.canonicalBraidingMorphismReceipt
  ≡ true →
  ⊥
canonicalPrimeLaneCannotWitnessNonAbelianMajoranaBraiding ()

------------------------------------------------------------------------
-- Existing quantum-runtime boundary remains active downstream.
------------------------------------------------------------------------

runtimeAcceptanceIsNotPhysicalPromotion :
  QExec.runtimeAcceptedMeansEstablishedPhysicalTheory
    QExec.canonicalQuantumExecutablePromotionBoundary
  ≡ false
runtimeAcceptanceIsNotPhysicalPromotion =
  QExec.runtimeAcceptedMeansEstablishedPhysicalTheoryIsFalse
    QExec.canonicalQuantumExecutablePromotionBoundary

------------------------------------------------------------------------
-- Terminal bridge package.  Every seam must be supplied independently.
------------------------------------------------------------------------

record YbSbTwoMajoranaQuantumComputerBridge : Set₁ where
  field
    platform : MajoranaPhysicalPlatform
    encoding : MajoranaLogicalEncoding platform
    braidLayer : MajoranaBraidGateLayer encoding
    computationLayer : MajoranaComputationLayer braidLayer

    sourceModelIdentifiedWithPhysicalMajoranaPlatform : Set
    sourceModelIdentificationWitness :
      sourceModelIdentifiedWithPhysicalMajoranaPlatform

    encodedReadoutExperimentallyResolved : Set
    encodedReadoutWitness :
      encodedReadoutExperimentallyResolved

open YbSbTwoMajoranaQuantumComputerBridge public

-- No canonical inhabitant is provided: the paper's modeled surface branch
-- does not by itself discharge isolation, parity-qubit encoding, non-Abelian
-- braiding, protected logical action, or experimental readout.
