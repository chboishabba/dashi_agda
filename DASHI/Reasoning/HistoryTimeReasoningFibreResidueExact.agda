module DASHI.Reasoning.HistoryTimeReasoningFibreResidueExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.Reasoning.HistoryTimeRelationalReasoningFibreExact as Fibre
import DASHI.Reasoning.HistoryTimeReasoningFibreTransportExact as Transport
import DASHI.Reasoning.HistoryTimeReasoningFibreTransportPathExact as Path

------------------------------------------------------------------------
-- PATH RESIDUE OVER THE HISTORY/TIME REASONING FIBRE
--
-- A transport path retains more than endpoints.  This owner gives applications
-- an explicit residue observer on reasoning-fibre points and proves that a
-- residue deposited by one governed step remains present over an arbitrarily
-- long retained path when every later step is no-erasing.
------------------------------------------------------------------------

record FibreResiduePolicy
    (carrier : Fibre.HistoryTimeArtifactCarrier) : Set₁ where
  constructor fibreResiduePolicy
  field
    residueAt : Fibre.ReasoningFibrePoint carrier → Residue.ResidueFlag
    residueReference : String

open FibreResiduePolicy public

record StepPreservesResidue
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    (policy : FibreResiduePolicy carrier)
    {kind : Transport.TransitionKind}
    {before after : Fibre.ReasoningFibrePoint carrier}
    (step : Path.AttachedGovernedStep fabric kind before after) : Set where
  constructor stepPreservesResidue
  field
    noErase :
      residueAt policy before ≡ Residue.residuePresent →
      residueAt policy after ≡ Residue.residuePresent

open StepPreservesResidue public

data PathPreservesResidue
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    (policy : FibreResiduePolicy carrier) :
    ∀ {start finish} →
    Path.GovernedTransportPath fabric start finish → Set₁ where
  preservesRefl :
    ∀ {point receipt} →
    PathPreservesResidue policy (Path.pathRefl {point = point} receipt)
  preservesStep :
    ∀ {before middle after kind}
      {step : Path.AttachedGovernedStep fabric kind before middle}
      {rest : Path.GovernedTransportPath fabric middle after} →
    StepPreservesResidue policy step →
    PathPreservesResidue policy rest →
    PathPreservesResidue policy (Path.pathStep step rest)

pathPreservesPresentResidue :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {policy : FibreResiduePolicy carrier}
    {start finish : Fibre.ReasoningFibrePoint carrier}
    {path : Path.GovernedTransportPath fabric start finish} →
  PathPreservesResidue policy path →
  residueAt policy start ≡ Residue.residuePresent →
  residueAt policy finish ≡ Residue.residuePresent
pathPreservesPresentResidue preservesRefl present = present
pathPreservesPresentResidue
  (preservesStep stepPreservation restPreservation) present =
  pathPreservesPresentResidue
    restPreservation
    (noErase stepPreservation present)

------------------------------------------------------------------------
-- Deposited residue and no-erasure are separate receipts.
------------------------------------------------------------------------

record PathResidueDeposition
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    (policy : FibreResiduePolicy carrier)
    {start finish : Fibre.ReasoningFibrePoint carrier}
    (path : Path.GovernedTransportPath fabric start finish) : Set₁ where
  constructor pathResidueDeposition
  field
    beforeAbsent : residueAt policy start ≡ Residue.residueAbsent
    afterPresent : residueAt policy finish ≡ Residue.residuePresent
    depositionReference : String

open PathResidueDeposition public

record PersistentPathResidue
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    (policy : FibreResiduePolicy carrier)
    {start finish : Fibre.ReasoningFibrePoint carrier}
    (path : Path.GovernedTransportPath fabric start finish) : Set₁ where
  constructor persistentPathResidue
  field
    preservation : PathPreservesResidue policy path
    finalResiduePresent : residueAt policy start ≡ Residue.residuePresent
    persistenceReference : String

open PersistentPathResidue public

------------------------------------------------------------------------
-- Composition: residue preservation composes structurally with path append.
------------------------------------------------------------------------

appendPathPreservesResidue :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {policy : FibreResiduePolicy carrier}
    {a b c : Fibre.ReasoningFibrePoint carrier}
    {left : Path.GovernedTransportPath fabric a b}
    {right : Path.GovernedTransportPath fabric b c} →
  PathPreservesResidue policy left →
  PathPreservesResidue policy right →
  PathPreservesResidue policy (Path.appendTransportPath left right)
appendPathPreservesResidue preservesRefl rightPreserves = rightPreserves
appendPathPreservesResidue
  (preservesStep stepPreservation restPreservation)
  rightPreserves =
  preservesStep stepPreservation
    (appendPathPreservesResidue restPreservation rightPreserves)

------------------------------------------------------------------------
-- Reconvergence: a coarse endpoint observer may identify two final states even
-- when their retained path residues differ.  The residue channel therefore
-- carries genuine extra history-sensitive information.
------------------------------------------------------------------------

record ResidueReconvergence
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    (policy : FibreResiduePolicy carrier) : Set₁ where
  constructor residueReconvergence
  field
    Coarse : Set
    observeCoarse : Fibre.ReasoningFibrePoint carrier → Coarse
    left right : Fibre.ReasoningFibrePoint carrier
    coarseSame : observeCoarse left ≡ observeCoarse right
    leftResidueAbsent : residueAt policy left ≡ Residue.residueAbsent
    rightResiduePresent : residueAt policy right ≡ Residue.residuePresent
    reconvergenceReference : String

open ResidueReconvergence public

residueReconvergenceBlocksResidueDescent :
  ∀ {carrier}
    {policy : FibreResiduePolicy carrier} →
  (collision : ResidueReconvergence policy) →
  Residue.ResidueDescendsThrough
    (ResidueReconvergence.observeCoarse collision)
    (residueAt policy) →
  ⊥
residueReconvergenceBlocksResidueDescent collision =
  Residue.coarseCollisionAcrossResidueBlocksDescent
    (ResidueReconvergence.coarseSame collision)
    (ResidueReconvergence.leftResidueAbsent collision)
    (ResidueReconvergence.rightResiduePresent collision)

record HistoryTimeReasoningFibreResidueBoundary : Set where
  constructor historyTimeReasoningFibreResidueBoundary
  field
    pathCanDepositPersistentResidue : Bool
    pathCanDepositPersistentResidueIsTrue :
      pathCanDepositPersistentResidue ≡ true
    pathAppendCanPreserveNoErasureReceipt : Bool
    pathAppendCanPreserveNoErasureReceiptIsTrue :
      pathAppendCanPreserveNoErasureReceipt ≡ true
    sameCoarseEndpointDeterminesResidue : Bool
    sameCoarseEndpointDeterminesResidueIsFalse :
      sameCoarseEndpointDeterminesResidue ≡ false
    residueDifferenceRequiresEndpointDifference : Bool
    residueDifferenceRequiresEndpointDifferenceIsFalse :
      residueDifferenceRequiresEndpointDifference ≡ false

canonicalHistoryTimeReasoningFibreResidueBoundary :
  HistoryTimeReasoningFibreResidueBoundary
canonicalHistoryTimeReasoningFibreResidueBoundary =
  historyTimeReasoningFibreResidueBoundary
    true refl
    true refl
    false refl
    false refl
