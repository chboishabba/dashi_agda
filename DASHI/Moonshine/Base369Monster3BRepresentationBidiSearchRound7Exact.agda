module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound7Exact where

------------------------------------------------------------------------
-- ROUND 7: SAME-ELEMENT 3B KERNEL/VOA FRONTIER
--
-- Round 6 reduced the 729 appraisal bridge to compiler output after literal
-- zeta-sector recognition.  The next duplication was between:
--
--   * the selected Monster element acting on the literal VOA carrier; and
--   * the abstract actual-kernel conjugacy class certified by AtlasRep/CTblLib.
--
-- MonsterGradedVOAActual3BKernelSameElementBidiExact makes that missing weld an
-- explicit receipt.  After it is supplied, the 65610 central-zeta amplitude
-- and ninety-fold Heisenberg character isotypy are already compiler output.
-- Character isotypy still does NOT construct ActualZetaSectorRecognition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

record Round7Frontier : Set where
  constructor round7Frontier
  field
    appraisalToX6Owned : Bool
    appraisalMonomialHeisenbergActionGenerated : Bool
    literalVOAActionOwned : Bool
    gradedTraceAndLiteralActionSameElementWeldOwned : Bool
    selected3BPhaseSourceOnSameVOAOwned : Bool

    selectedElementToActualKernelClassReceiptLive : Bool
    certifiedKernelClassFusionToMonster3BLive : Bool
    selectedGradeTwoTrace53AttachmentLive : Bool

    centralZetaAmplitude65610Downstream : Bool
    ninetyHeisenbergCharacterIsotypyDownstream : Bool
    separateMultiplicity90ComputationNeeded : Bool

    actualZetaSectorRecognitionLive : Bool
    separateActual729RecognitionNeededAfterZetaRecognition : Bool
    actual729AppraisalSlicesDownstream : Bool
    fin90InertiaActionDownstream : Bool
    sameActionTwelvePlusSeventyEightDownstream : Bool

    trace53CreatesStableFiftyThreeRepresentation : Bool
    fullMonsterActionOnHyperfabricEstablished : Bool

canonicalRound7Frontier : Round7Frontier
canonicalRound7Frontier =
  round7Frontier
    true true true true true
    true true true
    true true false
    true false true true true
    false false

------------------------------------------------------------------------
-- Human-readable ownership classification.
------------------------------------------------------------------------

data Round7Status : Set where
  OWNED GENERATED LIVE DOWNSTREAM PRUNED PARALLEL : Round7Status

data Round7Leaf : Set where
  appraisalX6
  appraisalMonomialAction
  literalVOAAction
  sameElementTraceActionWeld
  selected3BPhaseSource
  elementKernelClassAttachment
  kernelClassFusion3B
  selectedTrace53
  centralZetaAmplitude65610
  ninetyHeisenbergIsotypy
  zetaRecognition
  actual729Recognition
  actual729Slices
  fin90Inertia
  twelvePlusSeventyEight
  residual53Action
  : Round7Leaf

round7Status : Round7Leaf → Round7Status
round7Status appraisalX6 = OWNED
round7Status appraisalMonomialAction = GENERATED
round7Status literalVOAAction = OWNED
round7Status sameElementTraceActionWeld = OWNED
round7Status selected3BPhaseSource = OWNED
round7Status elementKernelClassAttachment = LIVE
round7Status kernelClassFusion3B = LIVE
round7Status selectedTrace53 = LIVE
round7Status centralZetaAmplitude65610 = DOWNSTREAM
round7Status ninetyHeisenbergIsotypy = DOWNSTREAM
round7Status zetaRecognition = LIVE
round7Status actual729Recognition = PRUNED
round7Status actual729Slices = DOWNSTREAM
round7Status fin90Inertia = DOWNSTREAM
round7Status twelvePlusSeventyEight = DOWNSTREAM
round7Status residual53Action = PARALLEL
