module DASHI.Foundations.HeisenbergAppraisalEquivarianceExact where

------------------------------------------------------------------------
-- H1.01/H2.01 ORIGINAL APPRAISAL EQUIVARIANCE ADMISSION FRONTIER.
--
-- A TYPE-CORRECT CONTRACT, NOT AN INHABITED CLAIM:
-- The original relational update kernel is asymmetric and
-- context-indexed. It does not currently supply a canonical
-- H_6 action on the original 144-cell relation field.
--
-- Payment requires actual selected source implementations of:
--  (1) appraisal updates, indexed by original participants/time;
--  (2) an original H_6 representation/action on 144-cell relations;
--  (3) re-labeling of H_6 elements under appraisal;
--  (4) a coherent *residual correction* with OBSERVED CELL
--      preservation and the original source action law;
--  (5) cellwise commutation in the full original relation field.
--
-- A correction is NOT automatically a 2-cocycle, a quantum
-- adjoint action, unitary representation, or world/ITIR semantic
-- equivalence. Those require independent source proofs.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369RelationalUpdateKernelExact as Update
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Relation
import DASHI.Foundations.TernaryThirteenOriginalRelational144NonIdentificationExact as Coarse
import DASHI.Foundations.TernaryThirteenOriginalRelationResidualReopeningExact as Residual
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H

-- Source-owner pointwise equality does not assume function
-- extensionality of StageRelationField functions.
RelationalPointwiseEquality :
  Relation.StageRelationField →
  Relation.StageRelationField → Set
RelationalPointwiseEquality left right =
  (cell : Relation.StageRelation144) → left cell ≡ right cell

-- This is the independently payable same-object action contract.
-- Appraisal acts on the actual original relation field, not on
-- an invented 13-word copy of the state.
record OriginalAppraisalHeisenbergAction
    (kernel : Update.RelationalUpdateKernel)
    (Time : Set) : Set₁ where
  field
    appraisalUpdate :
      Update.Participant kernel → Time →
      Relation.StageRelationField → Relation.StageRelationField

    groupAction :
      H.Heisenberg6 →
      Relation.StageRelationField → Relation.StageRelationField

    groupActionUnit :
      (field : Relation.StageRelationField)
      (cell : Relation.StageRelation144) →
      groupAction H.identityH field cell ≡ field cell

    groupActionComposition :
      (g h : H.Heisenberg6)
      (field : Relation.StageRelationField)
      (cell : Relation.StageRelation144) →
      groupAction (H.compose g h) field cell
        ≡ groupAction g (groupAction h field) cell

    -- This must be sourced from the intended relational/appraisal
    -- meaning of a transformed group element. No abstract
    -- coordinate bijection manufactures it.
    relabelGroup :
      Update.Participant kernel → Time →
      H.Heisenberg6 → H.Heisenberg6

    relabelPreservesMultiplication :
      (participant : Update.Participant kernel)
      (time : Time)
      (g h : H.Heisenberg6) →
      relabelGroup participant time (H.compose g h)
        ≡ H.compose (relabelGroup participant time g)
                    (relabelGroup participant time h)

    relabelPreservesIdentity :
      (participant : Update.Participant kernel)
      (time : Time) →
      relabelGroup participant time H.identityH ≡ H.identityH

    -- Source-selected correction on the FULL original relation.
    -- This is a candidate residual transport, NOT a 2-cocycle
    -- unless a separate cocycle law is proved.
    residualCorrection :
      Update.Participant kernel → Time →
      H.Heisenberg6 →
      Relation.StageRelationField → Relation.StageRelationField

    correctionPreservesCoarse :
      (participant : Update.Participant kernel)
      (time : Time)
      (g : H.Heisenberg6)
      (field : Relation.StageRelationField) →
      Coarse.relationToThirteen
        (residualCorrection participant time g field)
        ≡ Coarse.relationToThirteen field

    -- This is the actual requested cellwise equivariance with
    -- explicit correction. Its witnesses must be sourced from
    -- real appraisal and group-action operations.
    appraisalEquivariantUpToResidual :
      (participant : Update.Participant kernel)
      (time : Time)
      (g : H.Heisenberg6)
      (field : Relation.StageRelationField)
      (cell : Relation.StageRelation144) →
      appraisalUpdate participant time (groupAction g field) cell
      ≡
      residualCorrection participant time g
        (groupAction (relabelGroup participant time g)
          (appraisalUpdate participant time field)) cell

open OriginalAppraisalHeisenbergAction public

-- An independently required provenance/observation boundary:
-- the existing 13+131 codec can recover a correction at every
-- original addressed relation cell; it does not show that the
-- correction is physically or semantically admissible.
correctionReopensAt :
  (kernel : Update.RelationalUpdateKernel)
  (Time : Set)
  (action : OriginalAppraisalHeisenbergAction kernel Time)
  (participant : Update.Participant kernel)
  (time : Time)
  (g : H.Heisenberg6)
  (field : Relation.StageRelationField)
  (cell : Relation.StageRelation144) →
  Residual.reopenNormalized
    (Coarse.relationToThirteen
      (residualCorrection action participant time g field))
    (Residual.maskToResidual131
      (residualCorrection action participant time g field))
    cell
  ≡ residualCorrection action participant time g field cell
correctionReopensAt kernel Time action participant time g field cell =
  Residual.reopenNormalizedExact
    (residualCorrection action participant time g field) cell

-- The remaining H1.01 source admission is an *inhabitant*
-- of OriginalAppraisalHeisenbergAction for the actually
-- selected original relational kernel and time carrier.
-- There is intentionally NO canonical inhabitant here.
