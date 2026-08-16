module DASHI.Biology.Physical.HierarchicalGoalConstraintCompilerExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
-- Michael Levin and Christopher J. Martyniuk,
-- "The bioelectric code: An ancient computational medium for dynamic control
-- of growth and form", Biosystems 164 (2018), 76-93.
-- DOI: 10.1016/j.biosystems.2017.08.009.
--
-- A higher-scale goal constrains a family of admissible lower-scale goals.  It
-- does not decode to one mandatory microscopic trajectory.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data OrganismGoal : Set where
  viableBody : OrganismGoal

data OrganGoal : Set where
  leftHand rightHand heart : OrganGoal

data TissueGoal : Set where
  digitField tendonInterface vascularInterface cardiacWall : TissueGoal

data CellGoal : Set where
  divide migrate differentiate adhere quiesce : CellGoal

data MolecularGoal : Set where
  expressChannel expressAdhesion remodelCytoskeleton maintainATP : MolecularGoal

data OrganRefines : OrganGoal → OrganismGoal → Set where
  leftHandSupportsBody : OrganRefines leftHand viableBody
  rightHandSupportsBody : OrganRefines rightHand viableBody
  heartSupportsBody : OrganRefines heart viableBody

data TissueRefines : TissueGoal → OrganGoal → Set where
  digitRefinesLeftHand : TissueRefines digitField leftHand
  tendonRefinesLeftHand : TissueRefines tendonInterface leftHand
  vascularRefinesLeftHand : TissueRefines vascularInterface leftHand
  cardiacWallRefinesHeart : TissueRefines cardiacWall heart

data CellRefines : CellGoal → TissueGoal → Set where
  divideRefinesDigit : CellRefines divide digitField
  migrateRefinesDigit : CellRefines migrate digitField
  differentiateRefinesDigit : CellRefines differentiate digitField
  adhereRefinesTendon : CellRefines adhere tendonInterface
  differentiateRefinesVascular : CellRefines differentiate vascularInterface

data MolecularRefines : MolecularGoal → CellGoal → Set where
  channelRefinesDifferentiate : MolecularRefines expressChannel differentiate
  adhesionRefinesAdhere : MolecularRefines expressAdhesion adhere
  cytoskeletonRefinesMigrate : MolecularRefines remodelCytoskeleton migrate
  atpRefinesDivide : MolecularRefines maintainATP divide

------------------------------------------------------------------------
-- One high-level goal genuinely has multiple feasible refinements.
------------------------------------------------------------------------

leftHandHasDistinctTissueRefinements :
  Σ TissueGoal (λ first →
    Σ TissueGoal (λ second →
      TissueRefines first leftHand ×
      TissueRefines second leftHand ×
      first ≢ second))
leftHandHasDistinctTissueRefinements =
  digitField ,
  (tendonInterface ,
    (digitRefinesLeftHand ,
      (tendonRefinesLeftHand , λ ()) ))

digitFieldHasDistinctCellPolicies :
  Σ CellGoal (λ first →
    Σ CellGoal (λ second →
      CellRefines first digitField ×
      CellRefines second digitField ×
      first ≢ second))
digitFieldHasDistinctCellPolicies =
  divide ,
  (migrate ,
    (divideRefinesDigit ,
      (migrateRefinesDigit , λ ()) ))

------------------------------------------------------------------------
-- Proof-bearing hierarchical delegation chain.
------------------------------------------------------------------------

record GoalDelegationChain : Set where
  constructor goalDelegationChain
  field
    organism : OrganismGoal
    organ : OrganGoal
    tissue : TissueGoal
    cell : CellGoal
    molecular : MolecularGoal
    organRefinement : OrganRefines organ organism
    tissueRefinement : TissueRefines tissue organ
    cellRefinement : CellRefines cell tissue
    molecularRefinement : MolecularRefines molecular cell

open GoalDelegationChain public

canonicalHandDelegation : GoalDelegationChain
canonicalHandDelegation = goalDelegationChain
  viableBody
  leftHand
  digitField
  differentiate
  expressChannel
  leftHandSupportsBody
  digitRefinesLeftHand
  differentiateRefinesDigit
  channelRefinesDifferentiate

-- The presence of multiple witnesses above is the anti-micromanagement theorem:
-- a higher target specifies a feasible relation, not a unique action sequence.
