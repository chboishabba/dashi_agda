module DASHI.Physics.Closure.ChemistryRightLimitsNondegenerateQuotientCouplingRequirement where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem as ACRT
open import DASHI.Physics.Closure.AtomicChemistryRightLimitsAdapter as ACRLA
open import DASHI.Physics.Closure.ChemistryRightLimitsPromotedObservableCouplingLaw as PairLaw
open import DASHI.Physics.Closure.ChemistryRightLimitsQuotientObservableCouplingLaw as TripleLaw
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- The actual chemistry blockage breaker.
--
-- Existing state:
--   * defect observable is visible on the adapted chemistry carrier;
--   * promoted observable is visible as the photonuclear companion;
--   * quotient-visible strong-count observable is visible;
--   * the triple is only stably compatible.
--
-- That is not enough to collapse the atomic blocker.  The missing ingredient
-- is a non-degenerate relation showing that the quotient observable changes
-- something chemistry-facing that is not already forced by the defect/promoted
-- pair.
--
-- No blockerBroken stamp is provided here.  This module states the exact
-- witness an owner must provide.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record ChemistryRightLimitsNondegenerateQuotientCouplingRequirement : Setω where
  field
    tripleLaw :
      TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw

    Support : Set
    Support≡ :
      Support
      ≡
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (PairLaw.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
              tripleLaw)))

    toFeature : Support → CDQ.ChemistryFeature
    defect : Support → Nat
    promoted : Support → Nat
    quotient : Support → Nat

    defectVisible :
      (s : Support) →
      defect s
      ≡
      PairLaw.ChemistryRightLimitsPromotedObservableCouplingLaw.adaptedDefectObservable
        (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
          tripleLaw)
        s

    promotedVisible :
      (s : Support) →
      promoted s
      ≡
      PairLaw.ChemistryRightLimitsPromotedObservableCouplingLaw.adaptedPromotedObservable
        (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
          tripleLaw)
        s

    quotientVisible :
      (s : Support) →
      quotient s
      ≡
      TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.adaptedQuotientObservable
        tripleLaw
        s

    -- A chemistry-facing relation beyond mere stable triple compatibility.
    -- This is intentionally abstract: the owner must choose the first relation
    -- that is native to the atom/chemistry lane rather than a bookkeeping label.
    strongerChemistryRelation : Support → Support → Set

    -- The relation is quotient-sensitive while holding the old pair fixed.
    left right : Support

    sameDefect : defect left ≡ defect right
    samePromoted : promoted left ≡ promoted right
    quotientSeparates : quotient left ≢ quotient right

    relationWitness : strongerChemistryRelation left right

    preSpectralBoundary : Set
    preScaleSettingBoundary : Set

    nonClaimBoundary : List String

record ChemistryRightLimitsNondegenerateQuotientCouplingTheorem : Setω where
  field
    requirement : ChemistryRightLimitsNondegenerateQuotientCouplingRequirement

    pairHeldFixed :
      ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.defect requirement
        (ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.left requirement)
      ≡
      ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.defect requirement
        (ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.right requirement)
      ×
      ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.promoted requirement
        (ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.left requirement)
      ≡
      ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.promoted requirement
        (ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.right requirement)

    quotientIsNotBookkeeping :
      ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.quotient requirement
        (ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.left requirement)
      ≢
      ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.quotient requirement
        (ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.right requirement)

    strongerRelationLanded :
      ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.strongerChemistryRelation
        requirement
        (ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.left requirement)
        (ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.right requirement)

chemistryRequirementToTheorem :
  (req : ChemistryRightLimitsNondegenerateQuotientCouplingRequirement) →
  ChemistryRightLimitsNondegenerateQuotientCouplingTheorem
chemistryRequirementToTheorem req =
  record
    { requirement = req
    ; pairHeldFixed =
        ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.sameDefect req
        ,
        ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.samePromoted req
    ; quotientIsNotBookkeeping =
        ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.quotientSeparates req
    ; strongerRelationLanded =
        ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.relationWitness req
    }
