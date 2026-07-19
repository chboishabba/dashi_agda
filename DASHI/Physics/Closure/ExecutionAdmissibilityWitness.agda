module DASHI.Physics.Closure.ExecutionAdmissibilityWitness where

open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Step- and family-level execution classes.

-- StepClass is deliberately local: a family may contain ordinary interior
-- steps and a small number of boundary steps without the whole family being
-- classified as a structural escape.
data StepClass : Set where
  Interior : StepClass
  ArrowBoundary : StepClass
  StructuralBoundary : StepClass
  Outside : StepClass

-- FamilyClass records the observed execution regime at family scale.  In
-- particular, MDLTailBoundaryFamily is not a synonym for structural failure:
-- it names the narrower regime where geometric admissibility survives while
-- exact MDL descent fails on a localized terminal tail.
data FamilyClass : Set where
  InteriorFamily : FamilyClass
  ArrowLadderFamily : FamilyClass
  SingleArrowBreakFamily : FamilyClass
  MDLTailBoundaryFamily : FamilyClass

------------------------------------------------------------------------
-- Existing execution witness surface.

record ExecutionAdmissibilityWitness (StepId : Set) : Setω where
  field
    stepClass : StepId → StepClass
    coneOK : StepId → Set
    arrowOK : StepId → Set
    mdlOK : StepId → Set
    basinOK : StepId → Set
    eigenOK : StepId → Set
    interiorOrBoundary :
      ∀ step →
      stepClass step ≡ Interior ⊎ stepClass step ≡ ArrowBoundary
    noStructuralEscape :
      ∀ step →
      stepClass step ≡ StructuralBoundary ⊎ stepClass step ≡ Outside →
      ⊥

open ExecutionAdmissibilityWitness public

record FamilyClassificationWitness (FamilyId : Set) : Setω where
  field
    familyClass : FamilyId → FamilyClass
    coneOK : FamilyId → Set
    fejerOK : FamilyId → Set
    closestOK : FamilyId → Set
    mdlExactOK : FamilyId → Set
    tailLocalized : FamilyId → Set

open FamilyClassificationWitness public

------------------------------------------------------------------------
-- Theorem-grade MDL tail-boundary seam.
--
-- The predicates are parameters rather than built-in numerical claims.  A
-- generated or hand-written current-trace witness must supply each premise.
-- This keeps the formal layer honest: classification does not manufacture the
-- cone, Fejer, closest-point, MDL, localization, or terminality evidence.

record MDLTailBoundaryWitness
       (FamilyId : Set)
       (ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary :
         FamilyId → Set)
       : Setω where
  field
    family : FamilyId
    coneOK : ConeOK family
    fejerOK : FejerOK family
    closestOK : ClosestOK family
    mdlExactFails : MDLExactOK family → ⊥
    tailLocalized : TailLocalized family
    terminalBoundary : TerminalBoundary family

open MDLTailBoundaryWitness public

-- The family classification exported by a complete tail-boundary witness is
-- canonical and does not depend on a heuristic source-side prime projection.
mdlTailBoundary-familyClass :
  ∀ {FamilyId}
    {ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary :
      FamilyId → Set} →
  MDLTailBoundaryWitness
    FamilyId ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary →
  FamilyClass
mdlTailBoundary-familyClass _ = MDLTailBoundaryFamily

-- The positive geometric core can be projected without carrying the negative
-- exact-MDL premise.  This is the formal version of "geometry survives while
-- exact MDL descent fails".
record GeometricAdmissibility
       {FamilyId : Set}
       (ConeOK FejerOK ClosestOK : FamilyId → Set)
       (family : FamilyId)
       : Set where
  field
    coneOK : ConeOK family
    fejerOK : FejerOK family
    closestOK : ClosestOK family

open GeometricAdmissibility public

mdlTailBoundary-geometric :
  ∀ {FamilyId}
    {ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary :
      FamilyId → Set}
    (w : MDLTailBoundaryWitness
      FamilyId ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary) →
  GeometricAdmissibility ConeOK FejerOK ClosestOK
    (MDLTailBoundaryWitness.family w)
mdlTailBoundary-geometric w = record
  { coneOK = MDLTailBoundaryWitness.coneOK w
  ; fejerOK = MDLTailBoundaryWitness.fejerOK w
  ; closestOK = MDLTailBoundaryWitness.closestOK w
  }

-- Exact MDL failure remains available as an explicit negative witness; it is
-- not conflated with cone failure or source-support failure.
mdlTailBoundary-not-exact-MDL :
  ∀ {FamilyId}
    {ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary :
      FamilyId → Set}
    (w : MDLTailBoundaryWitness
      FamilyId ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary) →
  MDLExactOK (MDLTailBoundaryWitness.family w) → ⊥
mdlTailBoundary-not-exact-MDL w = MDLTailBoundaryWitness.mdlExactFails w

------------------------------------------------------------------------
-- Repeatability is intentionally scoped.
--
-- Two observations of the same family establish repeated-one-family evidence,
-- not a cross-family physical law.  A future cross-family promotion therefore
-- needs a separate witness rather than being inferred from repetition alone.

data EvidenceScope : Set where
  SingleObservation : EvidenceScope
  RepeatedOneFamily : EvidenceScope
  CrossFamily : EvidenceScope

record RepeatedMDLTailBoundaryWitness
       (FamilyId : Set)
       (ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary :
         FamilyId → Set)
       : Setω where
  field
    first : MDLTailBoundaryWitness
      FamilyId ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary
    second : MDLTailBoundaryWitness
      FamilyId ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary
    sameFamily :
      MDLTailBoundaryWitness.family first ≡
      MDLTailBoundaryWitness.family second

open RepeatedMDLTailBoundaryWitness public

repeatedMDLTailBoundary-scope :
  ∀ {FamilyId}
    {ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary :
      FamilyId → Set} →
  RepeatedMDLTailBoundaryWitness
    FamilyId ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary →
  EvidenceScope
repeatedMDLTailBoundary-scope _ = RepeatedOneFamily

-- Cross-family promotion is a separate interface.  It cannot be obtained from
-- RepeatedMDLTailBoundaryWitness alone, which prevents the current repeated
-- ttbar observation from silently becoming a universal tail law.
record CrossFamilyMDLTailBoundaryWitness (FamilyId : Set) : Setω where
  field
    firstFamily : FamilyId
    secondFamily : FamilyId
    distinctFamilies : firstFamily ≡ secondFamily → ⊥

open CrossFamilyMDLTailBoundaryWitness public

crossFamilyMDLTailBoundary-scope :
  ∀ {FamilyId} →
  CrossFamilyMDLTailBoundaryWitness FamilyId →
  EvidenceScope
crossFamilyMDLTailBoundary-scope _ = CrossFamily

------------------------------------------------------------------------
-- Existential wrappers used by generated trace artifacts.

record SomeExecutionAdmissibilityWitness : Setω where
  field
    StepId : Set
    witness : ExecutionAdmissibilityWitness StepId

open SomeExecutionAdmissibilityWitness public

record SomeFamilyClassificationWitness : Setω where
  field
    FamilyId : Set
    witness : FamilyClassificationWitness FamilyId

open SomeFamilyClassificationWitness public
