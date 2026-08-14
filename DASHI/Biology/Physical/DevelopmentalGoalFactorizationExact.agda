module DASHI.Biology.Physical.DevelopmentalGoalFactorizationExact where

------------------------------------------------------------------------
-- Source-facing interpretation:
-- Michael Levin, "Bioelectric signaling: Reprogrammable circuits underlying
-- embryogenesis, regeneration, and cancer", Cell 184 (2021), 1971-1989.
-- DOI: 10.1016/j.cell.2021.02.034.
--
-- DASHI CONTRIBUTION
--
-- Separate the reusable organ concept from relational variables needed for a
-- concrete developmental target.  "hand", "hand here", and "our hand" are
-- therefore different projections of one parameterised goal carrier rather
-- than synonyms for a stored microscopic bitmap.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

false≢true : false ≢ true
false≢true ()

true≢false : true ≢ false
true≢false ()

data OrganKind : Set where
  hand foot : OrganKind

data Side : Set where
  leftSide rightSide : Side

record DevelopmentalGoal : Set where
  constructor developmentalGoal
  field
    organ : OrganKind
    anchor : Bool
    owner : Bool
    side : Side
    scaleClass : Nat

open DevelopmentalGoal public

-- Coarse concept: what organ type is requested?
genericOrgan : DevelopmentalGoal → OrganKind
genericOrgan = organ

-- Relational refinement: type plus location.
record OrganHere : Set where
  constructor organHere
  field
    hereOrgan : OrganKind
    hereAnchor : Bool

open OrganHere public

organHereOf : DevelopmentalGoal → OrganHere
organHereOf g = organHere (organ g) (anchor g)

-- Organism-relative refinement: type plus location plus owner identity.
record OwnedOrganHere : Set where
  constructor ownedOrganHere
  field
    ownedOrgan : OrganKind
    ownedAnchor : Bool
    ownedBy : Bool

open OwnedOrganHere public

ownedOrganHereOf : DevelopmentalGoal → OwnedOrganHere
ownedOrganHereOf g = ownedOrganHere (organ g) (anchor g) (owner g)

leftHandHereOurs : DevelopmentalGoal
leftHandHereOurs = developmentalGoal hand false false leftSide 1

leftHandElsewhereOurs : DevelopmentalGoal
leftHandElsewhereOurs = developmentalGoal hand true false leftSide 1

leftHandHereTheirs : DevelopmentalGoal
leftHandHereTheirs = developmentalGoal hand false true leftSide 1

sameGenericHandDifferentLocation :
  genericOrgan leftHandHereOurs ≡ genericOrgan leftHandElsewhereOurs
sameGenericHandDifferentLocation = refl

sameHandHereDifferentOwner :
  organHereOf leftHandHereOurs ≡ organHereOf leftHandHereTheirs
sameHandHereDifferentOwner = refl

locationIsNotDeterminedByGenericHand :
  leftHandHereOurs ≢ leftHandElsewhereOurs
locationIsNotDeterminedByGenericHand eq =
  false≢true (cong anchor eq)

ownerIsNotDeterminedByHandHere :
  leftHandHereOurs ≢ leftHandHereTheirs
ownerIsNotDeterminedByHandHere eq =
  false≢true (cong owner eq)

------------------------------------------------------------------------
-- A small exact developmental factorisation regression.
--
-- Genome does not map directly to phenotype.  It parameterises a sequence of
-- context-dependent updates.  The finite Bool model proves the structural
-- distinction without pretending Bool is a biological state.
------------------------------------------------------------------------

Genome Epigenetic Regulatory Electrical Mechanical Morphology : Set
Genome = Bool
Epigenetic = Bool
Regulatory = Bool
Electrical = Bool
Mechanical = Bool
Morphology = Bool

xor : Bool → Bool → Bool
xor false false = false
xor false true = true
xor true false = true
xor true true = false

regulate : Genome → Epigenetic → Regulatory
regulate = xor

bioelectricUpdate : Regulatory → Electrical → Electrical
bioelectricUpdate = xor

mechanicalUpdate : Electrical → Mechanical → Mechanical
mechanicalUpdate = xor

realiseMorphology : Mechanical → Morphology
realiseMorphology x = x

developmentalStep :
  Genome → Epigenetic → Electrical → Mechanical → Morphology
developmentalStep genome epigenetic electrical mechanical =
  realiseMorphology
    (mechanicalUpdate
      (bioelectricUpdate (regulate genome epigenetic) electrical)
      mechanical)

developmentalStepFactorises :
  (g : Genome) (e : Epigenetic) (b : Electrical) (m : Mechanical) →
  developmentalStep g e b m ≡
  realiseMorphology (mechanicalUpdate (bioelectricUpdate (regulate g e) b) m)
developmentalStepFactorises g e b m = refl

sameGenomeDifferentContextCanChangeOutcome :
  developmentalStep false false false false
  ≢ developmentalStep false true false false
sameGenomeDifferentContextCanChangeOutcome = false≢true

------------------------------------------------------------------------
-- Goal realization preserves all declared variables: the organ concept alone
-- is intentionally insufficient to recover the concrete target.
------------------------------------------------------------------------

record GoalMorphology : Set where
  constructor goalMorphology
  field
    realisedOrgan : OrganKind
    realisedAnchor : Bool
    realisedOwner : Bool
    realisedSide : Side
    realisedScale : Nat

open GoalMorphology public

realiseGoal : DevelopmentalGoal → GoalMorphology
realiseGoal g =
  goalMorphology (organ g) (anchor g) (owner g) (side g) (scaleClass g)

realiseGoalPreservesAnchor :
  (g : DevelopmentalGoal) → realisedAnchor (realiseGoal g) ≡ anchor g
realiseGoalPreservesAnchor g = refl

realiseGoalPreservesOwner :
  (g : DevelopmentalGoal) → realisedOwner (realiseGoal g) ≡ owner g
realiseGoalPreservesOwner g = refl
