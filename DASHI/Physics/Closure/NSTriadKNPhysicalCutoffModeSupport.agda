module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffModeSupport where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; length; lookup; deduplicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-deduplicate⁺)
open import Data.List.Relation.Unary.Any using (here; there; index)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Unique.DecPropositional.Properties as UniqueDec
open import Data.Product using (_×_; Σ; _,_)
open import Data.Integer.Properties as ℤP using (_≟_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes; no)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactRetainedPairIncidences as Incidence
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Sector

------------------------------------------------------------------------
-- Finite raw mode support of the physical cutoff incidence carrier.
--
-- This is intentionally an occurrence list, not yet the coordinate carrier
-- of the Gram space: a mode may participate in several incidences and hence
-- occurs more than once.  The two endpoint lemmas below are constructive
-- facts about the exact cutoff list.  It is normalized below with exact
-- lattice equality, because identifying equal modes is essential for a
-- shared basis coordinate e_source - e_target.
------------------------------------------------------------------------

endpointSupport : List Incidence.PairIncidence → List Lattice.LatticeMode3
endpointSupport [] = []
endpointSupport (r ∷ rs) =
  Incidence.sourceMode r ∷ Incidence.targetMode r ∷ endpointSupport rs

-- Exact coordinate equality is decidable because a lattice mode is a triple
-- of integers.  This is the equality used for support normalization, rather
-- than equality of triad occurrences.
latticeModeDecEq : DecidableEquality Lattice.LatticeMode3
latticeModeDecEq
  (Lattice.mkLatticeMode3 a₁ a₂ a₃)
  (Lattice.mkLatticeMode3 b₁ b₂ b₃)
  with ℤP._≟_ a₁ b₁ | ℤP._≟_ a₂ b₂ | ℤP._≟_ a₃ b₃
... | yes refl | yes refl | yes refl = yes refl
... | no a₁≢b₁ | _ | _ = no λ { refl → a₁≢b₁ refl }
... | yes _ | no a₂≢b₂ | _ = no λ { refl → a₂≢b₂ refl }
... | yes _ | yes _ | no a₃≢b₃ = no λ { refl → a₃≢b₃ refl }

normalizedEndpointSupport :
  List Incidence.PairIncidence → List Lattice.LatticeMode3
normalizedEndpointSupport rs = deduplicate latticeModeDecEq (endpointSupport rs)

sourceAppearsInEndpointSupport :
  (r : Incidence.PairIncidence) → (rs : List Incidence.PairIncidence) →
  Incidence.sourceMode r ∈ endpointSupport (r ∷ rs)
sourceAppearsInEndpointSupport r rs = here refl

targetAppearsInEndpointSupport :
  (r : Incidence.PairIncidence) → (rs : List Incidence.PairIncidence) →
  Incidence.targetMode r ∈ endpointSupport (r ∷ rs)
targetAppearsInEndpointSupport r rs = there (here refl)

sourceAppearsForIncidenceMember :
  (r : Incidence.PairIncidence) → (rs : List Incidence.PairIncidence) →
  r ∈ rs → Incidence.sourceMode r ∈ endpointSupport rs
sourceAppearsForIncidenceMember r (s ∷ rs) (here refl) = here refl
sourceAppearsForIncidenceMember r (s ∷ rs) (there r∈rs) =
  there (there (sourceAppearsForIncidenceMember r rs r∈rs))

targetAppearsForIncidenceMember :
  (r : Incidence.PairIncidence) → (rs : List Incidence.PairIncidence) →
  r ∈ rs → Incidence.targetMode r ∈ endpointSupport rs
targetAppearsForIncidenceMember r (s ∷ rs) (here refl) = there (here refl)
targetAppearsForIncidenceMember r (s ∷ rs) (there r∈rs) =
  there (there (targetAppearsForIncidenceMember r rs r∈rs))

sourceAppearsInNormalizedEndpointSupport :
  (r : Incidence.PairIncidence) → (rs : List Incidence.PairIncidence) →
  r ∈ rs → Incidence.sourceMode r ∈ normalizedEndpointSupport rs
sourceAppearsInNormalizedEndpointSupport r rs r∈rs =
  ∈-deduplicate⁺ latticeModeDecEq
    (sourceAppearsForIncidenceMember r rs r∈rs)

targetAppearsInNormalizedEndpointSupport :
  (r : Incidence.PairIncidence) → (rs : List Incidence.PairIncidence) →
  r ∈ rs → Incidence.targetMode r ∈ normalizedEndpointSupport rs
targetAppearsInNormalizedEndpointSupport r rs r∈rs =
  ∈-deduplicate⁺ latticeModeDecEq
    (targetAppearsForIncidenceMember r rs r∈rs)

normalizedEndpointSupportUnique :
  (rs : List Incidence.PairIncidence) → Unique (normalizedEndpointSupport rs)
normalizedEndpointSupportUnique rs = UniqueDec.deduplicate-! latticeModeDecEq _

physicalCutoffEndpointSupport :
  (N R : Nat) →
  Sector.ExactOutputRetainedSectorLaw N R →
  List Lattice.LatticeMode3
physicalCutoffEndpointSupport N R sector =
  endpointSupport (Incidence.physicalCutoffRetainedPairIncidences N R sector)

physicalCutoffNormalizedModeSupport :
  (N R : Nat) →
  Sector.ExactOutputRetainedSectorLaw N R →
  List Lattice.LatticeMode3
physicalCutoffNormalizedModeSupport N R sector =
  normalizedEndpointSupport
    (Incidence.physicalCutoffRetainedPairIncidences N R sector)

physicalCutoffNormalizedModeSupportUnique :
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  Unique (physicalCutoffNormalizedModeSupport N R sector)
physicalCutoffNormalizedModeSupportUnique N R sector =
  normalizedEndpointSupportUnique
    (Incidence.physicalCutoffRetainedPairIncidences N R sector)

------------------------------------------------------------------------
-- Canonical finite coordinates for the exact normalized support.
--
-- An incidence is indexed by its actual membership in the retained cutoff
-- list.  Therefore its source and target coordinates are total and share a
-- coordinate precisely through equality of their lattice modes, not through
-- an occurrence/triad label.
------------------------------------------------------------------------

PhysicalCutoffIncidence :
  (N R : Nat) → Sector.ExactOutputRetainedSectorLaw N R → Set
PhysicalCutoffIncidence N R sector =
  Σ Incidence.PairIncidence
    (λ r → r ∈ Incidence.physicalCutoffRetainedPairIncidences N R sector)

liftIndexedMembership :
  {A : Set} → {x : A} → {xs : List A} →
  List (Σ A (λ y → y ∈ xs)) →
  List (Σ A (λ y → y ∈ x ∷ xs))
liftIndexedMembership [] = []
liftIndexedMembership ((y , y∈xs) ∷ ys) =
  (y , there y∈xs) ∷ liftIndexedMembership ys

indexListByMembership :
  {A : Set} → (xs : List A) → List (Σ A (λ x → x ∈ xs))
indexListByMembership [] = []
indexListByMembership (x ∷ xs) =
  (x , here refl) ∷ liftIndexedMembership (indexListByMembership xs)

physicalCutoffIndexedIncidences :
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  List (PhysicalCutoffIncidence N R sector)
physicalCutoffIndexedIncidences N R sector =
  indexListByMembership
    (Incidence.physicalCutoffRetainedPairIncidences N R sector)

physicalCutoffModeCoordinate :
  (N R : Nat) → Sector.ExactOutputRetainedSectorLaw N R → Set
physicalCutoffModeCoordinate N R sector =
  Fin (length (physicalCutoffNormalizedModeSupport N R sector))

coordinateMode :
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  physicalCutoffModeCoordinate N R sector → Lattice.LatticeMode3
coordinateMode N R sector i =
  lookup (physicalCutoffNormalizedModeSupport N R sector) i

sourceCoordinate :
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  PhysicalCutoffIncidence N R sector →
  physicalCutoffModeCoordinate N R sector
sourceCoordinate N R sector (r , r∈) =
  index
    (sourceAppearsInNormalizedEndpointSupport r
      (Incidence.physicalCutoffRetainedPairIncidences N R sector) r∈)

targetCoordinate :
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  PhysicalCutoffIncidence N R sector →
  physicalCutoffModeCoordinate N R sector
targetCoordinate N R sector (r , r∈) =
  index
    (targetAppearsInNormalizedEndpointSupport r
      (Incidence.physicalCutoffRetainedPairIncidences N R sector) r∈)

sourceCoordinateCorrect :
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  (r : PhysicalCutoffIncidence N R sector) →
  Incidence.sourceMode (Data.Product.proj₁ r) ≡
  coordinateMode N R sector (sourceCoordinate N R sector r)
sourceCoordinateCorrect N R sector (r , r∈) =
  lookup-index
    (sourceAppearsInNormalizedEndpointSupport r
      (Incidence.physicalCutoffRetainedPairIncidences N R sector) r∈)

targetCoordinateCorrect :
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  (r : PhysicalCutoffIncidence N R sector) →
  Incidence.targetMode (Data.Product.proj₁ r) ≡
  coordinateMode N R sector (targetCoordinate N R sector r)
targetCoordinateCorrect N R sector (r , r∈) =
  lookup-index
    (targetAppearsInNormalizedEndpointSupport r
      (Incidence.physicalCutoffRetainedPairIncidences N R sector) r∈)

------------------------------------------------------------------------
-- The normalized support is now concrete and duplicate-free.  What remains
-- before it becomes the actual scalar vector space is algebraic: the chosen
-- ordered scalar model must supply finite coordinate sums, additive inverses,
-- and the inner-product laws for functions on this list.
