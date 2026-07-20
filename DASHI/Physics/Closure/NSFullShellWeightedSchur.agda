module DASHI.Physics.Closure.NSFullShellWeightedSchur where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Analysis.FiniteWeightedKernelSums
open import DASHI.Physics.Closure.NSPairIncidenceKernel
import DASHI.Physics.Closure.NSIntegerFourierLattice as Lattice

------------------------------------------------------------------------
-- Full-shell Wall-1 carrier.
--
-- The critical design invariant is that kernel entries and Schur sums are
-- definitions obtained by finite folds over enumerated incidences.  A theorem
-- cannot substitute unrelated row/column scalars: it must bound these exact
-- expressions.
------------------------------------------------------------------------

infix 4 _∈_

data _∈_ {a : Level} {A : Set a} (x : A) : List A → Set a where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

record FullShellGeometry : Set₁ where
  field
    Scale Cutoff ShellIndex : Set
    _≤cutoff_ : Cutoff → Cutoff → Set

    targetShellModes : Scale → Cutoff → List Lattice.FourierMode
    nearShellModes : Scale → Cutoff → List Lattice.FourierMode

    InCutoffCube : Cutoff → Lattice.FourierMode → Set
    InTargetShell : Scale → Cutoff → Lattice.FourierMode → Set
    InNearShell : Scale → Cutoff → Lattice.FourierMode → Set
    shellIndex : Lattice.FourierMode → ShellIndex

    targetEnumerationSound :
      ∀ K N k → k ∈ targetShellModes K N → InTargetShell K N k
    targetEnumerationComplete :
      ∀ K N k → InTargetShell K N k → k ∈ targetShellModes K N

    nearEnumerationSound :
      ∀ K N k → k ∈ nearShellModes K N → InNearShell K N k
    nearEnumerationComplete :
      ∀ K N k → InNearShell K N k → k ∈ nearShellModes K N

    targetCutoffSound :
      ∀ K N k → InTargetShell K N k → InCutoffCube N k
    nearCutoffSound :
      ∀ K N k → InNearShell K N k → InCutoffCube N k

open FullShellGeometry public

record FullShellTriadIncidence
    (G : FullShellGeometry)
    (K : Scale G)
    (N : Cutoff G)
    (target source : Lattice.FourierMode) : Set where
  field
    background perturbation : Lattice.FourierMode
    resonance : Lattice.addMode background perturbation ≡ target
    sourceIdentified : perturbation ≡ source

    targetMembership : InTargetShell G K N target
    sourceMembership : InNearShell G K N source
    backgroundCutoff : InCutoffCube G N background
    sourceNonZero : Lattice.NonZeroMode source

    symmetryRepresentative : Set
    representativeChosen : symmetryRepresentative

open FullShellTriadIncidence public

record FullShellIncidenceEnumeration
    (G : FullShellGeometry) : Set₁ where
  field
    incidences :
      (K : Scale G) → (N : Cutoff G) →
      (target source : Lattice.FourierMode) →
      List (FullShellTriadIncidence G K N target source)

    incidenceSound :
      ∀ K N target source incidence →
      incidence ∈ incidences K N target source →
      FullShellTriadIncidence G K N target source

    CompleteIncidence :
      (K : Scale G) → (N : Cutoff G) →
      (target source : Lattice.FourierMode) → Set

    incidenceComplete :
      ∀ K N target source →
      CompleteIncidence K N target source →
      List (FullShellTriadIncidence G K N target source)

    completenessMatchesEnumeration :
      ∀ K N target source complete →
      incidenceComplete K N target source complete ≡
      incidences K N target source

    NoDuplicateModuloSymmetry :
      (K : Scale G) → (N : Cutoff G) →
      (target source : Lattice.FourierMode) → Set

    noDuplicateModuloSymmetry :
      ∀ K N target source →
      NoDuplicateModuloSymmetry K N target source

open FullShellIncidenceEnumeration public

record FullShellKernelData
    {s : Level}
    (Scalar : Set s)
    (G : FullShellGeometry)
    (E : FullShellIncidenceEnumeration G) : Set (lsuc s) where
  field
    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    shellWeight : Scale G → Lattice.FourierMode → Scalar

    localFourierMajorant :
      ∀ K N target source →
      FullShellTriadIncidence G K N target source → Scalar

open FullShellKernelData public

fullShellKernelEntry :
  ∀ {s} {Scalar : Set s}
    {G : FullShellGeometry}
    {E : FullShellIncidenceEnumeration G} →
  FullShellKernelData Scalar G E →
  (K : Scale G) → (N : Cutoff G) →
  Lattice.FourierMode → Lattice.FourierMode → Scalar
fullShellKernelEntry D K N target source =
  fold (add D) (zero D)
    (map
      (localFourierMajorant D K N target source)
      (incidences _ K N target source))

fullShellRowSum :
  ∀ {s} {Scalar : Set s}
    {G : FullShellGeometry}
    {E : FullShellIncidenceEnumeration G} →
  FullShellKernelData Scalar G E →
  (K : Scale G) → (N : Cutoff G) →
  Lattice.FourierMode → Scalar
fullShellRowSum {G = G} D K N target =
  fold (add D) (zero D)
    (map
      (λ source →
        multiply D
          (fullShellKernelEntry D K N target source)
          (shellWeight D K source))
      (nearShellModes G K N))

fullShellColumnSum :
  ∀ {s} {Scalar : Set s}
    {G : FullShellGeometry}
    {E : FullShellIncidenceEnumeration G} →
  FullShellKernelData Scalar G E →
  (K : Scale G) → (N : Cutoff G) →
  Lattice.FourierMode → Scalar
fullShellColumnSum {G = G} D K N source =
  fold (add D) (zero D)
    (map
      (λ target →
        multiply D
          (shellWeight D K target)
          (fullShellKernelEntry D K N target source))
      (targetShellModes G K N))

record FullShellConcreteBiotSavartMatch
    {s : Level}
    {Scalar : Set s}
    {G : FullShellGeometry}
    {E : FullShellIncidenceEnumeration G}
    (D : FullShellKernelData Scalar G E)
    (concreteKernel :
      Scale G → Cutoff G →
      Lattice.FourierMode → Lattice.FourierMode → Scalar) : Set s where
  field
    pointwiseFullShellMatch :
      ∀ K N target source →
      concreteKernel K N target source ≡
      fullShellKernelEntry D K N target source

open FullShellConcreteBiotSavartMatch public

record FullShellQuantitativeEvidence
    {s : Level}
    {Scalar : Set s}
    {G : FullShellGeometry}
    {E : FullShellIncidenceEnumeration G}
    (D : FullShellKernelData Scalar G E) : Set (lsuc s) where
  field
    shellIntersectionCounting : Set
    weightedRadialSummability : Set
    angularPolarizationMajorant : Set
    zeroModeExcluded : Set

    cutoffIncidenceEmbedding :
      ∀ K N N′ → _≤cutoff_ G N N′ →
      (target source : Lattice.FourierMode) → Set

    cutoffContributionPreserved :
      ∀ K N N′ le target source →
      cutoffIncidenceEmbedding K N N′ le target source

open FullShellQuantitativeEvidence public

record FullShellWeightedSchurCertificate
    {s : Level}
    {Scalar : Set s}
    {G : FullShellGeometry}
    {E : FullShellIncidenceEnumeration G}
    (D : FullShellKernelData Scalar G E) : Set (lsuc s) where
  field
    quantitativeEvidence : FullShellQuantitativeEvidence D

    rowConstant columnConstant : Scalar

    fullShellRowBound :
      ∀ K N target → InTargetShell G K N target →
      _≤_ D
        (fullShellRowSum D K N target)
        (multiply D rowConstant (shellWeight D K target))

    fullShellColumnBound :
      ∀ K N source → InNearShell G K N source →
      _≤_ D
        (fullShellColumnSum D K N source)
        (multiply D columnConstant (shellWeight D K source))

open FullShellWeightedSchurCertificate public

------------------------------------------------------------------------
-- Promotion is deliberately one-way: the completed certificate exposes the
-- exact incidence-derived row and column estimates.  No final certificate is
-- provided here; it must be inhabited by the genuine counting and analytic
-- estimates above.
------------------------------------------------------------------------

record FullShellSchurEndpoint
    {s : Level}
    {Scalar : Set s}
    (G : FullShellGeometry)
    (E : FullShellIncidenceEnumeration G)
    (D : FullShellKernelData Scalar G E) : Set (lsuc s) where
  field
    certificate : FullShellWeightedSchurCertificate D
    fullIntegerShellClosed : Set

open FullShellSchurEndpoint public
