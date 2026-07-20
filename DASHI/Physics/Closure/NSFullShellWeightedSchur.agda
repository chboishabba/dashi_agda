module DASHI.Physics.Closure.NSFullShellWeightedSchur where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Analysis.FiniteWeightedKernelSums
import DASHI.Physics.Closure.NSIntegerFourierLattice as Lattice

------------------------------------------------------------------------
-- Full-shell Wall-1 carrier.
--
-- Kernel entries and Schur sums are definitions obtained by finite folds over
-- enumerated incidences.  A theorem therefore cannot substitute unrelated
-- row/column scalars: it must bound these exact expressions.
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

    SymmetryRepresentative : Set
    representativeChosen : SymmetryRepresentative

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

    enumerateCompleteIncidences :
      ∀ K N target source →
      CompleteIncidence K N target source →
      List (FullShellTriadIncidence G K N target source)

    completenessMatchesEnumeration :
      ∀ K N target source complete →
      enumerateCompleteIncidences K N target source complete ≡
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
fullShellKernelEntry {E = E} D K N target source =
  fold (add D) (zero D)
    (map
      (localFourierMajorant D K N target source)
      (incidences E K N target source))

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

------------------------------------------------------------------------
-- Quantitative wall.  Every field is tied either to an actual incidence,
-- contribution, or exact full-shell fold.  These are the genuine obligations:
-- angular control, zero-mode exclusion, cutoff monotonicity, lattice counting
-- plus radial summability, and cutoff-independent constants.
------------------------------------------------------------------------

record FullShellQuantitativeEvidence
    {s : Level}
    {Scalar : Set s}
    {G : FullShellGeometry}
    {E : FullShellIncidenceEnumeration G}
    (D : FullShellKernelData Scalar G E) : Set (lsuc s) where
  field
    angularConstant : Scalar
    angularPolarizationMajorant :
      ∀ K N target source incidence →
      _≤_ D
        (localFourierMajorant D K N target source incidence)
        angularConstant

    zeroModeExcluded :
      ∀ K N target source incidence →
      source incidence ≡ Lattice.zeroMode → ⊥

    cutoffIncidenceEmbedding :
      ∀ K N N′ → _≤cutoff_ G N N′ →
      (target source : Lattice.FourierMode) →
      FullShellTriadIncidence G K N target source →
      FullShellTriadIncidence G K N′ target source

    cutoffContributionPreserved :
      ∀ K N N′ le target source incidence →
      localFourierMajorant D K N target source incidence ≡
      localFourierMajorant D K N′ target source
        (cutoffIncidenceEmbedding K N N′ le target source incidence)

    shellCountingRadialRowConstant : Scalar
    shellCountingRadialColumnConstant : Scalar

    shellCountingAndRadialRowBound :
      ∀ K N target → InTargetShell G K N target →
      _≤_ D
        (fullShellRowSum D K N target)
        (multiply D shellCountingRadialRowConstant
          (shellWeight D K target))

    shellCountingAndRadialColumnBound :
      ∀ K N sourceMode → InNearShell G K N sourceMode →
      _≤_ D
        (fullShellColumnSum D K N sourceMode)
        (multiply D shellCountingRadialColumnConstant
          (shellWeight D K sourceMode))

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
    rowConstantIdentified :
      rowConstant ≡ shellCountingRadialRowConstant quantitativeEvidence
    columnConstantIdentified :
      columnConstant ≡ shellCountingRadialColumnConstant quantitativeEvidence

    fullShellRowBound :
      ∀ K N target → InTargetShell G K N target →
      _≤_ D
        (fullShellRowSum D K N target)
        (multiply D rowConstant (shellWeight D K target))

    fullShellColumnBound :
      ∀ K N sourceMode → InNearShell G K N sourceMode →
      _≤_ D
        (fullShellColumnSum D K N sourceMode)
        (multiply D columnConstant (shellWeight D K sourceMode))

open FullShellWeightedSchurCertificate public

record FullShellSchurEndpoint
    {s : Level}
    {Scalar : Set s}
    (G : FullShellGeometry)
    (E : FullShellIncidenceEnumeration G)
    (D : FullShellKernelData Scalar G E) : Set (lsuc s) where
  field
    certificate : FullShellWeightedSchurCertificate D

open FullShellSchurEndpoint public
