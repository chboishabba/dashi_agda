module DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND 63 / A0 FIXED-CUTOFF CARRIER
--
-- Intersect the literal finite cutoff cube with the canonical half-lattice from
-- `CanonicalRealityOrbitHalfLatticeRound63Exact`.  The resulting list:
--
--   * is finite and duplicate-free;
--   * contains exactly every listed cutoff mode whose leading nonzero
--     coordinate is positive;
--   * excludes zero;
--   * never contains both k and -k;
--   * for every nonzero cutoff mode, contains k or -k according to the unique
--     reality-orbit choice.
--
-- This is the actual fixed list of one-representative-per-k~-k Fourier
-- coordinates needed to repair the Round62 n->2n->4n reconstructed-list growth.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNCanonicalRealityOrbitHalfLatticeRound63Exact as Half

filterLeadingPositive : List Z3.FourierMode → List Z3.FourierMode
filterLeadingPositive [] = []
filterLeadingPositive (k ∷ ks) with Half.leadingPositive k
... | true = k ∷ filterLeadingPositive ks
... | false = filterLeadingPositive ks

canonicalCutoffOrbitModes : Nat → List Z3.FourierMode
canonicalCutoffOrbitModes N = filterLeadingPositive (Cube.cutoffModes N)

filterMemberInSource :
  ∀ {k modes} →
  k Cube.∈ filterLeadingPositive modes →
  k Cube.∈ modes
filterMemberInSource {modes = []} ()
filterMemberInSource {k} {modes = head ∷ tail} member
  with Half.leadingPositive head
... | true with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest = Cube.there (filterMemberInSource rest)
... | false = Cube.there (filterMemberInSource member)

filterMemberIsPositive :
  ∀ {k modes} →
  k Cube.∈ filterLeadingPositive modes →
  Half.leadingPositive k ≡ true
filterMemberIsPositive {modes = []} ()
filterMemberIsPositive {k} {modes = head ∷ tail} member
  with Half.leadingPositive head
... | true with member
...   | Cube.here refl = refl
...   | Cube.there rest = filterMemberIsPositive rest
... | false = filterMemberIsPositive member

positiveSourceMemberInFilter :
  ∀ {k modes} →
  Half.leadingPositive k ≡ true →
  k Cube.∈ modes →
  k Cube.∈ filterLeadingPositive modes
positiveSourceMemberInFilter {modes = []} selected ()
positiveSourceMemberInFilter {k} {modes = head ∷ tail} selected member
  with Half.leadingPositive head
... | true with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest = Cube.there
      (positiveSourceMemberInFilter selected rest)
... | false with member
...   | Cube.here refl with selected
...     | ()
...   | Cube.there rest = positiveSourceMemberInFilter selected rest

filterPreservesNoDuplicates :
  ∀ {modes} →
  Cube.NoDuplicates modes →
  Cube.NoDuplicates (filterLeadingPositive modes)
filterPreservesNoDuplicates Cube.unique[] = Cube.unique[]
filterPreservesNoDuplicates
    {modes = head ∷ tail} (Cube.unique∷ fresh rest)
  with Half.leadingPositive head
... | true =
  Cube.unique∷
    (λ member → fresh (filterMemberInSource member))
    (filterPreservesNoDuplicates rest)
... | false = filterPreservesNoDuplicates rest

canonicalCutoffOrbitNoDuplicates :
  ∀ N → Cube.NoDuplicates (canonicalCutoffOrbitModes N)
canonicalCutoffOrbitNoDuplicates N =
  filterPreservesNoDuplicates (Cube.cutoffModeEnumerationNoDuplicates N)

canonicalCutoffMemberSound :
  ∀ {N k} →
  k Cube.∈ canonicalCutoffOrbitModes N →
  Cube.InCutoffCube N k
canonicalCutoffMemberSound {N} {k} member =
  Cube.cutoffModeEnumerationSound N k (filterMemberInSource member)

canonicalCutoffMemberPositive :
  ∀ {N k} →
  k Cube.∈ canonicalCutoffOrbitModes N →
  Half.leadingPositive k ≡ true
canonicalCutoffMemberPositive = filterMemberIsPositive

canonicalCutoffCompleteForPositive :
  ∀ {N k} →
  Cube.InCutoffCube N k →
  Half.leadingPositive k ≡ true →
  k Cube.∈ canonicalCutoffOrbitModes N
canonicalCutoffCompleteForPositive {N} {k} cutoff selected =
  positiveSourceMemberInFilter selected
    (Cube.cutoffModeEnumerationComplete N k cutoff)

canonicalCutoffExcludesZero :
  ∀ N → Z3.zeroMode Cube.∉ canonicalCutoffOrbitModes N
canonicalCutoffExcludesZero N member
  with canonicalCutoffMemberPositive member
... | ()

canonicalCutoffNeverContainsOppositePair :
  ∀ {N k} →
  Z3.NonZeroMode k →
  k Cube.∈ canonicalCutoffOrbitModes N →
  Z3.negateMode k Cube.∉ canonicalCutoffOrbitModes N
canonicalCutoffNeverContainsOppositePair {N} {k} nonzero kMember negMember =
  let
    kSelected = canonicalCutoffMemberPositive kMember
    negNotSelected =
      Half.selectedModeOppositeNotSelected k nonzero kSelected
    negSelected = canonicalCutoffMemberPositive negMember
  in
  falseNotTrue (trans (sym negNotSelected) negSelected)
  where
  falseNotTrue : false ≡ true → ⊥
  falseNotTrue ()

record NonzeroCutoffOrbitRepresented (N : Nat) (k : Z3.FourierMode) : Set where
  field
    representative : Z3.FourierMode
    representativeInCanonicalCutoff :
      representative Cube.∈ canonicalCutoffOrbitModes N
    representativeIsKOrNegK :
      (representative ≡ k) ⊎ (representative ≡ Z3.negateMode k)

open NonzeroCutoffOrbitRepresented public

canonicalCutoffRepresentsEveryNonzeroOrbit :
  ∀ {N k} →
  Cube.InCutoffCube N k →
  Z3.NonZeroMode k →
  NonzeroCutoffOrbitRepresented N k
canonicalCutoffRepresentsEveryNonzeroOrbit {N} {k} cutoff nonzero
  with Half.canonicalNonzeroOrbitChoice k nonzero
... | Half.chooseK kSelected negNotSelected = record
  { representative = k
  ; representativeInCanonicalCutoff =
      canonicalCutoffCompleteForPositive cutoff kSelected
  ; representativeIsKOrNegK = inj₁ refl
  }
... | Half.chooseNegK kNotSelected negSelected = record
  { representative = Z3.negateMode k
  ; representativeInCanonicalCutoff =
      canonicalCutoffCompleteForPositive
        negCutoff negSelected
  ; representativeIsKOrNegK = inj₂ refl
  }
  where
  kMember : k Cube.∈ Cube.cutoffModes N
  kMember = Cube.cutoffModeEnumerationComplete N k cutoff

  negMember : Z3.negateMode k Cube.∈ Cube.cutoffModes N
  negMember = Cube.cutoffClosedUnderNegation N k kMember

  negCutoff : Cube.InCutoffCube N (Z3.negateMode k)
  negCutoff = Cube.cutoffModeEnumerationSound N (Z3.negateMode k) negMember

round63FixedCutoffOneRepresentativePerRealityOrbitConstructed : Bool
round63FixedCutoffOneRepresentativePerRealityOrbitConstructed = true

round63FixedCutoffOneRepresentativePerRealityOrbitConstructedIsTrue :
  round63FixedCutoffOneRepresentativePerRealityOrbitConstructed ≡ true
round63FixedCutoffOneRepresentativePerRealityOrbitConstructedIsTrue = refl
