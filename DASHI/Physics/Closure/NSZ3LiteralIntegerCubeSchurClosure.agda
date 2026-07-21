module DASHI.Physics.Closure.NSZ3LiteralIntegerCubeSchurClosure where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_*_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3

------------------------------------------------------------------------
-- Literal Z^3 shell-Schur closure.
--
-- This module records the exact dependency chain needed by the cutoff-uniform
-- full-shell theorem.  Unlike the earlier SC1--SC9 carrier, the finite objects
-- here are literal lists of Fourier modes/pairs and the final row/column
-- budgets are derived from the shell-majorant estimates in this same package.
-- Thus a downstream theorem cannot combine an unrelated enumerator, fold
-- identity, geometric tail, intersection estimate, or Schur constant.
------------------------------------------------------------------------

record ResonantPair : Set where
  constructor pair
  field
    left right : Z3.FourierMode

open ResonantPair public

record LiteralIntegerCubeEnumeration {i : Level} : Set (lsuc i) where
  field
    cube : Nat → List Z3.FourierMode
    CubeMember : Nat → Z3.FourierMode → Set i
    listedIffMember : ∀ N k → CubeMember N k → Set i

    -- Literal duplicate-freeness and exact cardinality control.
    DuplicateFree : List Z3.FourierMode → Set i
    cubeDuplicateFree : ∀ N → DuplicateFree (cube N)

    listLength : List Z3.FourierMode → Nat
    cubeLengthBound : Nat → Nat
    literalCubeLengthBound : ∀ N → Set i

open LiteralIntegerCubeEnumeration public

record LiteralWeightedFolds
    {s i : Level}
    (Scalar : Set s)
    (E : LiteralIntegerCubeEnumeration {i = i}) :
    Set (lsuc (s ⊔ i)) where
  field
    shell : Nat → List Z3.FourierMode
    shellPairs : Nat → Nat → Z3.FourierMode → List ResonantPair

    weight : Nat → Z3.FourierMode → Scalar
    pairWeight : Nat → Nat → Nat → ResonantPair → Scalar

    fold : List Scalar → Scalar
    mapWeight : Nat → List Z3.FourierMode → List Scalar
    mapPairWeight : Nat → Nat → Nat → List ResonantPair → List Scalar

    intendedShellSum : Nat → Nat → Scalar
    intendedPairSum : Nat → Nat → Nat → Z3.FourierMode → Scalar

    literalShellFoldIdentifiesSum :
      ∀ sigma j →
      fold (mapWeight sigma (shell j)) ≡ intendedShellSum sigma j

    literalPairFoldIdentifiesSum :
      ∀ alpha a b k →
      fold (mapPairWeight alpha a b (shellPairs a b k)) ≡
      intendedPairSum alpha a b k

open LiteralWeightedFolds public

record LiteralShellMajorantEstimates
    {s i : Level}
    (Scalar : Set s)
    (E : LiteralIntegerCubeEnumeration {i = i})
    (Folds : LiteralWeightedFolds Scalar E) :
    Set (lsuc (s ⊔ i)) where
  field
    _≤_ : Scalar → Scalar → Set s
    add multiply : Scalar → Scalar → Scalar
    zero one : Scalar

    twoPower : Nat → Scalar
    inverseTwoPower : Nat → Scalar
    minNat : Nat → Nat → Nat

    -- Geometric-series shell and radial tails.
    shellTail : Nat → Nat → Scalar
    shellTailMajorant : Nat → Nat → Scalar
    geometricSeriesTailEstimate :
      ∀ sigma J → _≤_ (shellTail sigma J) (shellTailMajorant sigma J)

    -- The 2^(2 min(a,b))-type lattice shell-intersection estimate.
    shellIntersectionCount : Nat → Nat → Z3.FourierMode → Scalar
    shellIntersectionConstant : Scalar
    shellIntersectionBound :
      ∀ a b k →
      _≤_ (shellIntersectionCount a b k)
        (multiply shellIntersectionConstant (twoPower (2 * minNat a b)))

    -- Polarization remains valid when one or both transverse geometries
    -- degenerate; no division by a sine or frame determinant is permitted.
    polarizationSize : ResonantPair → Scalar
    polarizationMajorant : Nat → Nat → Scalar
    degenerateGeometryPolarizationEstimate :
      ∀ a b k interaction →
      _≤_ (polarizationSize interaction) (polarizationMajorant a b)

    shellMajorant : Nat → Nat → Nat → Scalar
    foldMajorants : Nat → Scalar
    summedShellMajorant : Nat → Scalar
    sumShellMajorants :
      ∀ K →
      _≤_ (foldMajorants K) (summedShellMajorant K)

open LiteralShellMajorantEstimates public

record DerivedFixedSchurConstants
    {s i : Level}
    (Scalar : Set s)
    (E : LiteralIntegerCubeEnumeration {i = i})
    (Folds : LiteralWeightedFolds Scalar E)
    (M : LiteralShellMajorantEstimates Scalar E Folds) :
    Set (lsuc (s ⊔ i)) where
  field
    rowConstant columnConstant : Scalar
    rowExpression columnExpression : Nat → Nat → Z3.FourierMode → Scalar

    rowFromShellMajorants :
      ∀ K N target →
      _≤_ M (rowExpression K N target) rowConstant

    columnFromShellMajorants :
      ∀ K N source →
      _≤_ M (columnExpression K N source) columnConstant

open DerivedFixedSchurConstants public

record Z3LiteralShellSchurClosure
    {s i : Level}
    (Scalar : Set s) : Set (lsuc (s ⊔ i)) where
  field
    enumeration : LiteralIntegerCubeEnumeration {i = i}
    weightedFolds : LiteralWeightedFolds Scalar enumeration
    majorants : LiteralShellMajorantEstimates Scalar enumeration weightedFolds
    fixedConstants :
      DerivedFixedSchurConstants Scalar enumeration weightedFolds majorants

open Z3LiteralShellSchurClosure public

-- Named endpoint projections used by audits and downstream synthesis.
concreteDuplicateFreeIntegerCubeEnumerator :
  ∀ {s i} {Scalar : Set s} →
  Z3LiteralShellSchurClosure {i = i} Scalar →
  Nat → List Z3.FourierMode
concreteDuplicateFreeIntegerCubeEnumerator C = cube (enumeration C)

literalIntegerCubeLengthBound :
  ∀ {s i} {Scalar : Set s} →
  (C : Z3LiteralShellSchurClosure {i = i} Scalar) →
  ∀ N → Set i
literalIntegerCubeLengthBound C = literalCubeLengthBound (enumeration C)

fixedRowConstant :
  ∀ {s i} {Scalar : Set s} →
  Z3LiteralShellSchurClosure {i = i} Scalar → Scalar
fixedRowConstant C = rowConstant (fixedConstants C)

fixedColumnConstant :
  ∀ {s i} {Scalar : Set s} →
  Z3LiteralShellSchurClosure {i = i} Scalar → Scalar
fixedColumnConstant C = columnConstant (fixedConstants C)

fixedRowEstimate :
  ∀ {s i} {Scalar : Set s}
    (C : Z3LiteralShellSchurClosure {i = i} Scalar) →
  ∀ K N target →
  _≤_ (majorants C)
    (rowExpression (fixedConstants C) K N target)
    (fixedRowConstant C)
fixedRowEstimate C = rowFromShellMajorants (fixedConstants C)

fixedColumnEstimate :
  ∀ {s i} {Scalar : Set s}
    (C : Z3LiteralShellSchurClosure {i = i} Scalar) →
  ∀ K N source →
  _≤_ (majorants C)
    (columnExpression (fixedConstants C) K N source)
    (fixedColumnConstant C)
fixedColumnEstimate C = columnFromShellMajorants (fixedConstants C)
