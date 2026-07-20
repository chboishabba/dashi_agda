module DASHI.Codec.DNAFirstFormalism where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_; proj₁)

------------------------------------------------------------------------
-- CAGT carrier and canonical involutions.

data Base : Set where
  A C G T : Base

complement : Base → Base
complement A = T
complement T = A
complement C = G
complement G = C

complement-involutive : ∀ b → complement (complement b) ≡ b
complement-involutive A = refl
complement-involutive C = refl
complement-involutive G = refl
complement-involutive T = refl

reverse : ∀ {X : Set} → List X → List X
reverse xs = go xs []
  where
  go : ∀ {X : Set} → List X → List X → List X
  go [] acc = acc
  go (x ∷ xs) acc = go xs (x ∷ acc)

map : ∀ {X Y : Set} → (X → Y) → List X → List Y
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

reverseComplement : List Base → List Base
reverseComplement xs = map complement (reverse xs)

------------------------------------------------------------------------
-- Geometry: line, sheet/voxel, six-sheet slab, and 27-cube.

data Axis3 : Set where
  axis0 axis1 axis2 : Axis3

Line3 : Set
Line3 = Axis3 → Base

Voxel9 : Set
Voxel9 = Axis3 → Axis3 → Base

SixSheet : Set
SixSheet = Axis3 → Axis3 → Base × Base

Cube27 : Set
Cube27 = Axis3 → Axis3 → Axis3 → Base

layer : Cube27 → Axis3 → Voxel9
layer cube k i j = cube i j k

stack : Cube27 → Axis3 → Axis3 → SixSheet
stack cube k l i j = layer cube k i j , layer cube l i j

------------------------------------------------------------------------
-- Valid = generable. Chemistry and viability are represented in the
-- admissible next-base fibre, rather than appended as terminal checks.

record ConstraintMachine : Set₁ where
  field
    State : Set
    initial : State
    admissible : State → Base → Set
    step : State → Base → State

open ConstraintMachine public

data Trace (M : ConstraintMachine) : State M → List Base → Set where
  emptyTrace :
    ∀ {s} → Trace M s []

  emitTrace :
    ∀ {s b bs} →
    admissible M s b →
    Trace M (step M s b) bs →
    Trace M s (b ∷ bs)

Generable : ConstraintMachine → List Base → Set
Generable M xs = Trace M (initial M) xs

------------------------------------------------------------------------
-- Concrete constraint-state factorisation. The component types remain
-- parameters so a finite suffix automaton, bounded GC debt, bounded hairpin
-- guard, lift phase, and orbit/coset phase can be instantiated without
-- confusing the operational state with the underlying ternary algebra.

record DNAStateComponents : Set₁ where
  field
    SuffixState : Set
    GCDebtState : Set
    HairpinGuardState : Set
    LiftPhaseState : Set
    OrbitPhaseState : Set

open DNAStateComponents public

record DNAState (C₀ : DNAStateComponents) : Set where
  constructor dnaState
  field
    suffix : SuffixState C₀
    gcDebt : GCDebtState C₀
    hairpinGuard : HairpinGuardState C₀
    liftPhase : LiftPhaseState C₀
    orbitPhase : OrbitPhaseState C₀

------------------------------------------------------------------------
-- Exact feed-forward viability is existential completion. Implementations
-- may expose a separate sound bounded/cache approximation, but that does not
-- redefine the formal language.

record CompletionViability : Set₁ where
  field
    Partial : Set
    Complete : Set
    extends : Partial → Complete → Set
    validComplete : Complete → Set

  Viable : Partial → Set
  Viable p = Σ Complete (λ c → extends p c × validComplete c)

------------------------------------------------------------------------
-- Recognisable 3/9/27 lift tower. The uniqueness/local-radius witness is a
-- required field, not silently promoted from block notation alone.

record LiftTower : Set₁ where
  field
    LineSymbol : Set
    VoxelSymbol : Set
    CubeSymbol : Set

    liftLine : Line3 → LineSymbol
    liftVoxel : Voxel9 → VoxelSymbol
    liftCube : Cube27 → CubeSymbol

    lineRecognisable : Set
    voxelRecognisable : Set
    cubeRecognisable : Set

    lineMacroAdmissible : LineSymbol → LineSymbol → Set
    voxelMacroAdmissible : VoxelSymbol → VoxelSymbol → Set
    cubeMacroAdmissible : CubeSymbol → CubeSymbol → Set

------------------------------------------------------------------------
-- Eigenstate/residual systems are dynamical: eigenstates carry a fixed-point
-- or low-action witness, and involution commutes with representative and
-- residual selection.

record EigenResidualSystem : Set₁ where
  field
    Block : Set
    Feature : Set
    Eigenstate : Set

    blockInvolution : Block → Block
    featureInvolution : Feature → Feature
    eigenInvolution : Eigenstate → Eigenstate

    features : Block → Feature
    representative : Block → Eigenstate
    residual : Block → Feature

    inducedUpdate : Eigenstate → Eigenstate
    eigenFixed : ∀ e → inducedUpdate e ≡ e

    representativeEquivariant :
      ∀ b → representative (blockInvolution b) ≡
            eigenInvolution (representative b)

    residualEquivariant :
      ∀ b → residual (blockInvolution b) ≡
            featureInvolution (residual b)

------------------------------------------------------------------------
-- Multiscale checks are predicates/invariants on generated structure. This
-- record deliberately does not append a binary CRC primitive.

record MultiscaleInvariantFamily : Set₁ where
  field
    Object : Set
    Mirror : Object → Object
    Level : Set
    Value : Level → Set
    inverse : ∀ l → Value l → Value l
    invariant : ∀ l → Object → Value l
    mirrorLaw : ∀ l x → invariant l (Mirror x) ≡ inverse l (invariant l x)

------------------------------------------------------------------------
-- Stateful variable branching. `branchCount` records the exact legal arity
-- exposed to arithmetic/ANS coding. No fixed number of trits or payload bits
-- is assigned to a 27-base cube.

record StreamingChoiceSurface : Set₁ where
  field
    State : Set
    next : State → Base → State
    legal : State → Base → Bool
    branchCount : State → Nat

    CoderState : Set
    select : CoderState → State → Base × CoderState
    selectionIsLegal :
      ∀ c s → legal s (proj₁ (select c s)) ≡ true
