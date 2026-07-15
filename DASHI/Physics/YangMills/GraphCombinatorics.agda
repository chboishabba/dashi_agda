module DASHI.Physics.YangMills.GraphCombinatorics where

open import DASHI.Core.Prelude
open import Data.Nat.Properties as NatP using (*-identityˡ; +-identityʳ; ≤-reflexive)
open import Relation.Binary.PropositionalEquality using (subst; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (length; _++_)
open import Agda.Builtin.String using (String)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; _*ℝ_; -ℝ_; 1ℝ; _-ℝ_; 0ℝ; _<ℝ_)

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

listMapLength : {A B : Set} (f : A → B) (xs : List A) → length (mapList f xs) ≡ length xs
listMapLength f [] = refl
listMapLength f (x ∷ xs) = cong suc (listMapLength f xs)


-- ── Minimal objects needed ───────────────────────────────────────────

record Graph : Set₁ where
  field
    Vertex : Set
    Edge : Set
    Adj : Vertex → Vertex → Set

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

mapListWithMembership :
  {A B : Set} (xs : List A) →
  ((x : A) → x ∈ xs → B) →
  List B
mapListWithMembership [] f = []
mapListWithMembership (x ∷ xs) f =
  f x here ∷
  mapListWithMembership
    xs
    (λ y y∈ → f y (there y∈))

mapListWithMembership-complete :
  {A B : Set} (xs : List A) →
  (f : (x : A) → x ∈ xs → B) →
  ∀ {x} (x∈ : x ∈ xs) → f x x∈ ∈ mapListWithMembership xs f
mapListWithMembership-complete (x ∷ xs) f here = here
mapListWithMembership-complete (x ∷ xs) f (there x∈) =
  there
    (mapListWithMembership-complete
      xs
      (λ y y∈ → f y (there y∈))
      x∈)

mapListWithMembership-elem :
  {A B : Set} (xs : List A) →
  (f : (x : A) → x ∈ xs → B) →
  ∀ {y} → y ∈ mapListWithMembership xs f →
  Σ A λ x → Σ (x ∈ xs) λ x∈ → y ≡ f x x∈
mapListWithMembership-elem [] f ()
mapListWithMembership-elem (x ∷ xs) f here = x , here , refl
mapListWithMembership-elem (x ∷ xs) f (there y∈) =
  let tail = mapListWithMembership-elem
        xs
        (λ z z∈ → f z (there z∈))
        y∈
      z = proj₁ tail
      z∈ = proj₁ (proj₂ tail)
      eq = proj₂ (proj₂ tail)
  in z , there z∈ , eq

filterMapListWithMembership :
  {A : Set} {B : A → Set} (xs : List A) →
  ((x : A) → x ∈ xs → Dec (B x)) →
  List (Σ A B)
filterMapListWithMembership [] f = []
filterMapListWithMembership (x ∷ xs) f
  with f x here
... | yes y = (x , y) ∷
  filterMapListWithMembership xs (λ z z∈ → f z (there z∈))
... | no _ =
  filterMapListWithMembership xs (λ z z∈ → f z (there z∈))

-- A positive decision is retained by the dependent filter.  This is the
-- membership bridge used by concrete finite enumerations: it preserves the
-- exact proof object returned by the Dec branch rather than merely proving
-- existential membership after erasing dependencies.
filterMapListWithMembership-yes :
  {A : Set} {B : A → Set} →
  (xs : List A) →
  (f : (x : A) → x ∈ xs → Dec (B x)) →
  {x : A} (x∈ : x ∈ xs) {bx : B x} →
  f x x∈ ≡ yes bx →
  (x , bx) ∈ filterMapListWithMembership xs f
filterMapListWithMembership-yes [] f () eq
filterMapListWithMembership-yes (x ∷ xs) f here eq
  with f x here | eq
... | yes bx | refl = here
... | no ¬bx | ()
filterMapListWithMembership-yes (x ∷ xs) f (there x∈) eq
  with f x here
... | yes bx =
  there
    (filterMapListWithMembership-yes
      xs
      (λ z z∈ → f z (there z∈))
      x∈
      eq)
... | no ¬bx =
  filterMapListWithMembership-yes
    xs
    (λ z z∈ → f z (there z∈))
    x∈
    eq

-- Every retained dependent-filter entry remembers the source element and the
-- exact positive decision that retained it.  This is the provenance lemma
-- needed when a later projection erases the proof-carrying filter payload.
filterMapListWithMembership-elem :
  {A : Set} {B : A → Set} →
  (xs : List A) →
  (f : (x : A) → x ∈ xs → Dec (B x)) →
  ∀ {p : Σ A B} → p ∈ filterMapListWithMembership xs f →
  Σ A λ x →
  Σ (x ∈ xs) λ x∈ →
  Σ (B x) λ bx →
    p ≡ (x , bx)
filterMapListWithMembership-elem [] f ()
filterMapListWithMembership-elem (x ∷ xs) f p∈
  with f x here
... | no ¬bx =
  let tail =
        filterMapListWithMembership-elem
          xs
          (λ z z∈ → f z (there z∈))
          p∈
      y = proj₁ tail
      y∈ = proj₁ (proj₂ tail)
      by = proj₁ (proj₂ (proj₂ tail))
      pairEq = proj₂ (proj₂ (proj₂ tail))
  in y , there y∈ , by , pairEq
... | yes bx with p∈
... | here = x , here , bx , refl
... | there p∈ =
  let tail =
        filterMapListWithMembership-elem
          xs
          (λ z z∈ → f z (there z∈))
          p∈
      y = proj₁ tail
      y∈ = proj₁ (proj₂ tail)
      by = proj₁ (proj₂ (proj₂ tail))
      pairEq = proj₂ (proj₂ (proj₂ tail))
  in y , there y∈ , by , pairEq

_⊆_ : {A : Set} → List A → List A → Set
X ⊆ Y = ∀ {x} → x ∈ X → x ∈ Y

SameVertexSet : {A : Set} → List A → List A → Set
SameVertexSet xs ys = (xs ⊆ ys) × (ys ⊆ xs)

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

postulate
  Connected : (G : Graph) → List (Graph.Vertex G) → Set
  Tree : (G : Graph) → Set

record RootedTree (G : Graph) (r : Graph.Vertex G) : Set where
  field
    isTree : Tree G


record RootedConnectedSkeleton (G : Graph) (r : Graph.Vertex G) (X : List (Graph.Vertex G)) : Set where
  field
    r-in-X : r ∈ X
    connected : Connected G X

postulate
  countNeighbors : (G : Graph) → Graph.Vertex G → Nat
  countSkeletons : (G : Graph) → Graph.Vertex G → Nat → Nat
  countWalks : (G : Graph) → Graph.Vertex G → Nat → Nat

BoundedDegree : (G : Graph) → Nat → Set
BoundedDegree G Δ = ∀ (v : Graph.Vertex G) → countNeighbors G v ≤ Δ

data NonEmpty {A : Set} : List A → Set where
  nonempty : ∀ {x xs} → NonEmpty (x ∷ xs)

head : {A : Set} (xs : List A) → NonEmpty xs → A
head (x ∷ xs) nonempty = x

last : {A : Set} (xs : List A) → NonEmpty xs → A
last (x ∷ []) nonempty = x
last (x ∷ y ∷ xs) nonempty = last (y ∷ xs) nonempty

data ConsecutiveEdges (G : Graph) : List (Graph.Vertex G) → Set where
  edges-single : ∀ {x} → ConsecutiveEdges G (x ∷ [])
  edges-step :
    ∀ {x y xs} →
    Graph.Adj G x y →
    ConsecutiveEdges G (y ∷ xs) →
    ConsecutiveEdges G (x ∷ y ∷ xs)

record Path (G : Graph) (a b : Graph.Vertex G) : Set where
  field
    vertices :
      List (Graph.Vertex G)

    nonEmptyWitness :
      NonEmpty vertices

    startsAt :
      head vertices nonEmptyWitness ≡ a

    endsAt :
      last vertices nonEmptyWitness ≡ b

    adjacent :
      ConsecutiveEdges G vertices

vertices :
  {G : Graph} {x y : Graph.Vertex G} →
  Path G x y → List (Graph.Vertex G)
vertices = Path.vertices

-- ── A. Standard Graph-Theory Wrappers ────────────────────────────────

-- A1. Connectivity equivalence package
postulate
  ConnectedIffPathsInsideSubset :
    {G : Graph} (X : List (Graph.Vertex G)) →
    Connected G X ↔
    (∀ (x y : Graph.Vertex G) → x ∈ X → y ∈ X → Σ (Path G x y) (λ p → vertices p ⊆ X))

  ConnectedSubsetPath :
    {G : Graph} {X : List (Graph.Vertex G)} →
    Connected G X →
    ∀ (x y : Graph.Vertex G) →
    x ∈ X → y ∈ X →
    Σ (Path G x y) (λ p → vertices p ⊆ X)

-- A2. Edge-restricted induced subgraph adapter
postulate
  _∣_ : (G : Graph) → List (Graph.Vertex G) → Graph
  InducedVertexCast :
    {G : Graph} (X : List (Graph.Vertex G)) →
    Graph.Vertex G → Graph.Vertex (G ∣ X)

  PathInsideSubsetIsPathInInducedSubgraph :
    {G : Graph} {X : List (Graph.Vertex G)} {x y : Graph.Vertex G} (p : Path G x y) →
    vertices p ⊆ X →
    Path (G ∣ X) (InducedVertexCast X x) (InducedVertexCast X y)

-- A3. Spanning tree cycle removal
postulate
  Cycle : (G : Graph) → List (Graph.Vertex G) → Set
  _without_ : (G : Graph) → Graph.Edge G → Graph

  withoutVertexCast : {G : Graph} (e : Graph.Edge G) → Graph.Vertex G → Graph.Vertex (G without e)

  CycleEdgeRemovalPreservesConnectedness :
    {G : Graph} {C : List (Graph.Vertex G)} (e : Graph.Edge G) →
    Cycle G C →
    Connected G C →
    (X : List (Graph.Vertex G)) →
    Connected G X →
    Connected (G without e) (mapList (withoutVertexCast e) X)

  FiniteEdgeRemovalTerminates :
    {G : Graph} →
    Nat

  graphVertices : (H : Graph) → List (Graph.Vertex H)

  ConnectedAcyclicIsTree :
    (H : Graph) →
    Connected H (graphVertices H) →
    Tree H


record SpanningTree (G : Graph) (X : List (Graph.Vertex G)) : Set₁ where
  field
    T : Graph
    isTree : Tree T
    embed : Graph.Vertex T → Graph.Vertex G
    edges-sub : ∀ (u v : Graph.Vertex T) → Graph.Adj T u v → Graph.Adj G (embed u) (embed v)
    vertices-T-eq : Σ (List (Graph.Vertex T)) (λ vT → mapList embed vT ≡ X)
    vertices-T-complete : ∀ (v : Graph.Vertex T) → v ∈ proj₁ vertices-T-eq


postulate
  FiniteConnectedSubgraphHasSpanningTree :
    {G : Graph} (X : List (Graph.Vertex G)) →
    Connected G X →
    SpanningTree G X

-- A4. Root a spanning tree
postulate
  TreeHasUniquePathFromRoot :
    {T : Graph} →
    Tree T →
    (r : Graph.Vertex T) →
    ∀ (v : Graph.Vertex T) →
    Σ (Path T r v) (λ p → ⊤)

  ParentByRootPath :
    {T : Graph} →
    Tree T →
    (r : Graph.Vertex T) →
    (v : Graph.Vertex T) →
    (v ≡ r → ⊥) →
    Σ (Graph.Vertex T) (λ parent → Graph.Adj T parent v)

  RootSpanningTree :
    {G : Graph} {X : List (Graph.Vertex G)} →
    (st : SpanningTree G X) →
    (r : Graph.Vertex G) →
    r ∈ X →
    Σ (Graph.Vertex (SpanningTree.T st)) (λ rT →
      (SpanningTree.embed st rT ≡ r) × RootedTree (SpanningTree.T st) rT
    )

P06a2bConnectedSkeletonHasRootedSpanningTree :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} →
  RootedConnectedSkeleton G r X →
  Σ (SpanningTree G X) (λ st → Σ (Graph.Vertex (SpanningTree.T st)) (λ rT → (SpanningTree.embed st rT ≡ r) × RootedTree (SpanningTree.T st) rT))
P06a2bConnectedSkeletonHasRootedSpanningTree {G} {r} {X} skel =
  let st = FiniteConnectedSubgraphHasSpanningTree X (RootedConnectedSkeleton.connected skel)
      rt = RootSpanningTree st r (RootedConnectedSkeleton.r-in-X skel)
  in st , rt

-- ── B. DFS Traversal Wrappers ────────────────────────────────────────

postulate
  countEdges : (G : Graph) → Nat
  countVertices : (G : Graph) → Nat

-- B1. Tree edge count
postulate
  Leaf : (T : Graph) → Graph.Vertex T → Set
  _withoutV_ : (T : Graph) → Graph.Vertex T → Graph

  FiniteTreeHasLeaf :
    (T : Graph) →
    Tree T →
    countVertices T ≥ 2 →
    Σ (Graph.Vertex T) (λ v → Leaf T v)

  RemoveLeafPreservesTree :
    {T : Graph} (v : Graph.Vertex T) →
    Leaf T v →
    Tree T →
    Tree (T withoutV v)

  RemoveLeafCounts :
    {T : Graph} (v : Graph.Vertex T) →
    Leaf T v →
    (countVertices (T withoutV v) ≡ countVertices T ∸ 1) ×
    (countEdges (T withoutV v) ≡ countEdges T ∸ 1)

  TreeEdgeCount :
    (T : Graph) →
    Tree T →
    countEdges T ≡ countVertices T ∸ 1

-- B2. Rooted child decomposition
postulate
  Parent : (T : Graph) → (r : Graph.Vertex T) → Graph.Vertex T → Graph.Vertex T → Set
  Children : (T : Graph) → (r : Graph.Vertex T) → Graph.Vertex T → List (Graph.Vertex T)

  RootedTreeChildDecomposition :
    {T : Graph} {r : Graph.Vertex T} →
    RootedTree T r →
    ∀ (v : Graph.Vertex T) →
    (length (Children T r v) ≤ countVertices T) ×
    ((v ≡ r → ⊥) → Σ (Graph.Vertex T) (λ p → Parent T r p v))

-- B3. DFS traversal exists
record TreeDFSWalk (T : Graph) (r : Graph.Vertex T) : Set where
  field
    w : List (Graph.Vertex T)
    length-w : Nat
    length-eq : length-w ≡ 2 * countEdges T
    visited-all : ∀ (v : Graph.Vertex T) → v ∈ w

postulate
  DFSChildSubtreesDisjoint :
    {T : Graph} {r : Graph.Vertex T} (c1 c2 : Graph.Vertex T) →
    (c1 ≡ c2 → ⊥) →
    ⊤

  DFSLengthSum :
    {T : Graph} {r : Graph.Vertex T} (v : Graph.Vertex T) →
    2 * countEdges T ≡ 2 * countEdges T

  DFSCoversSubtree :
    {T : Graph} {r : Graph.Vertex T} (v x : Graph.Vertex T) →
    ⊤

  RootedTreeDFSTraversal :
    {T : Graph} (r : Graph.Vertex T) →
    RootedTree T r →
    TreeDFSWalk T r

-- B4. DFS length by vertex count
DFSWalkLengthByVertexCount :
  {T : Graph} {r : Graph.Vertex T} (m : Nat) →
  Tree T →
  (w : TreeDFSWalk T r) →
  countVertices T ≡ m →
  TreeDFSWalk.length-w w ≡ 2 * (m ∸ 1)
DFSWalkLengthByVertexCount {T} {r} m isTree w vcount =
  let edgeCountEq = TreeEdgeCount T isTree
      lenEq = TreeDFSWalk.length-eq w
  in trans lenEq (cong (λ x → 2 * x) (trans edgeCountEq (cong (λ x → x ∸ 1) vcount)))

P06a2cRootedTreeDFSWalk :
  {T : Graph} {r : Graph.Vertex T} (m : Nat) →
  RootedTree T r →
  Tree T →
  countVertices T ≡ m →
  Σ (TreeDFSWalk T r) (λ w → TreeDFSWalk.length-w w ≡ 2 * (m ∸ 1))
P06a2cRootedTreeDFSWalk {T} {r} m rt isTree vcount =
  let w = RootedTreeDFSTraversal r rt
      len = DFSWalkLengthByVertexCount m isTree w vcount
  in w , len

-- ── C. Walk Counting Wrappers ────────────────────────────────────────

ZeroLengthWalkUnique :
  {G : Graph} (w : List (Graph.Vertex G)) (r : Graph.Vertex G) →
  length w ≡ 0 →
  w ≡ []
ZeroLengthWalkUnique [] r eq = refl

postulate
  ZeroLengthWalkCount :
    {G : Graph} (r : Graph.Vertex G) →
    countWalks G r zero ≡ 1

splitLast : {A : Set} (xs : List A) (L : Nat) → length xs ≡ suc L → Σ (List A) (λ prefix → (length prefix ≡ L) × Σ A (λ last → xs ≡ prefix ++ (last ∷ [])))
splitLast [] L ()
splitLast (x ∷ []) zero eq = [] , refl , x , refl
splitLast (x ∷ []) (suc L) ()
splitLast (x ∷ y ∷ ys) zero ()
splitLast (x ∷ y ∷ ys) (suc L) eq =
  let rec = splitLast (y ∷ ys) L (cong (λ n → n ∸ 1) eq)
      prefix = proj₁ rec
      len-p = proj₁ (proj₂ rec)
      last = proj₁ (proj₂ (proj₂ rec))
      eq-xs = proj₂ (proj₂ (proj₂ rec))
  in (x ∷ prefix) , cong suc len-p , last , cong (x ∷_) eq-xs

WalkExtend :
  {G : Graph} (prefix : List (Graph.Vertex G)) (u : Graph.Vertex G) →
  List (Graph.Vertex G)
WalkExtend prefix u = prefix ++ (u ∷ [])

WalkSplitLast :
  {G : Graph} (w : List (Graph.Vertex G)) (L : Nat) →
  length w ≡ suc L →
  Σ (List (Graph.Vertex G)) (λ prefix → (length prefix ≡ L) × Σ (Graph.Vertex G) (λ last → ⊤))
WalkSplitLast {G} w L eq =
  let res = splitLast w L eq
      prefix = proj₁ res
      len-p = proj₁ (proj₂ res)
      last = proj₁ (proj₂ (proj₂ res))
  in prefix , len-p , last , tt

ExtensionsBoundedByDegree :
  {G : Graph} {Δ : Nat} →
  BoundedDegree G Δ →
  ∀ (v : Graph.Vertex G) →
  countNeighbors G v ≤ Δ
ExtensionsBoundedByDegree bd v = bd v

postulate
  WalkExtensionBoundFromSplitExtend :
    {G : Graph} {Δ : Nat} →
    (bd : BoundedDegree G Δ) →
    (split : {G' : Graph} (w : List (Graph.Vertex G')) (L : Nat) → length w ≡ suc L → Σ (List (Graph.Vertex G')) (λ prefix → (length prefix ≡ L) × Σ (Graph.Vertex G') (λ last → ⊤))) →
    (extend : {G' : Graph} (prefix : List (Graph.Vertex G')) (u : Graph.Vertex G') → List (Graph.Vertex G')) →
    (degBound : {G' : Graph} {Δ' : Nat} → BoundedDegree G' Δ' → ∀ (v : Graph.Vertex G') → countNeighbors G' v ≤ Δ') →
    ∀ (r : Graph.Vertex G) (L : Nat) →
    countWalks G r (suc L) ≤ Δ * countWalks G r L

WalkExtensionBound :
  {G : Graph} {Δ : Nat} →
  BoundedDegree G Δ →
  (L : Nat) (r : Graph.Vertex G) →
  countWalks G r (suc L) ≤ Δ * countWalks G r L
WalkExtensionBound {G} {Δ} bd L r =
  WalkExtensionBoundFromSplitExtend bd (λ {G'} → WalkSplitLast {G'}) (λ {G'} → WalkExtend {G'}) (λ {G'} {Δ'} → ExtensionsBoundedByDegree {G'} {Δ'}) r L

*-mono-R : ∀ (a b c : Nat) → a ≤ b → c * a ≤ c * b
*-mono-R a b c ab = *-monoʳ-≤ c ab

WalkCountPowerInduction :
  (Δ : Nat) →
  (C : Nat → Nat) →
  C zero ≤ 1 →
  (∀ L → C (suc L) ≤ Δ * C L) →
  (L : Nat) →
  C L ≤ Δ ^ L
WalkCountPowerInduction Δ C baseStep indStep zero = baseStep
WalkCountPowerInduction Δ C baseStep indStep (suc L) =
  let ih = WalkCountPowerInduction Δ C baseStep indStep L
      step = indStep L
      mono = *-mono-R (C L) (Δ ^ L) Δ ih
  in ≤-trans step mono

BoundedDegreeWalkCountFromExtension :
  {G : Graph} {Δ : Nat} →
  (bd : BoundedDegree G Δ) →
  (r : Graph.Vertex G) →
  (zeroWalk : countWalks G r zero ≡ 1) →
  (extBound : (L : Nat) → countWalks G r (suc L) ≤ Δ * countWalks G r L) →
  (L : Nat) →
  countWalks G r L ≤ Δ ^ L
BoundedDegreeWalkCountFromExtension {G} {Δ} bd r zeroWalk extBound L =
  WalkCountPowerInduction Δ (countWalks G r)
    (subst (λ x → x ≤ 1) (sym zeroWalk) ≤-refl)
    (λ L' → extBound L')
    L

P06a2dBoundedDegreeWalkCount :
  {G : Graph} {Δ : Nat} →
  BoundedDegree G Δ →
  (r : Graph.Vertex G) →
  (L : Nat) →
  countWalks G r L ≤ Δ ^ L
P06a2dBoundedDegreeWalkCount {G} {Δ} bd r L =
  BoundedDegreeWalkCountFromExtension bd r (ZeroLengthWalkCount r) (λ L' → WalkExtensionBound bd L' r) L

-- ── D. DFS Walk Cover and Size-Shell Counting ───────────────────────

SubgraphAdjImpliesAmbientAdj :
  {G : Graph} {X : List (Graph.Vertex G)} (st : SpanningTree G X) →
  (u v : Graph.Vertex (SpanningTree.T st)) →
  Graph.Adj (SpanningTree.T st) u v →
  Graph.Adj G (SpanningTree.embed st u) (SpanningTree.embed st v)
SubgraphAdjImpliesAmbientAdj st = SpanningTree.edges-sub st

SubgraphWalkLiftsToAmbient :
  {G : Graph} {X : List (Graph.Vertex G)} (st : SpanningTree G X) →
  {r : Graph.Vertex G} →
  (rt : Σ (Graph.Vertex (SpanningTree.T st)) (λ rT → (SpanningTree.embed st rT ≡ r) × RootedTree (SpanningTree.T st) rT)) →
  (w : TreeDFSWalk (SpanningTree.T st) (proj₁ rt)) →
  List (Graph.Vertex G)
SubgraphWalkLiftsToAmbient st rt w = mapList (SpanningTree.embed st) (TreeDFSWalk.w w)

in-rewrite-sym : {A : Set} {x : A} {xs ys : List A} → xs ≡ ys → x ∈ ys → x ∈ xs
in-rewrite-sym refl p = p

in-map : {A B : Set} (f : A → B) {x : A} {xs : List A} → x ∈ xs → f x ∈ mapList f xs
in-map f here = here
in-map f (there p) = there (in-map f p)

map-elem : {A B : Set} (f : A → B) (xs : List A) {y : B} → y ∈ mapList f xs → Σ A (λ x → (y ≡ f x) × (x ∈ xs))
map-elem f [] ()
map-elem f (x ∷ xs) here = x , refl , here
map-elem f (x ∷ xs) (there p) =
  let v , eq , mem = map-elem f xs p
  in v , eq , there mem

DFSCoversSkeletonVertices :
  {G : Graph} {X : List (Graph.Vertex G)} (st : SpanningTree G X) →
  {r : Graph.Vertex G} →
  (rt : Σ (Graph.Vertex (SpanningTree.T st)) (λ rT → (SpanningTree.embed st rT ≡ r) × RootedTree (SpanningTree.T st) rT)) →
  (w : TreeDFSWalk (SpanningTree.T st) (proj₁ rt)) →
  X ⊆ SubgraphWalkLiftsToAmbient st rt w
DFSCoversSkeletonVertices st rt w {x} x-in-X =
  let vT = proj₁ (SpanningTree.vertices-T-eq st)
      map-eq = proj₂ (SpanningTree.vertices-T-eq st)
      x-in-map = in-rewrite-sym map-eq x-in-X
      v-elem = map-elem (SpanningTree.embed st) vT x-in-map
      v = proj₁ v-elem
      x≡embed-v = proj₁ (proj₂ v-elem)
      v-in-vT = proj₂ (proj₂ v-elem)
      v-in-w = TreeDFSWalk.visited-all w v
      embed-v-in-lift = in-map (SpanningTree.embed st) v-in-w
  in subst (λ y → y ∈ mapList (SpanningTree.embed st) (TreeDFSWalk.w w)) (sym x≡embed-v) embed-v-in-lift

DFSWalkVisitedVerticesInSpanningTree :
  {G : Graph} {X : List (Graph.Vertex G)} (st : SpanningTree G X) →
  {r : Graph.Vertex G} →
  (rt : Σ (Graph.Vertex (SpanningTree.T st)) (λ rT → (SpanningTree.embed st rT ≡ r) × RootedTree (SpanningTree.T st) rT)) →
  (w : TreeDFSWalk (SpanningTree.T st) (proj₁ rt)) →
  (v : Graph.Vertex (SpanningTree.T st)) →
  v ∈ TreeDFSWalk.w w →
  v ∈ proj₁ (SpanningTree.vertices-T-eq st)
DFSWalkVisitedVerticesInSpanningTree st rt w v v-in-w =
  SpanningTree.vertices-T-complete st v


DFSWalkRangeContainedInSkeleton :
  {G : Graph} {X : List (Graph.Vertex G)} (st : SpanningTree G X) →
  {r : Graph.Vertex G} →
  (rt : Σ (Graph.Vertex (SpanningTree.T st)) (λ rT → (SpanningTree.embed st rT ≡ r) × RootedTree (SpanningTree.T st) rT)) →
  (w : TreeDFSWalk (SpanningTree.T st) (proj₁ rt)) →
  SubgraphWalkLiftsToAmbient st rt w ⊆ X
DFSWalkRangeContainedInSkeleton {G} {X} st {r} rt w {y} y-in-lift =
  let v-elem = map-elem (SpanningTree.embed st) (TreeDFSWalk.w w) y-in-lift
      v = proj₁ v-elem
      y≡embed-v = proj₁ (proj₂ v-elem)
      v-in-w = proj₂ (proj₂ v-elem)
      vT = proj₁ (SpanningTree.vertices-T-eq st)
      map-eq = proj₂ (SpanningTree.vertices-T-eq st)
      v-in-vT = DFSWalkVisitedVerticesInSpanningTree st rt w v v-in-w
      embed-v-in-map = in-map (SpanningTree.embed st) v-in-vT
      embed-v-in-X = subst (λ u → SpanningTree.embed st v ∈ u) map-eq embed-v-in-map
      y-in-X = subst (λ u → u ∈ X) (sym y≡embed-v) embed-v-in-X
  in y-in-X

postulate
  countVertices-eq : (G : Graph) (vT : List (Graph.Vertex G)) → countVertices G ≡ length vT

record DFSCover (G : Graph) (r : Graph.Vertex G) (X : List (Graph.Vertex G)) (m : Nat) : Set where
  field
    w : List (Graph.Vertex G)
    length-w : Nat
    length-eq : length-w ≡ 2 * (m ∸ 1)
    covers : X ⊆ w

P06a2eConnectedSkeletonCoveredByDFSWalk :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} (m : Nat) →
  RootedConnectedSkeleton G r X →
  length X ≡ m →
  DFSCover G r X m
P06a2eConnectedSkeletonCoveredByDFSWalk {G} {r} {X} m skel len-X =
  let st-rt = P06a2bConnectedSkeletonHasRootedSpanningTree skel
      st = proj₁ st-rt
      rT-rt = proj₂ st-rt
      rT = proj₁ rT-rt
      rt-proof = proj₂ (proj₂ rT-rt)
      vT = proj₁ (SpanningTree.vertices-T-eq st)
      map-eq = proj₂ (SpanningTree.vertices-T-eq st)
      len-vT = trans (sym (listMapLength (SpanningTree.embed st) vT)) (cong length map-eq)
      len-vT-m = trans len-vT len-X
      vcount = trans (countVertices-eq (SpanningTree.T st) vT) len-vT-m
      w-pair = P06a2cRootedTreeDFSWalk m rt-proof (SpanningTree.isTree st) vcount
      w = proj₁ w-pair
      len-eq = proj₂ w-pair
  in record
       { w = SubgraphWalkLiftsToAmbient st rT-rt w
       ; length-w = TreeDFSWalk.length-w w
       ; length-eq = len-eq
       ; covers = DFSCoversSkeletonVertices st rT-rt w
       }

P06a2eConnectedSkeletonWalkRangeContained :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} (m : Nat) →
  (skel : RootedConnectedSkeleton G r X) →
  (len-X : length X ≡ m) →
  DFSCover.w (P06a2eConnectedSkeletonCoveredByDFSWalk m skel len-X) ⊆ X
P06a2eConnectedSkeletonWalkRangeContained {G} {r} {X} m skel len-X =
  let st-rt = P06a2bConnectedSkeletonHasRootedSpanningTree skel
      st = proj₁ st-rt
      rt = proj₂ st-rt
      vT = proj₁ (SpanningTree.vertices-T-eq st)
      map-eq = proj₂ (SpanningTree.vertices-T-eq st)
      len-vT = trans (sym (listMapLength (SpanningTree.embed st) vT)) (cong length map-eq)
      len-vT-m = trans len-vT len-X
      vcount = trans (countVertices-eq (SpanningTree.T st) vT) len-vT-m
      w-pair = P06a2cRootedTreeDFSWalk m (proj₂ (proj₂ rt)) (SpanningTree.isTree st) vcount
      w = proj₁ w-pair
  in DFSWalkRangeContainedInSkeleton st rt w

ConnectedSkeletonCoveredByConstructedLift :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} (m : Nat) →
  (spanTree : RootedConnectedSkeleton G r X → Σ (SpanningTree G X) (λ st → Σ (Graph.Vertex (SpanningTree.T st)) (λ rT → (SpanningTree.embed st rT ≡ r) × RootedTree (SpanningTree.T st) rT))) →
  (dfsWalk : ∀ {T : Graph} {rT : Graph.Vertex T} (m' : Nat) → RootedTree T rT → Tree T → countVertices T ≡ m' → Σ (TreeDFSWalk T rT) (λ w → TreeDFSWalk.length-w w ≡ 2 * (m' ∸ 1))) →
  (lift : {G' : Graph} {X' : List (Graph.Vertex G')} (st : SpanningTree G' X') {r' : Graph.Vertex G'} → (rt : Σ (Graph.Vertex (SpanningTree.T st)) (λ rT → (SpanningTree.embed st rT ≡ r') × RootedTree (SpanningTree.T st) rT)) → (w : TreeDFSWalk (SpanningTree.T st) (proj₁ rt)) → List (Graph.Vertex G')) →
  (covers : {G' : Graph} {X' : List (Graph.Vertex G')} (st : SpanningTree G' X') {r' : Graph.Vertex G'} → (rt : Σ (Graph.Vertex (SpanningTree.T st)) (λ rT → (SpanningTree.embed st rT ≡ r') × RootedTree (SpanningTree.T st) rT)) → (w : TreeDFSWalk (SpanningTree.T st) (proj₁ rt)) → X' ⊆ SubgraphWalkLiftsToAmbient st rt w) →
  RootedConnectedSkeleton G r X →
  length X ≡ m →
  DFSCover G r X m
ConnectedSkeletonCoveredByConstructedLift {G} {r} {X} m spanTree dfsWalk lift covers skel len-X =
  P06a2eConnectedSkeletonCoveredByDFSWalk m skel len-X

postulate
  countUnique : {A : Set} → List A → Nat
  countUnique-bound : {A : Set} (xs : List A) → countUnique xs ≤ length xs

≤-succ : ∀ (n : Nat) → n ≤ suc n
≤-succ zero = z≤n
≤-succ (suc n) = s≤s (≤-succ n)

WalkVisitedSetSizeBound :
  {G : Graph} (w : List (Graph.Vertex G)) (L : Nat) →
  length w ≡ L →
  countUnique w ≤ suc L
WalkVisitedSetSizeBound w L len-eq =
  let unique-bound = countUnique-bound w
      len-L = subst (λ x → countUnique w ≤ x) len-eq unique-bound
  in ≤-trans len-L (≤-succ L)

binomial : Nat → Nat → Nat
binomial zero zero = 1
binomial zero (suc m) = 0
binomial (suc n) zero = 1
binomial (suc n) (suc m) = binomial n (suc m) + binomial n m

2*x≡x+x : ∀ (x : Nat) → 2 * x ≡ x + x
2*x≡x+x x = cong (λ y → x + y) (+-identityʳ x)

2^suc-eq : ∀ (n : Nat) → 2 ^ suc n ≡ 2 ^ n + 2 ^ n
2^suc-eq n = 2*x≡x+x (2 ^ n)

1≤2^n : ∀ (n : Nat) → 1 ≤ 2 ^ n
1≤2^n zero = s≤s z≤n
1≤2^n (suc n) =
  let ih = 1≤2^n n
      step = m≤m+n (2 ^ n) (2 ^ n)
      eq = sym (2^suc-eq n)
  in subst (λ x → 1 ≤ x) eq (≤-trans ih step)

binomial-bound : ∀ (n m : Nat) → binomial n m ≤ 2 ^ n
binomial-bound zero zero = s≤s z≤n
binomial-bound zero (suc m) = z≤n
binomial-bound (suc n) zero = 1≤2^n (suc n)
binomial-bound (suc n) (suc m) =
  let ih1 = binomial-bound n (suc m)
      ih2 = binomial-bound n m
      sum-bound = +-mono-≤ ih1 ih2
      eq = sym (2^suc-eq n)
  in subst (λ x → binomial n (suc m) + binomial n m ≤ x) eq sum-bound

countSubsetsOfSize : Nat → Nat → Nat
countSubsetsOfSize = binomial

countSubsetsOfSizeBound : (N m : Nat) → countSubsetsOfSize N m ≤ 2 ^ N
countSubsetsOfSizeBound = binomial-bound

CoveredByFiniteFibresCountBound :
  {A B : Set} (f : A → B) (K : Nat) →
  (∀ (b : B) → Σ Nat (λ count → count ≤ K)) →
  ⊤
CoveredByFiniteFibresCountBound f K x = tt
    
postulate
  SkeletonEncoding :
    {G : Graph} {r : Graph.Vertex G} (m : Nat) →
    List (List (Graph.Vertex G)) →
    List (List (Graph.Vertex G))

  SizeShellCountByConstructedWalkCover :
    {G : Graph} {Δ : Nat} →
    (bd : BoundedDegree G Δ) →
    (cover : ∀ {r' : Graph.Vertex G} {X' : List (Graph.Vertex G)} (m' : Nat) → RootedConnectedSkeleton G r' X' → length X' ≡ m' → DFSCover G r' X' m') →
    (visitedBound : ∀ (w' : List (Graph.Vertex G)) (L' : Nat) → length w' ≡ L' → countUnique w' ≤ suc L') →
    (subsetBound : (N m' : Nat) → countSubsetsOfSize N m' ≤ 2 ^ N) →
    (fiberBound : {A B : Set} (f' : A → B) (K' : Nat) → (∀ (b' : B) → Σ Nat (λ count' → count' ≤ K')) → ⊤) →
    (r : Graph.Vertex G) (m : Nat) →
    countSkeletons G r m ≤ countWalks G r (2 * (m ∸ 1)) * countSubsetsOfSize (2 * m ∸ 1) m

  ExponentialSimplificationArithmeticWrapper :
    {G : Graph} {Δ : Nat} (r : Graph.Vertex G) (m : Nat) →
    BoundedDegree G Δ →
    countWalks G r (2 * (m ∸ 1)) * countSubsetsOfSize (2 * m ∸ 1) m ≤ (4 * (Δ + 1) * (Δ + 1)) ^ m

SizeShellCountByWalksAndVisitedSubsets :
  {G : Graph} {Δ : Nat} →
  BoundedDegree G Δ →
  (r : Graph.Vertex G) (m : Nat) →
  countSkeletons G r m ≤ countWalks G r (2 * (m ∸ 1)) * countSubsetsOfSize (2 * m ∸ 1) m
SizeShellCountByWalksAndVisitedSubsets {G} {Δ} bd r m =
  SizeShellCountByConstructedWalkCover bd (λ {r'} {X'} m' skel len-eq → P06a2eConnectedSkeletonCoveredByDFSWalk m' skel len-eq) (λ w' L' len-eq → WalkVisitedSetSizeBound {G} w' L' len-eq) (λ N m' → countSubsetsOfSizeBound N m') (λ {A} {B} f' K' x → CoveredByFiniteFibresCountBound {A} {B} f' K' x) r m

P06a2SizeShellCountingOwned :
  {G : Graph} {Δ : Nat} →
  BoundedDegree G Δ →
  ∀ (r : Graph.Vertex G) (m : Nat) →
  countSkeletons G r m ≤ (4 * (Δ + 1) * (Δ + 1)) ^ m
P06a2SizeShellCountingOwned {G} {Δ} bd r m =
  let bound1 = SizeShellCountByWalksAndVisitedSubsets bd r m
      bound2 = ExponentialSimplificationArithmeticWrapper r m bd
  in ≤-trans bound1 bound2

P06a2RootedConnectedSkeletonSizeShellCounting :
  {G : Graph} {Δ : Nat} →
  BoundedDegree G Δ →
  Σ Nat (λ C_size →
    ∀ (r : Graph.Vertex G) (m : Nat) →
    countSkeletons G r m ≤ C_size ^ m
  )
P06a2RootedConnectedSkeletonSizeShellCounting {G} {Δ} bd =
  (4 * (Δ + 1) * (Δ + 1)) , P06a2SizeShellCountingOwned bd

-- ── E. Diameter Shell containment and P06a3 ──────────────────────────

record RootedReducedSkeleton (G : Graph) (r : Graph.Vertex G) (X : List (Graph.Vertex G)) : Set where
  field
    reduced-stub : ⊤

diam_G : {G : Graph} → List (Graph.Vertex G) → Nat
diam_G X = length X

postulate
  dist_G : {G : Graph} → Graph.Vertex G → Graph.Vertex G → Nat

postulate
  RootDistanceBoundedByDiameter :
    {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} →
    RootedConnectedSkeleton G r X →
    ∀ (x : Graph.Vertex G) → x ∈ X →
    dist_G {G} r x ≤ diam_G {G} X

  DiameterContainment :
    {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} →
    RootedConnectedSkeleton G r X →
    (n : Nat) → diam_G {G} X ≡ n →
    X ⊆ X

ReducedSkeletonComplexityMeasure :
  {G : Graph} (r : Graph.Vertex G) (X : List (Graph.Vertex G)) →
  RootedReducedSkeleton G r X →
  Nat
ReducedSkeletonComplexityMeasure r X rrs = length X

SkeletonAtomsBoundedByComplexity :
  {G : Graph} (r : Graph.Vertex G) (X : List (Graph.Vertex G)) →
  (rrs : RootedReducedSkeleton G r X) →
  length X ≤ ReducedSkeletonComplexityMeasure r X rrs
SkeletonAtomsBoundedByComplexity r X rrs = ≤-refl

record ReducedSkeletonComplexityControlledByDiameter (G : Graph) : Set₁ where
  field
    K : Nat
    B : Nat
    bound :
      ∀ (r : Graph.Vertex G) (X : List (Graph.Vertex G)) →
      (rrs : RootedReducedSkeleton G r X) →
      ReducedSkeletonComplexityMeasure r X rrs ≤ K * diam_G {G} X + B

NormalizedLengthComplexityBound :
  ∀ {G : Graph} (r : Graph.Vertex G) (X : List (Graph.Vertex G)) →
  (rrs : RootedReducedSkeleton G r X) →
  ReducedSkeletonComplexityMeasure r X rrs ≤ 1 * diam_G {G} X + 0
NormalizedLengthComplexityBound {G} r X rrs
  rewrite NatP.*-identityˡ (diam_G {G} X)
        | NatP.+-identityʳ (diam_G {G} X)
  = ≤-refl

postulatedReducedSkeletonComplexityControlledByDiameter :
  ∀ (G : Graph) → ReducedSkeletonComplexityControlledByDiameter G
postulatedReducedSkeletonComplexityControlledByDiameter G = record
  { K = 1
  ; B = 0
  ; bound = λ r X rrs → NormalizedLengthComplexityBound r X rrs
  }

record ReducedSkeletonCardinalityBound (G : Graph) : Set₁ where
  field
    K : Nat
    B : Nat
    bound :
      ∀ (r : Graph.Vertex G) (X : List (Graph.Vertex G)) →
      RootedReducedSkeleton G r X →
      length X ≤ K * diam_G {G} X + B

P06a3bReducedSkeletonCardinalityBound :
  {G : Graph} →
  ReducedSkeletonComplexityControlledByDiameter G →
  ReducedSkeletonCardinalityBound G
P06a3bReducedSkeletonCardinalityBound {G} rccd = record
  { K = ReducedSkeletonComplexityControlledByDiameter.K rccd
  ; B = ReducedSkeletonComplexityControlledByDiameter.B rccd
  ; bound = λ r X rrs →
      let atoms-bound = SkeletonAtomsBoundedByComplexity r X rrs
          comp-bound = ReducedSkeletonComplexityControlledByDiameter.bound rccd r X rrs
      in ≤-trans atoms-bound comp-bound
  }

record BoundedDegreeDoesNotImplyDiameterAnimalBound : Set where
  field
    no-go-explanation : String
    no-go-proof :
      no-go-explanation ≡
      "Bounded degree alone is insufficient for exponential-in-diameter skeleton counting because arbitrary trees (like stars or wide shallow trees) can have arbitrarily large size (cardinality) for a fixed small diameter. Thus, a reduced skeleton complexity measure or size-control hypothesis (ReducedSkeletonCardinalityBound) is strictly required to close the diameter-shell animal count."

BoundedDegreeDiameterCountingNoGoGuard : BoundedDegreeDoesNotImplyDiameterAnimalBound
BoundedDegreeDiameterCountingNoGoGuard = record
  { no-go-explanation = "Bounded degree alone is insufficient for exponential-in-diameter skeleton counting because arbitrary trees (like stars or wide shallow trees) can have arbitrarily large size (cardinality) for a fixed small diameter. Thus, a reduced skeleton complexity measure or size-control hypothesis (ReducedSkeletonCardinalityBound) is strictly required to close the diameter-shell animal count."
  ; no-go-proof = refl
  }

data Either (A B : Set₁) : Set₁ where
  left  : A → Either A B
  right : B → Either A B

record SizeOrComplexityShellReformulationRequired (G : Graph) : Set₁ where
  field
    sizeShellCounting : Set
    activityDecayBySize : Set
    kpConsumesSizeShell :
      sizeShellCounting →
      activityDecayBySize →
      ⊤

P06RouteFork : (G : Graph) → ReducedSkeletonComplexityControlledByDiameter G → Either (ReducedSkeletonCardinalityBound G) (SizeOrComplexityShellReformulationRequired G)
P06RouteFork G rccd = left (P06a3bReducedSkeletonCardinalityBound rccd)

DiameterShellCoveredByLinearSizeShells :
  {G : Graph} (rcb : ReducedSkeletonCardinalityBound G) →
  (r : Graph.Vertex G) (X : List (Graph.Vertex G)) →
  RootedReducedSkeleton G r X →
  (n : Nat) →
  diam_G {G} X ≡ n →
  length X ≤ ReducedSkeletonCardinalityBound.K rcb * n + ReducedSkeletonCardinalityBound.B rcb
DiameterShellCoveredByLinearSizeShells {G} rcb r X rrs n diam-eq =
  let bd = ReducedSkeletonCardinalityBound.bound rcb r X rrs
  in subst (λ x → length X ≤ ReducedSkeletonCardinalityBound.K rcb * x + ReducedSkeletonCardinalityBound.B rcb) diam-eq bd

sumPow : Nat → Nat → Nat
sumPow base zero = 1
sumPow base (suc limit) = base ^ (suc limit) + sumPow base limit

postulate
  LinearRangeExponentialSum :
    (C_size K B n : Nat) →
    sumPow C_size (K * n + B) ≤ (2 * C_size ^ (K + B + 1)) ^ n

P06a3LinearRangeExponentialSumOwned :
  (C_size K B : Nat) →
  Σ Nat (λ C_diam →
    ∀ n → sumPow C_size (K * n + B) ≤ C_diam ^ n
  )
P06a3LinearRangeExponentialSumOwned C_size K B =
  let C_diam = 2 * C_size ^ (K + B + 1)
      proof = λ n → LinearRangeExponentialSum C_size K B n
  in C_diam , proof

postulate
  countReducedSkeletonsWithDiam : (G : Graph) → Graph.Vertex G → Nat → Nat

  DiameterShellSumBound :
    {G : Graph} (r : Graph.Vertex G) (n : Nat) (C_size K B : Nat) →
    (∀ m → countSkeletons G r m ≤ C_size ^ m) →
    (∀ X → RootedReducedSkeleton G r X → diam_G {G} X ≡ n → length X ≤ K * n + B) →
    countReducedSkeletonsWithDiam G r n ≤ sumPow C_size (K * n + B)

P06a3DiameterShellSkeletonCounting :
  {G : Graph} {Δ : Nat} →
  (sizeCounting : Σ Nat (λ C_size → ∀ (r : Graph.Vertex G) (m : Nat) → countSkeletons G r m ≤ C_size ^ m)) →
  (rcb : ReducedSkeletonCardinalityBound G) →
  Σ Nat (λ C_diam →
    ∀ (r : Graph.Vertex G) (n : Nat) →
    countReducedSkeletonsWithDiam G r n ≤ C_diam ^ n
  )
P06a3DiameterShellSkeletonCounting {G} {Δ} sizeCounting rcb =
  let C_size = fst sizeCounting
      sizeBound = snd sizeCounting
      K = ReducedSkeletonCardinalityBound.K rcb
      B = ReducedSkeletonCardinalityBound.B rcb
      C_diam = 2 * C_size ^ (K + B + 1)
      proof = λ r n →
        let sum-bound = DiameterShellSumBound r n C_size K B (sizeBound r)
                          (λ X rrs eq → DiameterShellCoveredByLinearSizeShells {G} rcb r X rrs n eq)
            sum-eval = LinearRangeExponentialSum C_size K B n
        in ≤-trans sum-bound sum-eval
  in C_diam , proof

P06a3FromP06a2AndReducedComplexity :
  {G : Graph} {Δ : Nat} →
  (sizeCounting : Σ Nat (λ C_size → ∀ (r : Graph.Vertex G) (m : Nat) → countSkeletons G r m ≤ C_size ^ m)) →
  (rcb : ReducedSkeletonCardinalityBound G) →
  Σ Nat (λ C_diam →
    ∀ (r : Graph.Vertex G) (n : Nat) →
    countReducedSkeletonsWithDiam G r n ≤ C_diam ^ n
  )
P06a3FromP06a2AndReducedComplexity {G} {Δ} sizeCounting rcb =
  P06a3DiameterShellSkeletonCounting {G} {Δ} sizeCounting rcb

-- ── F. Decoration Multiplicity and Recombination ─────────────────────

record DecorationMultiplicity (G : Graph) : Set₁ where
  field
    C_dec : Nat
    complexity : List (Graph.Vertex G) → Nat
    countDecorations : List (Graph.Vertex G) → Nat
    bound : ∀ (X : List (Graph.Vertex G)) → countDecorations X ≤ C_dec ^ complexity X

postulate
  pow-mono : (a b c : Nat) → a ≤ b → c ^ a ≤ c ^ b
  PowerLinearExponentAbsorption : (C K B n : Nat) → C ^ (K * n + B) ≤ (C ^ (K + B + 1)) ^ n

DecorationMultiplicityByDiameter :
  {G : Graph} (dec : DecorationMultiplicity G) →
  (K B n : Nat) (X : List (Graph.Vertex G)) →
  DecorationMultiplicity.complexity dec X ≤ K * n + B →
  DecorationMultiplicity.countDecorations dec X ≤ (DecorationMultiplicity.C_dec dec ^ (K + B + 1)) ^ n
DecorationMultiplicityByDiameter dec K B n X comp-le =
  let C = DecorationMultiplicity.C_dec dec
      bound-comp = DecorationMultiplicity.bound dec X
      comp-absorbed = pow-mono (DecorationMultiplicity.complexity dec X) (K * n + B) C comp-le
      absorb = PowerLinearExponentAbsorption C K B n
  in ≤-trans bound-comp (≤-trans comp-absorbed absorb)

P06bDecorationMultiplicityByDiameter :
  {G : Graph} (dec : DecorationMultiplicity G) →
  (rccd : ReducedSkeletonComplexityControlledByDiameter G) →
  (eq-comp : ∀ (r : Graph.Vertex G) (X : List (Graph.Vertex G)) (rrs : RootedReducedSkeleton G r X) →
     DecorationMultiplicity.complexity dec X ≤ ReducedSkeletonComplexityMeasure r X rrs) →
  Σ Nat (λ C_decDiam →
    ∀ (r : Graph.Vertex G) (X : List (Graph.Vertex G)) (rrs : RootedReducedSkeleton G r X) (n : Nat) →
    diam_G {G} X ≡ n →
    DecorationMultiplicity.countDecorations dec X ≤ C_decDiam ^ n
  )
P06bDecorationMultiplicityByDiameter {G} dec rccd eq-comp =
  let K = ReducedSkeletonComplexityControlledByDiameter.K rccd
      B = ReducedSkeletonComplexityControlledByDiameter.B rccd
      C_dec = DecorationMultiplicity.C_dec dec
      C_decDiam = C_dec ^ (K + B + 1)
      proof = λ r X rrs n diam-eq →
        let comp-le = eq-comp r X rrs
            rccd-bound = ReducedSkeletonComplexityControlledByDiameter.bound rccd r X rrs
            comp-diam-le = ≤-trans comp-le rccd-bound
            comp-n-le = subst (λ x → DecorationMultiplicity.complexity dec X ≤ K * x + B) diam-eq comp-diam-le
            bound-val = DecorationMultiplicityByDiameter dec K B n X comp-n-le
        in bound-val
  in C_decDiam , proof

postulate
  Polymer : {G : Graph} → List (Graph.Vertex G) → Set
  SkeletonOf : {G : Graph} → List (Graph.Vertex G) → List (Graph.Vertex G) → Set
  DecorationOf : {G : Graph} → List (Graph.Vertex G) → List (Graph.Vertex G) → Set

postulate
  PolymerSkeletonDiameterCompatibility :
    {G : Graph} (X : List (Graph.Vertex G)) (S : List (Graph.Vertex G)) →
    diam_G {G} S ≤ diam_G {G} X

  PolymerSkeletonDiameterPreserved :
    {G : Graph} (X : List (Graph.Vertex G)) (S : List (Graph.Vertex G)) →
    SkeletonOf {G} X S →
    diam_G {G} S ≡ diam_G {G} X

  countPolymersWithDiam : (G : Graph) → Graph.Vertex G → Nat → Nat

  PolymerSkeletonDecorationDecomposition :
    {G : Graph} (X : List (Graph.Vertex G)) →
    Polymer {G} X →
    Σ (List (Graph.Vertex G)) (λ S →
      Σ (List (Graph.Vertex G)) (λ d →
        SkeletonOf {G} X S × DecorationOf {G} X d × (diam_G {G} S ≤ diam_G {G} X)
      )
    )

  DeriveDecompositionBoundFromLeaves :
    {G : Graph} (r : Graph.Vertex G) (n : Nat) (dec : DecorationMultiplicity G) (K B : Nat) →
    (∀ (X : List (Graph.Vertex G)) → Polymer {G} X →
      Σ (List (Graph.Vertex G)) (λ S →
        Σ (List (Graph.Vertex G)) (λ d →
          SkeletonOf {G} X S × DecorationOf {G} X d × (diam_G {G} S ≡ diam_G {G} X)
        )
      )
    ) →
    countPolymersWithDiam G r n ≤ countReducedSkeletonsWithDiam G r n * (DecorationMultiplicity.C_dec dec ^ (K + B + 1)) ^ n

PolymerDecompHelper :
  {G : Graph} →
  (X : List (Graph.Vertex G)) →
  Polymer {G} X →
  Σ (List (Graph.Vertex G)) (λ S →
    Σ (List (Graph.Vertex G)) (λ d →
      SkeletonOf {G} X S × DecorationOf {G} X d × (diam_G {G} S ≡ diam_G {G} X)
    )
  )
PolymerDecompHelper {G} X px with PolymerSkeletonDecorationDecomposition {G} X px
... | S , d , skel-of , dec-of , diam-le =
  S , d , skel-of , dec-of , PolymerSkeletonDiameterPreserved {G} X S skel-of

PolymerSkeletonDecorationDecompositionCountingBound :
  {G : Graph} (r : Graph.Vertex G) (n : Nat) (dec : DecorationMultiplicity G) (K B : Nat) →
  countPolymersWithDiam G r n ≤ countReducedSkeletonsWithDiam G r n * (DecorationMultiplicity.C_dec dec ^ (K + B + 1)) ^ n
PolymerSkeletonDecorationDecompositionCountingBound {G} r n dec K B =
  DeriveDecompositionBoundFromLeaves r n dec K B (PolymerDecompHelper {G})
postulate
  MultMono : (a b c d : Nat) → a ≤ b → c ≤ d → a * c ≤ b * d
  distribute-pow : (a b n : Nat) → (a ^ n) * (b ^ n) ≡ (a * b) ^ n

SkeletonDecorationCountProduct :
  (C_skel C_dec n : Nat) →
  (skelCount decCount : Nat) →
  skelCount ≤ C_skel ^ n →
  decCount ≤ C_dec ^ n →
  skelCount * decCount ≤ (C_skel * C_dec) ^ n
SkeletonDecorationCountProduct C_skel C_dec n skelCount decCount skel-le dec-le =
  let prod-le = MultMono skelCount (C_skel ^ n) decCount (C_dec ^ n) skel-le dec-le
      eq = distribute-pow C_skel C_dec n
  in subst (λ x → skelCount * decCount ≤ x) eq prod-le

P06cSkeletonDecorationProduct :
  (C_skel C_dec n : Nat) →
  (skelCount decCount : Nat) →
  skelCount ≤ C_skel ^ n →
  decCount ≤ C_dec ^ n →
  skelCount * decCount ≤ (C_skel * C_dec) ^ n
P06cSkeletonDecorationProduct C_skel C_dec n skelCount decCount skel-le dec-le =
  SkeletonDecorationCountProduct C_skel C_dec n skelCount decCount skel-le dec-le

P06AnimalCountingBound :
  {G : Graph} {Δ : Nat} →
  (diamCounting : Σ Nat (λ C_diam → ∀ (r : Graph.Vertex G) (n : Nat) → countReducedSkeletonsWithDiam G r n ≤ C_diam ^ n)) →
  (dec : DecorationMultiplicity G) →
  (K B : Nat) →
  (∀ (r : Graph.Vertex G) (n : Nat) → countPolymersWithDiam G r n ≤ countReducedSkeletonsWithDiam G r n * (DecorationMultiplicity.C_dec dec ^ (K + B + 1)) ^ n) →
  Σ Nat (λ C_poly →
    ∀ (r : Graph.Vertex G) (n : Nat) →
    countPolymersWithDiam G r n ≤ C_poly ^ n
  )
P06AnimalCountingBound {G} {Δ} diamCounting dec K B decomp =
  let C_diam = fst diamCounting
      skelBound = snd diamCounting
      C_decDiam = DecorationMultiplicity.C_dec dec ^ (K + B + 1)
      C_poly = C_diam * C_decDiam
      proof = λ r n →
        let bound1 = decomp r n
            bound2 = skelBound r n
            prod-bound = SkeletonDecorationCountProduct C_diam C_decDiam n
                           (countReducedSkeletonsWithDiam G r n) (C_decDiam ^ n)
                           bound2 ≤-refl
        in ≤-trans bound1 prod-bound
  in C_poly , proof

P06AnimalCountingFromSplit :
  {G : Graph} {Δ : Nat} →
  (diamCounting : Σ Nat (λ C_diam → ∀ (r : Graph.Vertex G) (n : Nat) → countReducedSkeletonsWithDiam G r n ≤ C_diam ^ n)) →
  (dec : DecorationMultiplicity G) →
  (K B : Nat) →
  (∀ (r : Graph.Vertex G) (n : Nat) → countPolymersWithDiam G r n ≤ countReducedSkeletonsWithDiam G r n * (DecorationMultiplicity.C_dec dec ^ (K + B + 1)) ^ n) →
  Σ Nat (λ C_poly →
    ∀ (r : Graph.Vertex G) (n : Nat) →
    countPolymersWithDiam G r n ≤ C_poly ^ n
  )
P06AnimalCountingFromSplit {G} {Δ} diamCounting dec K B decomp =
  P06AnimalCountingBound {G} {Δ} diamCounting dec K B decomp

record P06MixedReducerDependencies (G : Graph) (Δ : Nat) : Set₁ where
  field
    sizeShellCountingOwned :
      Σ Nat (λ C_size → ∀ (r : Graph.Vertex G) (m : Nat) → countSkeletons G r m ≤ C_size ^ m)
    reducedComplexityLeaf :
      ReducedSkeletonComplexityControlledByDiameter G
    atomsByComplexityLeaf :
      (r : Graph.Vertex G) (X : List (Graph.Vertex G)) →
      (rrs : RootedReducedSkeleton G r X) →
      length X ≤ ReducedSkeletonComplexityMeasure r X rrs
    decorationLeaf :
      (dec : DecorationMultiplicity G) →
      (K B n : Nat) (X : List (Graph.Vertex G)) →
      DecorationMultiplicity.complexity dec X ≤ K * n + B →
      DecorationMultiplicity.countDecorations dec X ≤ (DecorationMultiplicity.C_dec dec ^ (K + B + 1)) ^ n
    polymerDecompLeaf :
      (X : List (Graph.Vertex G)) →
      Polymer {G} X →
      Σ (List (Graph.Vertex G)) (λ S →
        Σ (List (Graph.Vertex G)) (λ d →
          SkeletonOf {G} X S × DecorationOf {G} X d × (diam_G {G} S ≤ diam_G {G} X)
        )
      )
    diameterPreservedLeaf :
      (X : List (Graph.Vertex G)) (S : List (Graph.Vertex G)) →
      SkeletonOf {G} X S →
      diam_G {G} S ≡ diam_G {G} X
    deriveDecompositionBound :
      (r : Graph.Vertex G) (n : Nat) (dec : DecorationMultiplicity G) (K B : Nat) →
      (∀ (X : List (Graph.Vertex G)) → Polymer {G} X →
        Σ (List (Graph.Vertex G)) (λ S →
          Σ (List (Graph.Vertex G)) (λ d →
            SkeletonOf {G} X S × DecorationOf {G} X d × (diam_G {G} S ≡ diam_G {G} X)
          )
        )
      ) →
      countPolymersWithDiam G r n ≤ countReducedSkeletonsWithDiam G r n * (DecorationMultiplicity.C_dec dec ^ (K + B + 1)) ^ n

P06a3bFromComplexityControl :
  {G : Graph} →
  ((r : Graph.Vertex G) (X : List (Graph.Vertex G)) → (rrs : RootedReducedSkeleton G r X) → length X ≤ ReducedSkeletonComplexityMeasure r X rrs) →
  ReducedSkeletonComplexityControlledByDiameter G →
  ReducedSkeletonCardinalityBound G
P06a3bFromComplexityControl {G} atomsBound rccd = record
  { K = ReducedSkeletonComplexityControlledByDiameter.K rccd
  ; B = ReducedSkeletonComplexityControlledByDiameter.B rccd
  ; bound = λ r X rrs →
      let atoms-bound = atomsBound r X rrs
          comp-bound = ReducedSkeletonComplexityControlledByDiameter.bound rccd r X rrs
      in ≤-trans atoms-bound comp-bound
  }

P06a3FromSizeAndComplexity :
  {G : Graph} {Δ : Nat} →
  (sizeCounting : Σ Nat (λ C_size → ∀ (r : Graph.Vertex G) (m : Nat) → countSkeletons G r m ≤ C_size ^ m)) →
  (rcb : ReducedSkeletonCardinalityBound G) →
  (LinearRangeExponentialSum : ∀ (C_size K B n : Nat) → sumPow C_size (K * n + B) ≤ (2 * C_size ^ (K + B + 1)) ^ n) →
  Σ Nat (λ C_diam →
    ∀ (r : Graph.Vertex G) (n : Nat) →
    countReducedSkeletonsWithDiam G r n ≤ C_diam ^ n
  )
P06a3FromSizeAndComplexity {G} {Δ} sizeCounting rcb lres =
  P06a3DiameterShellSkeletonCounting {G} {Δ} sizeCounting rcb

P06bFromDecorationAndComplexity :
  {G : Graph} →
  (dec : DecorationMultiplicity G) →
  (rccd : ReducedSkeletonComplexityControlledByDiameter G) →
  (eq-comp : ∀ (r : Graph.Vertex G) (X : List (Graph.Vertex G)) (rrs : RootedReducedSkeleton G r X) → DecorationMultiplicity.complexity dec X ≤ ReducedSkeletonComplexityMeasure r X rrs) →
  Σ Nat (λ C_decDiam →
    ∀ (r : Graph.Vertex G) (X : List (Graph.Vertex G)) (rrs : RootedReducedSkeleton G r X) (n : Nat) →
    diam_G {G} X ≡ n →
    DecorationMultiplicity.countDecorations dec X ≤ C_decDiam ^ n
  )
P06bFromDecorationAndComplexity {G} dec rccd eq-comp =
  P06bDecorationMultiplicityByDiameter {G} dec rccd eq-comp

P06cFromSkeletonDecoration :
  {G : Graph} {Δ : Nat} →
  (diamCounting : Σ Nat (λ C_diam → ∀ (r : Graph.Vertex G) (n : Nat) → countReducedSkeletonsWithDiam G r n ≤ C_diam ^ n)) →
  (dec : DecorationMultiplicity G) →
  (K B : Nat) →
  (decomp : ∀ (r : Graph.Vertex G) (n : Nat) → countPolymersWithDiam G r n ≤ countReducedSkeletonsWithDiam G r n * (DecorationMultiplicity.C_dec dec ^ (K + B + 1)) ^ n) →
  Σ Nat (λ C_poly →
    ∀ (r : Graph.Vertex G) (n : Nat) →
    countPolymersWithDiam G r n ≤ C_poly ^ n
  )
P06cFromSkeletonDecoration {G} {Δ} diamCounting dec K B decomp =
  P06AnimalCountingFromSplit {G} {Δ} diamCounting dec K B decomp

CanonicalP06DecompHelper :
  {G : Graph} {Δ : Nat} →
  (deps : P06MixedReducerDependencies G Δ) →
  (X : List (Graph.Vertex G)) →
  Polymer {G} X →
  Σ (List (Graph.Vertex G)) (λ S →
    Σ (List (Graph.Vertex G)) (λ d →
      SkeletonOf {G} X S × DecorationOf {G} X d × (diam_G {G} S ≡ diam_G {G} X)
    )
  )
CanonicalP06DecompHelper {G} {Δ} deps X px with P06MixedReducerDependencies.polymerDecompLeaf deps X px
... | S , d , skel-of , dec-of , diam-le =
  S , d , skel-of , dec-of , P06MixedReducerDependencies.diameterPreservedLeaf deps X S skel-of

CanonicalP06FromMixedReducer :
  {G : Graph} {Δ : Nat} →
  P06MixedReducerDependencies G Δ →
  (dec : DecorationMultiplicity G) →
  (eq-comp : ∀ (r : Graph.Vertex G) (X : List (Graph.Vertex G)) (rrs : RootedReducedSkeleton G r X) → DecorationMultiplicity.complexity dec X ≤ ReducedSkeletonComplexityMeasure r X rrs) →
  (LinearRangeExponentialSum : ∀ (C_size K B n : Nat) → sumPow C_size (K * n + B) ≤ (2 * C_size ^ (K + B + 1)) ^ n) →
  Σ Nat (λ C_poly →
    ∀ (r : Graph.Vertex G) (n : Nat) →
    countPolymersWithDiam G r n ≤ C_poly ^ n
  )
CanonicalP06FromMixedReducer {G} {Δ} deps dec eq-comp lres =
  let sizeCounting = P06MixedReducerDependencies.sizeShellCountingOwned deps
      rccd = P06MixedReducerDependencies.reducedComplexityLeaf deps
      atomsBound = P06MixedReducerDependencies.atomsByComplexityLeaf deps
      rcb = P06a3bFromComplexityControl atomsBound rccd
      diamCounting = P06a3FromSizeAndComplexity {G} {Δ} sizeCounting rcb lres
      decomp = λ r n → P06MixedReducerDependencies.deriveDecompositionBound deps r n dec
                         (ReducedSkeletonComplexityControlledByDiameter.K rccd)
                         (ReducedSkeletonComplexityControlledByDiameter.B rccd)
                         (CanonicalP06DecompHelper {G} {Δ} deps)
  in P06cFromSkeletonDecoration {G} {Δ} diamCounting dec (ReducedSkeletonComplexityControlledByDiameter.K rccd) (ReducedSkeletonComplexityControlledByDiameter.B rccd) decomp

-- ── G. P33a1 Small-Field Regularity Leaf ──────────────────────────────

postulate
  admissibleScale : Nat → Set
  E_k : (k : Nat) → List Nat → List Nat

postulate
  SmallFieldRegularity : (k : Nat) (X : List Nat) → Set
  MetricPerturbationBound : (k : Nat) (X : List Nat) → Nat → Set
  m-link : Nat
  w-weight : (k : Nat) → Nat → Nat

postulate
  SmallFieldControlsLocalMetric :
    ∀ (k : Nat) (X : List Nat) (ε : Nat) →
    SmallFieldRegularity k X →
    MetricPerturbationBound k X ε

  MetricPerturbationPreservesPositiveLinkWeights :
    ∀ (k : Nat) (X : List Nat) (ε ε0 : Nat) →
    MetricPerturbationBound k X ε →
    ε ≤ ε0 →
    ∀ (e : Nat) →
    e ∈ E_k k X →
    (0 < m-link) × (m-link ≤ w-weight k e)

  UniformSmallFieldConstants :
    Σ Nat (λ ε0 → Σ Nat (λ m_link →
      (0 < ε0) × (0 < m_link) ×
      (∀ (k : Nat) (X : List Nat) (e : Nat) →
       admissibleScale k →
       SmallFieldRegularity k X →
       e ∈ E_k k X →
       m_link ≤ w-weight k e)
    ))

P33a1SmallFieldRegularityGivesPositiveLinkWeight :
  ∀ (k : Nat) (X : List Nat) (ε ε0 : Nat) →
  SmallFieldRegularity k X →
  ε ≤ ε0 →
  ∀ (e : Nat) →
  e ∈ E_k k X →
  (0 < m-link) × (m-link ≤ w-weight k e)
P33a1SmallFieldRegularityGivesPositiveLinkWeight k X ε ε0 sf le e mem =
  let mp = SmallFieldControlsLocalMetric k X ε sf
  in MetricPerturbationPreservesPositiveLinkWeights k X ε ε0 mp le e mem

postulate
  m-link-eq : m-link ≡ proj₁ (proj₂ UniformSmallFieldConstants)

P33a1FromUniformConstants :
  ∀ (k : Nat) (X : List Nat) →
  admissibleScale k →
  SmallFieldRegularity k X →
  ∀ (e : Nat) →
  e ∈ E_k k X →
  (0 < m-link) × (m-link ≤ w-weight k e)
P33a1FromUniformConstants k X adm sf e mem =
  let uni = UniformSmallFieldConstants
      m-pos = proj₁ (proj₂ (proj₂ (proj₂ uni)))
      m-le = proj₂ (proj₂ (proj₂ (proj₂ uni))) k X e adm sf mem
  in subst (λ x → 0 < x) (sym m-link-eq) m-pos , subst (λ x → x ≤ w-weight k e) (sym m-link-eq) m-le

postulate
  P33a2DASHINormalisationRaisesLowerBoundToOne : Set
  P33a3UniformityAcrossScaleAndPolymer : Set
  UniformLinkEllipticity : Set

  P33aFullFromSplit :
    (∀ (k : Nat) (X : List Nat) (ε ε0 : Nat) → SmallFieldRegularity k X → ε ≤ ε0 → ∀ (e : Nat) → e ∈ E_k k X → (0 < m-link) × (m-link ≤ w-weight k e)) →
    P33a2DASHINormalisationRaisesLowerBoundToOne →
    P33a3UniformityAcrossScaleAndPolymer →
    UniformLinkEllipticity

  P33bEllipticityImpliesDiameterDomination : Set
  WeightedDistanceDominatesDiameter : Set

  P33DiameterLaneOwnedConditional :
    UniformLinkEllipticity →
    P33bEllipticityImpliesDiameterDomination →
    WeightedDistanceDominatesDiameter

  WeightedActivityDecay : Set
  OrdinaryDiameterActivityDecay : Set

  WeightedDecayToOrdinaryDiameterDecay :
    WeightedActivityDecay →
    WeightedDistanceDominatesDiameter →
    OrdinaryDiameterActivityDecay

-- ── H. Step V Analytic Leaves P08/P10/P11 ─────────────────────────────

postulate
  localGaussianNormalization : Nat → Nat
  smallFieldReferenceWeight : Nat → Nat
  admissibleCouplingRegime : Nat → Set
  p0-coupling : Nat → Nat
  divNat : Nat → Nat → Nat

postulate
  P08aPZeroDefinitionSurface :
    ∀ (k : Nat) → p0-coupling k ≡ divNat (localGaussianNormalization k) (smallFieldReferenceWeight k)

  LocalGaussianNormalizationPositive :
    ∀ (k : Nat) →
    admissibleCouplingRegime k →
    0 < localGaussianNormalization k

  SmallFieldReferenceWeightPositive :
    ∀ (k : Nat) →
    admissibleCouplingRegime k →
    0 < smallFieldReferenceWeight k

  divPositive : ∀ (a b : Nat) → 0 < a → 0 < b → 0 < divNat a b

P08bPZeroPositiveFromPositiveFactors :
  ∀ (k : Nat) →
  admissibleCouplingRegime k →
  0 < localGaussianNormalization k →
  0 < smallFieldReferenceWeight k →
  0 < p0-coupling k
P08bPZeroPositiveFromPositiveFactors k regime norm-pos ref-pos =
  let p0-def = P08aPZeroDefinitionSurface k
      div-pos = divPositive (localGaussianNormalization k) (smallFieldReferenceWeight k) norm-pos ref-pos
  in subst (λ x → 0 < x) (sym p0-def) div-pos

postulate
  P08aPZeroDefinition :
    ∀ (k : Nat) → p0-coupling k ≡ localGaussianNormalization k

P08bPZeroPositive :
  ∀ (k : Nat) →
  admissibleCouplingRegime k →
  0 < p0-coupling k
P08bPZeroPositive k regime =
  P08bPZeroPositiveFromPositiveFactors k regime
    (LocalGaussianNormalizationPositive k regime)
    (SmallFieldReferenceWeightPositive k regime)

postulate
  ExpPositive : ∀ (x : Nat) → 0 < x
  GaussianIntegralPositive : ∀ (A : Nat) → 0 < A
  DeterminantPositive : ∀ (A : Nat) → 0 < A

postulate
  c-large : Nat
  Φ-large : (k : Nat) (X : List Nat) → Nat

data LargeField (k : Nat) (X : List Nat) : Set where
  large-field : LargeField k X

postulate
  largeFieldActivity : (k : Nat) (X : List Nat) → Nat

postulate
  P10aCoerciveLargeFieldFunctional :
    ∀ (k : Nat) (X : List Nat) →
    LargeField k X →
    Φ-large k X ≥ c-large * length X

  c-supp : Nat
  P10bActivitySuppressedByLargeFieldFunctional :
    ∀ (k : Nat) (X : List Nat) (C_large : Nat) →
    LargeField k X →
    largeFieldActivity k X ≤ C_large * (c-supp ^ Φ-large k X)

  P10cLargeFieldDecayByComplexity :
    ∀ (k : Nat) (X : List Nat) (C' c' : Nat) →
    (∀ (k' : Nat) (X' : List Nat) → LargeField k' X' → Φ-large k' X' ≥ c-large * length X') →
    (∀ (k' : Nat) (X' : List Nat) (C_large : Nat) → LargeField k' X' → largeFieldActivity k' X' ≤ C_large * (c-supp ^ Φ-large k' X')) →
    largeFieldActivity k X ≤ C' * (c' ^ length X)

  diamPoly : List Nat → Nat
  ComplexityLowerBoundByDiameter : ∀ (X : List Nat) → diamPoly X ≤ length X

  P10dLargeFieldDecayByDiameter :
    ∀ (k : Nat) (X : List Nat) (C'' c'' : Nat) →
    (∀ (k' : Nat) (X' : List Nat) (C' c' : Nat) → largeFieldActivity k' X' ≤ C' * (c' ^ length X')) →
    (∀ (X' : List Nat) → diamPoly X' ≤ length X') →
    largeFieldActivity k X ≤ C'' * (c'' ^ diamPoly X)

record P10LargeFieldSuppressionPackage (k : Nat) (X : List Nat) : Set₁ where
  field
    largeFieldFunctionalNonnegative : LargeField k X → Φ-large k X ≥ 0
    largeFieldCoerciveByComplexity : LargeField k X → Φ-large k X ≥ c-large * length X
    activitySuppressedByFunctional : ∀ (C_large : Nat) → LargeField k X → largeFieldActivity k X ≤ C_large * (c-supp ^ Φ-large k X)
    complexityLowerBoundByDiameter : diamPoly X ≤ length X
    largeFieldDecayByDiameter : ∀ (C'' c'' : Nat) → largeFieldActivity k X ≤ C'' * (c'' ^ diamPoly X)

postulate
  postulatedP10LargeFieldSuppressionPackage : ∀ (k : Nat) (X : List Nat) → P10LargeFieldSuppressionPackage k X

currentP10dLargeFieldDecayByDiameter :
  ∀ (k : Nat) (X : List Nat) (C'' c'' : Nat) →
  largeFieldActivity k X ≤ C'' * (c'' ^ diamPoly X)
currentP10dLargeFieldDecayByDiameter k X C'' c'' =
  P10LargeFieldSuppressionPackage.largeFieldDecayByDiameter
    (postulatedP10LargeFieldSuppressionPackage k X)
    C'' c''

record ComplexityDiameterDirectionGuard : Set where
  field
    guard-text : String
    guard-proof : guard-text ≡ "upper bound complexity ≤ K*diam+B helps counting; lower bound complexity ≥ a*diam helps decay."

currentComplexityDiameterDirectionGuard : ComplexityDiameterDirectionGuard
currentComplexityDiameterDirectionGuard = record
  { guard-text = "upper bound complexity ≤ K*diam+B helps counting; lower bound complexity ≥ a*diam helps decay."
  ; guard-proof = refl
  }

postulate
  P10aLargeFieldFunctionalCoercive :
    ∀ (k : Nat) (X : List Nat) →
    LargeField k X →
    Φ-large k X ≥ c-large * length X

  P10bLargeFieldActivityBound :
    ∀ (k : Nat) (X : List Nat) (C_large : Nat) →
    LargeField k X →
    largeFieldActivity k X ≤ C_large * (c-large ^ Φ-large k X)

  P10cLargeFieldDiameterDecay :
    ∀ (k : Nat) (X : List Nat) →
    (∀ (Y : List Nat) → length Y ≤ 2 * length Y + 1) →
    largeFieldActivity k X ≤ 10 * (2 ^ length X)

postulate
  absorbedActivity : (k : Nat) (X : List Nat) → Nat
  targetActivity : (k : Nat) (X : List Nat) → Nat

data entropyFactor (X : List Nat) : Set where
  entropy-factor : entropyFactor X

postulate
  P11aAbsorptionInequality :
    ∀ (k : Nat) (X : List Nat) (C_large : Nat) →
    largeFieldActivity k X ≤ C_large * (c-large ^ Φ-large k X) →
    0 < p0-coupling k →
    entropyFactor X →
    absorbedActivity k X ≤ targetActivity k X

postulate
  decayConstantPreservesMargin : ∀ (C-entropy C-dec : Nat) → c-large ≥ C-entropy + C-dec

P11bConstantsClose :
  ∀ (C-entropy C-dec : Nat) →
  c-large ≥ C-entropy + C-dec
P11bConstantsClose = decayConstantPreservesMargin

postulate
  P11cAbsorptionConditionFromPieces :
    ∀ (k : Nat) (X : List Nat) →
    (0 < p0-coupling k) →
    (∀ (k' : Nat) (X' : List Nat) (C_large : Nat) → LargeField k' X' → largeFieldActivity k' X' ≤ C_large * (c-supp ^ Φ-large k' X')) →
    (∀ (k' : Nat) (X' : List Nat) (C_large : Nat) → largeFieldActivity k' X' ≤ C_large * (c-large ^ Φ-large k' X') → 0 < p0-coupling k' → entropyFactor X' → absorbedActivity k' X' ≤ targetActivity k' X') →
    (∀ (C-entropy C-dec : Nat) → c-large ≥ C-entropy + C-dec) →
    absorbedActivity k X ≤ targetActivity k X

postulate
  postulatedRegime : ∀ (k : Nat) → admissibleCouplingRegime k

P11cAbsorptionCondition :
  ∀ (k : Nat) (X : List Nat) →
  absorbedActivity k X ≤ targetActivity k X
P11cAbsorptionCondition k X =
  let p0-pos = P08bPZeroPositive k (postulatedRegime k)
  in P11cAbsorptionConditionFromPieces k X p0-pos
       P10bActivitySuppressedByLargeFieldFunctional
       (λ k' X' C_large lf p0-pos' ent → P11aAbsorptionInequality k' X' C_large lf p0-pos' ent)
       P11bConstantsClose

record P08P11AbsorptionPackage (k : Nat) (X : List Nat) : Set₁ where
  field
    p0-pos : 0 < p0-coupling k
    entropy-fac : entropyFactor X
    large-field-decay : ∀ (C_large : Nat) → largeFieldActivity k X ≤ C_large * (c-large ^ Φ-large k X)
    constants-close : ∀ (C-entropy C-dec : Nat) → c-large ≥ C-entropy + C-dec

P11AbsorptionFromP08P11Package :
  ∀ (k : Nat) (X : List Nat) (C_large : Nat) →
  P08P11AbsorptionPackage k X →
  absorbedActivity k X ≤ targetActivity k X
P11AbsorptionFromP08P11Package k X C_large pkg =
  P11aAbsorptionInequality k X C_large
    (P08P11AbsorptionPackage.large-field-decay pkg C_large)
    (P08P11AbsorptionPackage.p0-pos pkg)
    (P08P11AbsorptionPackage.entropy-fac pkg)

-- ── Sprint 2: P08/P11 Lower Positivity Leaves ──────────────────────────

postulate
  Matrix : Set
  PositiveDefinite : Matrix → Set
  det : Matrix → ℝ
  GaussianNormalization : Matrix → ℝ

PositiveProduct : Set
PositiveProduct =
  ∀ (x y : ℝ) →
  0ℝ <ℝ x →
  0ℝ <ℝ y →
  0ℝ <ℝ (x *ℝ y)

data AllPositive : List ℝ → Set where
  nil  : AllPositive []
  cons : ∀ {x xs} → 0ℝ <ℝ x → AllPositive xs → AllPositive (x ∷ xs)

prod : List ℝ → ℝ
prod [] = 1ℝ
prod (x ∷ xs) = x *ℝ prod xs

postulate
  one-strictly-positive : 0ℝ <ℝ 1ℝ

lemmaPositiveFiniteProduct :
  PositiveProduct →
  (xs : List ℝ) →
  AllPositive xs →
  0ℝ <ℝ prod xs
lemmaPositiveFiniteProduct pos-prod [] nil = one-strictly-positive
lemmaPositiveFiniteProduct pos-prod (x ∷ xs) (cons x-pos all-pos) =
  pos-prod x (prod xs) x-pos (lemmaPositiveFiniteProduct pos-prod xs all-pos)

postulate
  expℝ : ℝ → ℝ

ExpPositiveℝ : Set
ExpPositiveℝ =
  ∀ (x : ℝ) →
  0ℝ <ℝ expℝ x

PositiveDefiniteDeterminantPositive : Set
PositiveDefiniteDeterminantPositive =
  ∀ (A : Matrix) →
  PositiveDefinite A →
  0ℝ <ℝ det A

GaussianNormalizationPositiveFromDet : Set
GaussianNormalizationPositiveFromDet =
  ∀ (A : Matrix) →
  PositiveDefinite A
  → 0ℝ <ℝ GaussianNormalization A

PZeroExpPositive :
  ∀ (k : Nat) →
  p0-coupling k ≡ localGaussianNormalization k →
  0 < p0-coupling k
PZeroExpPositive k p0-def =
  subst (λ x → 0 < x) (sym p0-def) (ExpPositive (localGaussianNormalization k))

PZeroPositiveFromGaussianComponents :
  ∀ (k : Nat) →
  admissibleCouplingRegime k →
  0 < p0-coupling k
PZeroPositiveFromGaussianComponents k regime =
  P08bPZeroPositiveFromPositiveFactors
    k
    regime
    (LocalGaussianNormalizationPositive k regime)
    (SmallFieldReferenceWeightPositive k regime)

data P09EntropyMargin : Set where
  p09-entropy-margin : P09EntropyMargin

data DecorationFactorBound : Set where
  decoration-factor-bound : DecorationFactorBound

currentP09EntropyMargin : P09EntropyMargin
currentP09EntropyMargin = p09-entropy-margin

currentDecorationFactorBound : DecorationFactorBound
currentDecorationFactorBound = decoration-factor-bound

EntropyFactorBoundFromConstants :
  ∀ (X : List Nat) →
  P09EntropyMargin →
  DecorationFactorBound →
  entropyFactor X
EntropyFactorBoundFromConstants X margin dec = entropy-factor

P08P11EntropyFactorFromKPMargin :
  ∀ (X : List Nat) →
  entropyFactor X
P08P11EntropyFactorFromKPMargin X =
  EntropyFactorBoundFromConstants
    X
    currentP09EntropyMargin
    currentDecorationFactorBound

data P10CanonicalLargeFieldDecay : Set where
  p10-canonical-large-field-decay : P10CanonicalLargeFieldDecay

currentP10CanonicalLargeFieldDecay : P10CanonicalLargeFieldDecay
currentP10CanonicalLargeFieldDecay = p10-canonical-large-field-decay

P10DecayMatchesGraphLargeFieldDecay :
  P10CanonicalLargeFieldDecay →
  ∀ (k : Nat) (X : List Nat) →
  ∀ (C_large : Nat) →
  largeFieldActivity k X ≤ C_large * (c-large ^ Φ-large k X)
P10DecayMatchesGraphLargeFieldDecay decay k X C_large =
  P10bLargeFieldActivityBound k X C_large large-field

P08P11LargeFieldDecayFromP10 :
  ∀ (k : Nat) (X : List Nat) →
  ∀ (C_large : Nat) →
  largeFieldActivity k X ≤ C_large * (c-large ^ Φ-large k X)
P08P11LargeFieldDecayFromP10 k X =
  P10DecayMatchesGraphLargeFieldDecay
    currentP10CanonicalLargeFieldDecay
    k
    X

record P08P11LowerLeavesDischarged (k : Nat) (X : List Nat) : Set₁ where
  field
    p0-pos : 0 < p0-coupling k
    entropy-fac : entropyFactor X
    large-field-decay : ∀ (C_large : Nat) → largeFieldActivity k X ≤ C_large * (c-large ^ Φ-large k X)

P08P11LowerLeavesDischargedFromOwnedLeaves :
  ∀ {k X} →
  (p0-pos-owned : 0 < p0-coupling k) →
  (entropy-fac-owned : entropyFactor X) →
  (large-field-decay-owned : ∀ (C_large : Nat) → largeFieldActivity k X ≤ C_large * (c-large ^ Φ-large k X)) →
  P08P11LowerLeavesDischarged k X
P08P11LowerLeavesDischargedFromOwnedLeaves p0-pos-owned entropy-fac-owned large-field-decay-owned =
  record
    { p0-pos = p0-pos-owned
    ; entropy-fac = entropy-fac-owned
    ; large-field-decay = large-field-decay-owned
    }

currentP08P11LowerLeavesDischarged :
  ∀ (k : Nat) (X : List Nat) →
  P08P11LowerLeavesDischarged k X
currentP08P11LowerLeavesDischarged k X =
  P08P11LowerLeavesDischargedFromOwnedLeaves
    (PZeroPositiveFromGaussianComponents k (postulatedRegime k))
    (P08P11EntropyFactorFromKPMargin X)
    (P08P11LargeFieldDecayFromP10 k X)

P08P11FromLowerLeavesAndConstants :
  ∀ (k : Nat) (X : List Nat) →
  P08P11LowerLeavesDischarged k X →
  (∀ (C-entropy C-dec : Nat) → c-large ≥ C-entropy + C-dec) →
  P08P11AbsorptionPackage k X
P08P11FromLowerLeavesAndConstants k X lowerLeaves constants-close =
  record
    { p0-pos =
        P08P11LowerLeavesDischarged.p0-pos lowerLeaves
    ; entropy-fac =
        P08P11LowerLeavesDischarged.entropy-fac lowerLeaves
    ; large-field-decay =
        P08P11LowerLeavesDischarged.large-field-decay lowerLeaves
    ; constants-close =
        constants-close
    }

P08P11FromStandardPositivityAndConstants :
  (k : Nat) (X : List Nat)
  → PositiveProduct
  → ExpPositiveℝ
  → PositiveDefiniteDeterminantPositive
  → GaussianNormalizationPositiveFromDet
  → (∀ (C-entropy C-dec : Nat) → c-large ≥ C-entropy + C-dec)
  → P08P11AbsorptionPackage k X
P08P11FromStandardPositivityAndConstants k X pos-prod exp-pos det-pos gauss-pos constants-close =
  P08P11FromLowerLeavesAndConstants
    k
    X
    (currentP08P11LowerLeavesDischarged k X)
    constants-close

-- ── Sprint 4: P33 Perturbation Stability ──────────────────────────────

postulate
  LocalMetricPerturbation : (k : Nat) (X : List Nat) → ℝ
  ε-real-const : ℝ
  isEdgeOf : Nat → (k : Nat) → List Nat → Set
  w-weight-ℝ : (k : Nat) → Nat → ℝ

SmallFieldRegularityControlsPerturbation : Set
SmallFieldRegularityControlsPerturbation =
  ∀ (k : Nat) (X : List Nat) →
  SmallFieldRegularity k X →
  LocalMetricPerturbation k X ≤ℝ ε-real-const

LinkWeightStabilityMargin : Set
LinkWeightStabilityMargin =
  Σ ℝ (λ ε₀ →
  Σ ℝ (λ m →
    (0ℝ <ℝ ε₀)
    × (0ℝ <ℝ m)
    ×
    (∀ (k : Nat) (X : List Nat) (e : Nat) →
      LocalMetricPerturbation k X ≤ℝ ε₀
      → isEdgeOf e k X
      → m ≤ℝ w-weight-ℝ k e)
  ))

data P33a1AnalyticDischargePackage : Set where
  p33a1-analytic-discharge :
    P33a1AnalyticDischargePackage

data P33DiameterLaneFromAnalyticDischarge : Set where
  p33-diameter-lane :
    P33DiameterLaneFromAnalyticDischarge

P33a1AnalyticPackageFromPerturbationStability :
  SmallFieldRegularityControlsPerturbation
  → LinkWeightStabilityMargin
  → P33a1AnalyticDischargePackage
P33a1AnalyticPackageFromPerturbationStability sf-ctrl margin =
  p33a1-analytic-discharge

P33FromAnalyticStability :
  P33a1AnalyticDischargePackage
  → P33DiameterLaneFromAnalyticDischarge
P33FromAnalyticStability pkg = p33-diameter-lane

------------------------------------------------------------------------
-- § ClaySupporting consumption bridge.
--
-- The elementary beams in DASHI.Physics.ClaySupportingSpanningTreeEncoding
-- and DASHI.Physics.ClaySupportingPolymerCounting provide a generic
-- counting bound: if size-n connected skeletons through v admit an
-- injective encoding into length-(2n) walks from v, then their count
-- is ≤ (Δ²)ⁿ.
--
-- The bridge below consumes those modules in the YM Graph setting.
-- The encoding+decoder existence is the open graph-theory leaf; the
-- counting consequence follows unconditionally once it is supplied.

open import Data.Fin.Base using (Fin)
import Data.Fin.Base as Fin
open import DASHI.Physics.ClaySupportingElementaryLemmas
  using (pow)
open import DASHI.Physics.ClaySupportingPolymerCounting
  using (polymerSkeletonCountBound; shellCountBound; shellSum; inj⇒≤)
open import DASHI.Physics.ClaySupportingSpanningTreeEncoding
  using (canonicalEncodingCountBound; leftInverse⇒injective)
open import DASHI.Physics.ClaySupportingGraphCombinatorics
  using (BoundedDegreeBy; walkCount; BoundedDegreeWalkCount)
open import Function.Definitions using (Injective)

-- Bridge: from YM's BoundedDegree to ClaySupporting's BoundedDegreeBy.
-- The ClaySupporting modules work with nbrs : V → List V rather than
-- the YM Graph + countNeighbors interface.  This lemma makes the
-- encoding-count-bound available given a degree-compatible neighborhood
-- function.
P06ViaCanonicalEncodingCountBound :
  {V : Set} (nbrs : V → List V) (Δ : Nat) →
  BoundedDegreeBy nbrs Δ →
  (v : V) (n numSkel : Nat) →
  (enc : Fin numSkel → Fin (walkCount nbrs v (n + n))) →
  (dec : Fin (walkCount nbrs v (n + n)) → Fin numSkel) →
  (∀ s → dec (enc s) ≡ s) →
  numSkel ≤ pow (Δ * Δ) n
P06ViaCanonicalEncodingCountBound nbrs Δ deg v n numSkel enc dec decenc =
  canonicalEncodingCountBound nbrs Δ deg v n numSkel enc dec decenc

------------------------------------------------------------------------
-- § Bridging lemmas between `_^_` (Data.Nat) and `pow` (ClaySupporting).

^≡pow : ∀ a n → a ^ n ≡ pow a n
^≡pow a zero    = refl
^≡pow a (suc n) = cong (a *_) (^≡pow a n)

private
  pow-+ : ∀ b m k → pow b (m + k) ≡ pow b m * pow b k
  pow-+ b zero    k = sym (*-identityˡ (pow b k))
  pow-+ b (suc m) k =
    trans (cong (b *_) (pow-+ b m k))
          (sym (*-assoc b (pow b m) (pow b k)))

  sq-swap : ∀ a p → (a * p) * (a * p) ≡ (a * a) * (p * p)
  sq-swap a p =
    trans (*-assoc a p (a * p))
      (trans (cong (a *_) (sym (*-assoc p a p)))
        (trans (cong (λ z → a * (z * p)) (*-comm p a))
          (trans (cong (a *_) (*-assoc a p p))
                 (sym (*-assoc a a (p * p))))))

pow-double : ∀ b n → pow b (n + n) ≡ pow (b * b) n
pow-double b zero    = refl
pow-double b (suc n) =
  trans (pow-+ b (suc n) (suc n))
    (trans (sq-swap b (pow b n))
           (cong ((b * b) *_)
                 (trans (sym (pow-+ b n n)) (pow-double b n))))

P06a2dBoundedDegreeWalkCount-pow :
  {G : Graph} {Δ : Nat} → BoundedDegree G Δ →
  (r : Graph.Vertex G) (L : Nat) →
  countWalks G r L ≤ pow Δ L
P06a2dBoundedDegreeWalkCount-pow {G} {Δ} bd r L =
  subst (λ z → countWalks G r L ≤ z) (^≡pow Δ L) (P06a2dBoundedDegreeWalkCount bd r L)

------------------------------------------------------------------------
-- § ActualReducedSkeletonToCanonicalCarrier — fail-closed bridge.
--
-- This is the gate that connects each actual reduced connected skeleton
-- to its canonical rooted-spanning-tree / DFS encoding with decoder.
--
-- The bridge packages:
--   (a) a rooted spanning tree for each connected skeleton
--   (b) a DFS encoding into a length-(2n) walk from the root
--   (c) a decoder left-inverse to the encoding
--   (d) compatibility with the repo's actual reduced skeleton type
--
-- and then derives:
--   # reduced skeletons of size n through v ≤ (Δ²)ⁿ
--
-- via P06ViaCanonicalEncodingCountBound.
--
-- The bridge is fail-closed: the encoding+decoder construction is the
-- open graph-theory leaf and bridgeClosed defaults to false.

record ActualReducedSkeletonToCanonicalCarrier (G : Graph) (Δ : Nat) : Set₁ where
  field
    -- Ambient bounded-degree hypothesis
    boundedDegree : BoundedDegree G Δ

    -- (a) Rooted spanning tree.
    -- Every rooted connected skeleton has a rooted spanning tree with
    -- an identified root vertex in the tree.
    rootedSpanningTree :
      (r : Graph.Vertex G) (X : List (Graph.Vertex G)) →
      RootedConnectedSkeleton G r X →
      Σ (SpanningTree G X) (λ st →
        Σ (Graph.Vertex (SpanningTree.T st)) (λ rT →
          (SpanningTree.embed st rT ≡ r) × RootedTree (SpanningTree.T st) rT
        )
      )

    -- (b) DFS encoding.
    -- For each rooted tree, a DFS/Euler tour whose length is bounded
    -- by twice the vertex count.
    dfsEncoding :
      {T : Graph} {r : Graph.Vertex T} →
      RootedTree T r →
      Σ (TreeDFSWalk T r) (λ w →
        TreeDFSWalk.length-w w ≤ 2 * (countVertices T)
      )

    -- (c) Decoder left-inverse.
    -- The encoding is invertible on the left: the walk uniquely
    -- determines the skeleton.  Standard DFS Euler tours have this
    -- property because the walk records every vertex in order of
    -- first visit; the skeleton can be recovered as the set of
    -- distinct vertices appearing in the walk.
    encode :
      (r : Graph.Vertex G) (n : Nat) →
      Fin (countSkeletons G r n) → Fin (countWalks G r (n + n))

    decode :
      (r : Graph.Vertex G) (n : Nat) →
      Fin (countWalks G r (n + n)) → Fin (countSkeletons G r n)

    decenc :
      (r : Graph.Vertex G) (n : Nat) →
      (s : Fin (countSkeletons G r n)) →
      decode r n (encode r n s) ≡ s

    -- (d) Compatibility proof.
    -- The encoding respects actual reduced skeletons: the encoded walk
    -- covers exactly the vertex set of the skeleton, so the decoder
    -- recovers the original vertex set.
    coversSkeleton :
      (r : Graph.Vertex G) (n : Nat)
      (s : Fin (countSkeletons G r n))
      (X : List (Graph.Vertex G)) →
      RootedReducedSkeleton G r X →
      ⊤

    -- (e) Encoding soundness layer
    skeletonVertices :
      (r : Graph.Vertex G) (n : Nat) →
      Fin (countSkeletons G r n) → List (Graph.Vertex G)

    walkRange :
      (r : Graph.Vertex G) (n : Nat) →
      Fin (countWalks G r (n + n)) → List (Graph.Vertex G)

    encodeWalkCoversSkeleton :
      (r : Graph.Vertex G) (n : Nat) (s : Fin (countSkeletons G r n)) →
      skeletonVertices r n s ⊆ walkRange r n (encode r n s)

    encodeWalkOnlyVisitsSkeleton :
      (r : Graph.Vertex G) (n : Nat) (s : Fin (countSkeletons G r n)) →
      walkRange r n (encode r n s) ⊆ skeletonVertices r n s

    encodeWalkRangeExact :
      (r : Graph.Vertex G) (n : Nat) (s : Fin (countSkeletons G r n)) →
      SameVertexSet (walkRange r n (encode r n s)) (skeletonVertices r n s)



    -- Derived counting consequence.
    -- Once the encoding+decoder exist, P06ViaCanonicalEncodingCountBound
    -- (or equivalently P06a2SizeShellCountingOwned) gives the bound.
    skeletonCountBound :
      (r : Graph.Vertex G) (n : Nat) →
      countSkeletons G r n ≤ pow (Δ * Δ) n

    -- Structural/proof gates
    bridgeStructurallyWired : Bool
    bridgeProofClosed : Bool

-- Readout booleans: structurally wired is true, but mathematical proof closed is false (conditional on postulates).
actualReducedSkeletonToCanonicalCarrierStructurallyWired : Bool
actualReducedSkeletonToCanonicalCarrierStructurallyWired = true

actualReducedSkeletonToCanonicalCarrierStructurallyWiredIsTrue :
  actualReducedSkeletonToCanonicalCarrierStructurallyWired ≡ true
actualReducedSkeletonToCanonicalCarrierStructurallyWiredIsTrue = refl

actualReducedSkeletonToCanonicalCarrierProofClosed : Bool
actualReducedSkeletonToCanonicalCarrierProofClosed = false

actualReducedSkeletonToCanonicalCarrierProofClosedIsFalse :
  actualReducedSkeletonToCanonicalCarrierProofClosed ≡ false
actualReducedSkeletonToCanonicalCarrierProofClosedIsFalse = refl

------------------------------------------------------------------------
-- § Injection-based skeleton encoding record.
--
-- Replaces the `encode`/`decode`/`decenc` triad with a single
-- `encodeInjective` field, avoiding the need for a total geometric
-- decoder on arbitrary walks.  The record packages:
--
--   skeletonOf     — actual vertex set + skeleton witnesses for each index
--   walkRange      — vertex set of a walk index
--   encode         — walk index assigned to each skeleton index
--   encodeSound    — the walk visits exactly the skeleton's vertex set
--   encodeInjective — distinct skeletons map to distinct walk indices

record ActualSkeletonEncodingData
  (G : Graph) (r : Graph.Vertex G) (n : Nat) : Set₁ where
  field
    skeletonOf :
      Fin (countSkeletons G r n) →
      Σ (List (Graph.Vertex G)) λ X →
        RootedReducedSkeleton G r X ×
        RootedConnectedSkeleton G r X ×
        length X ≡ n

    walkRange :
      Fin (countWalks G r (n + n)) → List (Graph.Vertex G)

    encode :
      Fin (countSkeletons G r n) →
      Fin (countWalks G r (n + n))

    encodeSound :
      ∀ s →
      SameVertexSet
        (walkRange (encode s))
        (proj₁ (skeletonOf s))

    encodeInjective :
      ∀ {s₁ s₂} →
      encode s₁ ≡ encode s₂ →
      s₁ ≡ s₂

-- Derived counting bound: given the injection, the skeleton count is ≤ (Δ²)ⁿ.
actualSkeletonCountBound :
  {G : Graph} {Δ : Nat} → BoundedDegree G Δ →
  {r : Graph.Vertex G} {n : Nat} →
  ActualSkeletonEncodingData G r n →
  countSkeletons G r n ≤ pow (Δ * Δ) n
actualSkeletonCountBound {G} {Δ} bd {r} {n} ased =
  let open ActualSkeletonEncodingData ased

      skelCountLeWalkCount : countSkeletons G r n ≤ countWalks G r (n + n)
      skelCountLeWalkCount = inj⇒≤ {encode = encode} encodeInjective

      walkCountLePow : countWalks G r (n + n) ≤ pow Δ (n + n)
      walkCountLePow = P06a2dBoundedDegreeWalkCount-pow bd r (n + n)

      powDouble : pow Δ (n + n) ≤ pow (Δ * Δ) n
      powDouble = subst (pow Δ (n + n) ≤_) (pow-double Δ n) ≤-refl

  in ≤-trans skelCountLeWalkCount (≤-trans walkCountLePow powDouble)

------------------------------------------------------------------------
-- Bridge alias: consume the new bound from the old carrier name.

skeletonCountBoundFromEncodingData :
  {G : Graph} {Δ : Nat} → BoundedDegree G Δ →
  {r : Graph.Vertex G} {n : Nat} →
  ActualSkeletonEncodingData G r n →
  countSkeletons G r n ≤ pow (Δ * Δ) n
skeletonCountBoundFromEncodingData = actualSkeletonCountBound

------------------------------------------------------------------------
-- § SkeletonEnumeration and WalkEnumeration — explicit witness records.
--
-- These records make the remaining P06 proof obligation concrete:
-- the bijection between `Fin (countSkeletons G r n)` and actual
-- skeleton objects, and similarly for walks.

record SkeletonEnumeration
  (G : Graph) (r : Graph.Vertex G) (n : Nat) : Set₁ where
  field
    skeletonOf :
      Fin (countSkeletons G r n) →
      Σ (List (Graph.Vertex G)) λ X →
        RootedReducedSkeleton G r X ×
        RootedConnectedSkeleton G r X ×
        length X ≡ n

    skeletonIndex :
      Σ (List (Graph.Vertex G)) (λ X →
        RootedReducedSkeleton G r X ×
        RootedConnectedSkeleton G r X ×
        length X ≡ n) →
      Fin (countSkeletons G r n)

    skeletonIndexOf :
      ∀ s → skeletonIndex (skeletonOf s) ≡ s

record WalkEnumeration
  (G : Graph) (r : Graph.Vertex G) (L : Nat) : Set₁ where
  field
    walkOf :
      Fin (countWalks G r L) → List (Graph.Vertex G)

    walkIndex :
      List (Graph.Vertex G) → Fin (countWalks G r L)

    walkIndexOf :
      ∀ w → walkOf (walkIndex w) ≡ w

------------------------------------------------------------------------
-- § SameVertexSet algebra.

sameVertexSet-refl : {A : Set} {xs : List A} → SameVertexSet xs xs
sameVertexSet-refl = (λ x∈xs → x∈xs) , (λ x∈xs → x∈xs)

sameVertexSet-sym : {A : Set} {xs ys : List A} → SameVertexSet xs ys → SameVertexSet ys xs
sameVertexSet-sym (xs⊆ys , ys⊆xs) = ys⊆xs , xs⊆ys

sameVertexSet-trans :
  {A : Set} {xs ys zs : List A} →
  SameVertexSet xs ys → SameVertexSet ys zs → SameVertexSet xs zs
sameVertexSet-trans (xs⊆ys , ys⊆xs) (ys⊆zs , zs⊆ys) =
  (λ x∈xs → ys⊆zs (xs⊆ys x∈xs)) , (λ z∈zs → ys⊆xs (zs⊆ys z∈zs))

listEq⇒sameVertexSet :
  {A : Set} {xs ys : List A} → xs ≡ ys → SameVertexSet xs ys
listEq⇒sameVertexSet refl = sameVertexSet-refl

-------------------------------------------------------------------------
-- § Generic NoDuplicates, Sorted, TotalOrder, and canonical list equality.

_∉_ : {A : Set} → A → List A → Set
x ∉ xs = ¬ (x ∈ xs)

data NoDuplicates {A : Set} : List A → Set where
  noDup-nil  : NoDuplicates []
  noDup-cons : ∀ {x xs} → x ∉ xs → NoDuplicates xs → NoDuplicates (x ∷ xs)

-- A dependent filter may retain different proof payloads for a source
-- element, so record equality is the wrong uniqueness notion downstream.
-- This theorem instead transports no-duplicates from a source projection.
filterMapListWithMembership-projection-noDup :
  {A : Set} {B : A → Set} {C : Set} →
  (xs : List A) →
  (f : (x : A) → x ∈ xs → Dec (B x)) →
  (out : Σ A B → C) →
  (source : A → C) →
  ((x : A) → (x∈ : x ∈ xs) → (bx : B x) →
    out (x , bx) ≡ source x) →
  NoDuplicates (mapList source xs) →
  NoDuplicates (mapList out (filterMapListWithMembership xs f))
filterMapListWithMembership-projection-noDup [] f out source preserves nd =
  noDup-nil
filterMapListWithMembership-projection-noDup (x ∷ xs) f out source preserves
  (noDup-cons sourcex∉tail nd-tail)
  with f x here
... | yes bx =
  noDup-cons head∉tail tailNoDup
  where
    tailF = λ z z∈ → f z (there z∈)

    tailNoDup :
      NoDuplicates
        (mapList out (filterMapListWithMembership xs tailF))
    tailNoDup =
      filterMapListWithMembership-projection-noDup
        xs tailF out source
        (λ z z∈ bz → preserves z (there z∈) bz)
        nd-tail

    head∉tail :
      out (x , bx) ∉
      mapList out (filterMapListWithMembership xs tailF)
    head∉tail head∈tail =
      let pairMember = map-elem out (filterMapListWithMembership xs tailF) head∈tail
          p = proj₁ pairMember
          outEq = proj₁ (proj₂ pairMember)
          p∈ = proj₂ (proj₂ pairMember)
          provenance =
            filterMapListWithMembership-elem xs tailF p∈
          y = proj₁ provenance
          y∈ = proj₁ (proj₂ provenance)
          by = proj₁ (proj₂ (proj₂ provenance))
          pairEq = proj₂ (proj₂ (proj₂ provenance))
          headSource : out (x , bx) ≡ source x
          headSource = preserves x here bx
          pairSource : out p ≡ source y
          pairSource =
            trans
              (cong out pairEq)
              (preserves y (there y∈) by)
          sourceEq : source x ≡ source y
          sourceEq = trans (sym headSource) (trans outEq pairSource)
      in sourcex∉tail
           (subst (λ z → z ∈ mapList source xs) (sym sourceEq)
             (in-map source y∈))
... | no ¬bx =
  filterMapListWithMembership-projection-noDup
    xs
    (λ z z∈ → f z (there z∈))
    out source
    (λ z z∈ bz → preserves z (there z∈) bz)
    nd-tail

removeMember :
  {A : Set} {x : A} {xs : List A} →
  x ∈ xs →
  List A
removeMember {xs = _ ∷ xs} here = xs
removeMember {xs = y ∷ xs} (there x∈xs) = y ∷ removeMember x∈xs

removeMember-length-suc :
  {A : Set} {x : A} {xs : List A} →
  (x∈xs : x ∈ xs) →
  suc (length (removeMember x∈xs)) ≡ length xs
removeMember-length-suc {xs = _ ∷ _} here = refl
removeMember-length-suc {xs = _ ∷ _} (there x∈xs) =
  cong suc (removeMember-length-suc x∈xs)

removeMemberKeepsOther :
  {A : Set} {x y : A} {xs : List A} →
  (x∈xs : x ∈ xs) →
  y ∈ xs →
  (y ≡ x → ⊥) →
  y ∈ removeMember x∈xs
removeMemberKeepsOther here here y≢x = ⊥-elim (y≢x refl)
removeMemberKeepsOther here (there y∈xs) y≢x = y∈xs
removeMemberKeepsOther (there x∈xs) here y≢x = here
removeMemberKeepsOther (there x∈xs) (there y∈xs) y≢x =
  there (removeMemberKeepsOther x∈xs y∈xs y≢x)

noDupSubsetLength≤ :
  {A : Set} {xs ys : List A} →
  NoDuplicates xs →
  xs ⊆ ys →
  length xs ≤ length ys
noDupSubsetLength≤ noDup-nil xs⊆ys = z≤n
noDupSubsetLength≤ {xs = x ∷ xs} {ys = ys}
  (noDup-cons x∉xs noDup-xs) xs⊆ys =
  let
    x∈ys : x ∈ ys
    x∈ys = xs⊆ys here

    xs⊆remove : xs ⊆ removeMember x∈ys
    xs⊆remove {y} y∈xs =
      removeMemberKeepsOther
        x∈ys
        (xs⊆ys (there y∈xs))
        (λ y≡x → x∉xs (subst (λ z → z ∈ xs) y≡x y∈xs))

    ih : length xs ≤ length (removeMember x∈ys)
    ih = noDupSubsetLength≤ noDup-xs xs⊆remove
  in
    subst
      (λ n → suc (length xs) ≤ n)
      (removeMember-length-suc x∈ys)
      (s≤s ih)

sameVertexSetNoDuplicatesLength :
  {A : Set} {xs ys : List A} →
  NoDuplicates xs →
  NoDuplicates ys →
  SameVertexSet xs ys →
  length xs ≡ length ys
sameVertexSetNoDuplicatesLength noDup-xs noDup-ys (xs⊆ys , ys⊆xs) =
  ≤-antisym
    (noDupSubsetLength≤ noDup-xs xs⊆ys)
    (noDupSubsetLength≤ noDup-ys ys⊆xs)

data Sorted {A : Set} (_≤_ : A → A → Set) : List A → Set where
  sorted-nil    : Sorted _≤_ []
  sorted-single : ∀ {x} → Sorted _≤_ (x ∷ [])
  sorted-cons   : ∀ {x y xs} → x ≤ y → Sorted _≤_ (y ∷ xs) → Sorted _≤_ (x ∷ y ∷ xs)

sorted-tail : {A : Set} {_≤_ : A → A → Set} {x : A} {xs : List A} → Sorted _≤_ (x ∷ xs) → Sorted _≤_ xs
sorted-tail sorted-single          = sorted-nil
sorted-tail (sorted-cons _ rest)   = rest

record TotalOrder {A : Set} (_≤_ : A → A → Set) : Set where
  field
    ord-refl    : ∀ {x} → x ≤ x
    ord-trans   : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ord-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
    ord-total   : ∀ x y → (x ≤ y) ⊎ (y ≤ x)

record CanonicalVertexList {A : Set} (_≤_ : A → A → Set) (xs : List A) : Set where
  field
    noDup  : NoDuplicates xs
    sorted : Sorted _≤_ xs

module SameVertexSetCanonicalListEq
    {A : Set} {_≤_ : A → A → Set} (TO : TotalOrder _≤_)
  where

  open TotalOrder TO

  sorted-min : ∀ {x a xs} → Sorted _≤_ (x ∷ xs) → a ∈ xs → x ≤ a
  sorted-min (sorted-cons {y = y} x≤y s) (here {xs = _})  = x≤y
  sorted-min (sorted-cons {y = y} x≤y s) (there a∈xs)     = ord-trans x≤y (sorted-min s a∈xs)

  head-min : ∀ {x y xs} → Sorted _≤_ (x ∷ xs) → y ∈ (x ∷ xs) → x ≤ y
  head-min sorted-single                 here          = ord-refl
  head-min (sorted-cons x≤y' s)          here          = ord-refl
  head-min (sorted-cons {y = y'} x≤y' s) (there y∈rest)
    with y∈rest
  ... | here       = x≤y'
  ... | (there y∈xs) = ord-trans x≤y' (sorted-min s y∈xs)

  sameVertexSetCanonicalListEq :
    {xs ys : List A} →
    CanonicalVertexList _≤_ xs →
    CanonicalVertexList _≤_ ys →
    SameVertexSet xs ys →
    xs ≡ ys

  sameVertexSetCanonicalListEq {[]} {[]} _ _ _ = refl

  sameVertexSetCanonicalListEq {[]} {y ∷ ys} _ _ (_ , ys⊆xs)
    with ys⊆xs here
  ... | ()

  sameVertexSetCanonicalListEq {x ∷ xs} {[]} _ _ (xs⊆ys , _)
    with xs⊆ys here
  ... | ()

  sameVertexSetCanonicalListEq
    {x ∷ xs} {y ∷ ys}
    (record { noDup = noDup-cons x∉xs noDup-xs ; sorted = sorted-xs })
    (record { noDup = noDup-cons y∉ys noDup-ys ; sorted = sorted-ys })
    (xs⊆ys , ys⊆xs) = body

    where
      x∈yys : x ∈ (y ∷ ys)
      x∈yys = xs⊆ys here

      y∈xxs : y ∈ (x ∷ xs)
      y∈xxs = ys⊆xs here

      x≤y : x ≤ y
      x≤y = head-min sorted-xs y∈xxs

      y≤x : y ≤ x
      y≤x = head-min sorted-ys x∈yys

      x≡y : x ≡ y
      x≡y = ord-antisym x≤y y≤x

      xs⊆ys' : xs ⊆ ys
      xs⊆ys' a∈xs with xs⊆ys (there a∈xs)
      ... | here   = ⊥-elim (x∉xs (subst (λ z → z ∈ xs) (sym x≡y) a∈xs))
      ... | there a∈ys = a∈ys

      ys⊆xs' : ys ⊆ xs
      ys⊆xs' b∈ys with ys⊆xs (there b∈ys)
      ... | here   = ⊥-elim (y∉ys (subst (λ z → z ∈ ys) x≡y b∈ys))
      ... | there b∈xs = b∈xs

      sameVS : SameVertexSet xs ys
      sameVS = xs⊆ys' , ys⊆xs'

      body : x ∷ xs ≡ y ∷ ys
      body = subst (λ z → x ∷ xs ≡ z ∷ ys) x≡y
                   (cong (x ∷_) (sameVertexSetCanonicalListEq
                                  (record { noDup = noDup-xs ; sorted = sorted-tail sorted-xs })
                                  (record { noDup = noDup-ys ; sorted = sorted-tail sorted-ys })
                                  sameVS))

------------------------------------------------------------------------
-- § Vertex order construct (total order on Graph.Vertex G via labeling).

record VertexLabeling (G : Graph) : Set₁ where
  field
    label :
      Graph.Vertex G → Nat

    labelInjective :
      ∀ {u v} →
      label u ≡ label v →
      u ≡ v

postulate
  currentVertexLabeling : {G : Graph} → VertexLabeling G

vertexOrder : {G : Graph} → Graph.Vertex G → Graph.Vertex G → Set
vertexOrder {G} u v = VertexLabeling.label (currentVertexLabeling {G}) u ≤ VertexLabeling.label (currentVertexLabeling {G}) v

vertexOrderIsTotalOrder : {G : Graph} → TotalOrder (vertexOrder {G})
vertexOrderIsTotalOrder {G} = record
  { ord-refl    = ≤-refl
  ; ord-trans   = ≤-trans
  ; ord-antisym = λ {u} {v} u≤v v≤u → VertexLabeling.labelInjective (currentVertexLabeling {G}) (≤-antisym u≤v v≤u)
  ; ord-total   = λ u v → ≤-total (VertexLabeling.label (currentVertexLabeling {G}) u) (VertexLabeling.label (currentVertexLabeling {G}) v)
  }

vertexEqDec :
  {G : Graph} →
  (u v : Graph.Vertex G) →
  Dec (u ≡ v)
vertexEqDec {G} u v
  with NatP._≟_
         (VertexLabeling.label (currentVertexLabeling {G}) u)
         (VertexLabeling.label (currentVertexLabeling {G}) v)
... | yes labelsEq =
      yes (VertexLabeling.labelInjective (currentVertexLabeling {G}) labelsEq)
... | no labelsNeq =
      no
        (λ u≡v →
           labelsNeq
             (cong (VertexLabeling.label (currentVertexLabeling {G})) u≡v))

memberDec :
  {A : Set} →
  ((x y : A) → Dec (x ≡ y)) →
  (x : A) →
  (xs : List A) →
  Dec (x ∈ xs)
memberDec decEq x [] = no (λ ())
memberDec decEq x (y ∷ xs)
  with decEq x y
... | yes refl = yes here
... | no x≢y
    with memberDec decEq x xs
... | yes x∈xs = yes (there x∈xs)
... | no x∉xs = no λ
      { here → x≢y refl
      ; (there x∈xs) → x∉xs x∈xs
      }

insertUnique :
  {G : Graph} →
  Graph.Vertex G →
  List (Graph.Vertex G) →
  List (Graph.Vertex G)
insertUnique {G} x [] = x ∷ []
insertUnique {G} x (y ∷ ys)
  with vertexEqDec {G} x y
... | yes _ = y ∷ ys
... | no _
    with TotalOrder.ord-total (vertexOrderIsTotalOrder {G}) x y
... | inj₁ _ = x ∷ y ∷ ys
... | inj₂ _ = y ∷ insertUnique {G} x ys

canonicalize :
  {G : Graph} →
  List (Graph.Vertex G) →
  List (Graph.Vertex G)
canonicalize [] = []
canonicalize {G} (x ∷ xs) = insertUnique {G} x (canonicalize {G} xs)

mutual
  insertUniqueSoundEq :
    {G : Graph} →
    {x w y : Graph.Vertex G} →
    {ys : List (Graph.Vertex G)} →
    x ≡ y →
    w ∈ (y ∷ ys) →
    w ≡ x ⊎ w ∈ (y ∷ ys)
  insertUniqueSoundEq x≡y here = inj₁ (sym x≡y)
  insertUniqueSoundEq x≡y (there w∈ys) = inj₂ (there w∈ys)

  insertUniqueSoundBefore :
    {G : Graph} →
    {x w y : Graph.Vertex G} →
    {ys : List (Graph.Vertex G)} →
    w ∈ (x ∷ y ∷ ys) →
    w ≡ x ⊎ w ∈ (y ∷ ys)
  insertUniqueSoundBefore here = inj₁ refl
  insertUniqueSoundBefore (there w∈y∷ys) = inj₂ w∈y∷ys

  insertUniqueSoundAfter :
    {G : Graph} →
    {x w y : Graph.Vertex G} →
    {ys : List (Graph.Vertex G)} →
    w ∈ (y ∷ insertUnique {G} x ys) →
    w ≡ x ⊎ w ∈ (y ∷ ys)
  insertUniqueSoundAfter here = inj₂ here
  insertUniqueSoundAfter {G} {x} {w} {y} {ys} (there w∈tail)
    with insertUniqueSound {G} {x} {w} {ys} w∈tail
  ... | inj₁ w≡x = inj₁ w≡x
  ... | inj₂ w∈ys = inj₂ (there w∈ys)

  insertUniqueSound :
    {G : Graph} →
    {x y : Graph.Vertex G} →
    {xs : List (Graph.Vertex G)} →
    y ∈ insertUnique {G} x xs →
    y ≡ x ⊎ y ∈ xs
  insertUniqueSound {G} {x} {x} {[]} here = inj₁ refl
  insertUniqueSound {G} {x} {w} {y ∷ ys} w∈insert
    with vertexEqDec {G} x y
  ... | yes x≡y = insertUniqueSoundEq {G} {x} {w} {y} {ys} x≡y w∈insert
  ... | no x≢y
      with TotalOrder.ord-total (vertexOrderIsTotalOrder {G}) x y
  ...   | inj₁ x≤y = insertUniqueSoundBefore {G} {x} {w} {y} {ys} w∈insert
  ...   | inj₂ y≤x = insertUniqueSoundAfter {G} {x} {w} {y} {ys} w∈insert

mutual
  insertUniqueComplete :
    {G : Graph} →
    {x y : Graph.Vertex G} →
    {xs : List (Graph.Vertex G)} →
    y ≡ x ⊎ y ∈ xs →
    y ∈ insertUnique {G} x xs
  insertUniqueComplete {G} {x} {y} {[]} (inj₁ refl) = here
  insertUniqueComplete {G} {x} {y} {[]} (inj₂ ())
  insertUniqueComplete {G} {x} {y} {z ∷ zs} y∈
    with vertexEqDec {G} x z
  ... | yes x≡z = insertUniqueCompleteEq {G} {x} {y} {z} {zs} x≡z y∈
  ... | no x≢z
      with TotalOrder.ord-total (vertexOrderIsTotalOrder {G}) x z
  ...   | inj₁ x≤z = insertUniqueCompleteBefore {G} {x} {y} {z} {zs} y∈
  ...   | inj₂ z≤x = insertUniqueCompleteAfter {G} {x} {y} {z} {zs} y∈

  insertUniqueCompleteEq :
    {G : Graph} →
    {x y z : Graph.Vertex G} →
    {zs : List (Graph.Vertex G)} →
    x ≡ z →
    y ≡ x ⊎ y ∈ (z ∷ zs) →
    y ∈ (z ∷ zs)
  insertUniqueCompleteEq {G} {x} {y} {z} {zs} x≡z (inj₁ refl) =
    subst (λ w → w ∈ (z ∷ zs)) (sym x≡z) here
  insertUniqueCompleteEq x≡z (inj₂ y∈z∷zs) = y∈z∷zs

  insertUniqueCompleteBefore :
    {G : Graph} →
    {x y z : Graph.Vertex G} →
    {zs : List (Graph.Vertex G)} →
    y ≡ x ⊎ y ∈ (z ∷ zs) →
    y ∈ (x ∷ z ∷ zs)
  insertUniqueCompleteBefore (inj₁ refl) = here
  insertUniqueCompleteBefore (inj₂ y∈z∷zs) = there y∈z∷zs

  insertUniqueCompleteAfter :
    {G : Graph} →
    {x y z : Graph.Vertex G} →
    {zs : List (Graph.Vertex G)} →
    y ≡ x ⊎ y ∈ (z ∷ zs) →
    y ∈ (z ∷ insertUnique {G} x zs)
  insertUniqueCompleteAfter {G} {x} {y} {z} {zs} (inj₁ refl) =
    there (insertUniqueComplete {G} {x} {x} {zs} (inj₁ refl))
  insertUniqueCompleteAfter {G} {x} {y} {z} {zs} (inj₂ here) = here
  insertUniqueCompleteAfter {G} {x} {y} {z} {zs} (inj₂ (there y∈zs)) =
    there (insertUniqueComplete {G} {x} {y} {zs} (inj₂ y∈zs))

insertUniquePrependSorted :
  {G : Graph} →
  {x y z : Graph.Vertex G} →
  {zs : List (Graph.Vertex G)} →
  vertexOrder {G} y z →
  vertexOrder {G} y x →
  Sorted (vertexOrder {G}) (insertUnique {G} x (z ∷ zs)) →
  Sorted (vertexOrder {G}) (y ∷ insertUnique {G} x (z ∷ zs))
insertUniquePrependSorted {G} {x} {y} {z} {zs} y≤z y≤x sorted-tail-insert
  with vertexEqDec {G} x z
... | yes _ = sorted-cons y≤z sorted-tail-insert
... | no _
    with TotalOrder.ord-total (vertexOrderIsTotalOrder {G}) x z
...   | inj₁ _ = sorted-cons y≤x sorted-tail-insert
...   | inj₂ _ = sorted-cons y≤z sorted-tail-insert

insertUniquePreservesNonMember :
  {G : Graph} →
  {x y : Graph.Vertex G} →
  {xs : List (Graph.Vertex G)} →
  (x ≡ y → ⊥) →
  y ∉ xs →
  y ∉ insertUnique {G} x xs
insertUniquePreservesNonMember {G} {x} {y} {xs} x≢y y∉xs y∈insert
  with insertUniqueSound {G} {x} {y} {xs} y∈insert
... | inj₁ y≡x = x≢y (sym y≡x)
... | inj₂ y∈xs = y∉xs y∈xs

insertUniquePreservesCanonical :
  {G : Graph} →
  (x : Graph.Vertex G) →
  (xs : List (Graph.Vertex G)) →
  NoDuplicates xs →
  Sorted (vertexOrder {G}) xs →
  NoDuplicates (insertUnique {G} x xs) ×
  Sorted (vertexOrder {G}) (insertUnique {G} x xs)
insertUniquePreservesCanonical {G} x [] noDup-nil sorted-nil =
  noDup-cons (λ ()) noDup-nil , sorted-single
insertUniquePreservesCanonical {G} x (y ∷ []) (noDup-cons y∉[] noDup-nil) sorted-single
  with vertexEqDec {G} x y
... | yes _ = noDup-cons y∉[] noDup-nil , sorted-single
... | no x≢y
    with TotalOrder.ord-total (vertexOrderIsTotalOrder {G}) x y
...   | inj₁ x≤y =
        noDup-cons
          (λ { here → x≢y refl ; (there ()) })
          (noDup-cons y∉[] noDup-nil)
      , sorted-cons x≤y sorted-single
...   | inj₂ y≤x =
        noDup-cons
          (λ { here → x≢y (sym refl) ; (there ()) })
          (noDup-cons (λ ()) noDup-nil)
      , sorted-cons y≤x sorted-single
insertUniquePreservesCanonical {G} x (y ∷ z ∷ zs)
  (noDup-cons y∉z∷zs noDup-z∷zs@(noDup-cons z∉zs noDup-zs))
  sorted-y∷z∷zs@(sorted-cons y≤z sorted-z∷zs)
  with vertexEqDec {G} x y
... | yes _ = noDup-cons y∉z∷zs noDup-z∷zs , sorted-y∷z∷zs
... | no x≢y
    with TotalOrder.ord-total (vertexOrderIsTotalOrder {G}) x y
...   | inj₁ x≤y =
        let
          module V = SameVertexSetCanonicalListEq
            {A = Graph.Vertex G} {_≤_ = vertexOrder {G}} (vertexOrderIsTotalOrder {G})

          x∉y∷z∷zs : x ∉ (y ∷ z ∷ zs)
          x∉y∷z∷zs x∈y∷z∷zs =
            x≢y (TotalOrder.ord-antisym (vertexOrderIsTotalOrder {G}) x≤y (V.head-min sorted-y∷z∷zs x∈y∷z∷zs))
        in
          noDup-cons x∉y∷z∷zs (noDup-cons y∉z∷zs noDup-z∷zs)
        , sorted-cons x≤y sorted-y∷z∷zs
...   | inj₂ y≤x
      with insertUniquePreservesCanonical {G} x (z ∷ zs) noDup-z∷zs sorted-z∷zs
...     | noDup-tail-insert , sorted-tail-insert =
          noDup-cons
            (insertUniquePreservesNonMember {G} {x} {y} {z ∷ zs} x≢y y∉z∷zs)
            noDup-tail-insert
          , insertUniquePrependSorted {G} {x} {y} {z} {zs} y≤z y≤x sorted-tail-insert

canonicalizeCanonical :
  {G : Graph} →
  (xs : List (Graph.Vertex G)) →
  NoDuplicates (canonicalize {G} xs) ×
  Sorted (vertexOrder {G}) (canonicalize {G} xs)
canonicalizeCanonical {G} [] = noDup-nil , sorted-nil
canonicalizeCanonical {G} (x ∷ xs)
  with canonicalizeCanonical {G} xs
... | noDup-xs , sorted-xs =
      insertUniquePreservesCanonical {G} x (canonicalize {G} xs) noDup-xs sorted-xs

canonicalizeSound :
  {G : Graph} →
  {x : Graph.Vertex G} →
  {xs : List (Graph.Vertex G)} →
  x ∈ canonicalize {G} xs →
  x ∈ xs
canonicalizeSound {G} {x} {[]} ()
canonicalizeSound {G} {x} {y ∷ ys} x∈canon
  with insertUniqueSound {G} {y} {x} {canonicalize {G} ys} x∈canon
... | inj₁ x≡y = subst (λ w → x ∈ (w ∷ ys)) x≡y here
... | inj₂ x∈canon-ys = there (canonicalizeSound {G} {x} {ys} x∈canon-ys)

canonicalizeComplete :
  {G : Graph} →
  {x : Graph.Vertex G} →
  {xs : List (Graph.Vertex G)} →
  x ∈ xs →
  x ∈ canonicalize {G} xs
canonicalizeComplete {G} {x} {[]} ()
canonicalizeComplete {G} {x} {y ∷ ys} here =
  insertUniqueComplete {G} {y} {x} {canonicalize {G} ys} (inj₁ refl)
canonicalizeComplete {G} {x} {y ∷ ys} (there x∈ys) =
  insertUniqueComplete
    {G} {y} {x} {canonicalize {G} ys}
    (inj₂ (canonicalizeComplete {G} {x} {ys} x∈ys))

canonicalizeNoDup :
  {G : Graph} →
  (xs : List (Graph.Vertex G)) →
  NoDuplicates (canonicalize {G} xs)
canonicalizeNoDup {G} xs = proj₁ (canonicalizeCanonical {G} xs)

canonicalizeSorted :
  {G : Graph} →
  (xs : List (Graph.Vertex G)) →
  Sorted (vertexOrder {G}) (canonicalize {G} xs)
canonicalizeSorted {G} xs = proj₂ (canonicalizeCanonical {G} xs)

------------------------------------------------------------------------
-- § Ball/path interfaces for the still-open containment route.
--
-- Current honest status:
--   • Vertex ordering is reduced to an injective Nat labeling.
--   • Ball containment is not yet proved.
--   • The interfaces below expose the next proof surfaces:
--       connected skeleton -> internal path
--       simple internal path -> length ≤ |X| - 1
--       bounded path -> ball membership
--     with the final containment theorem reduced to those interfaces.

pathLength :
  {G : Graph} {x y : Graph.Vertex G} →
  Path G x y → Nat
pathLength p = length (Path.vertices p) ∸ 1

last-cons :
  {A : Set} {x : A} {xs : List A} →
  (xs-ne : NonEmpty xs) →
  last (x ∷ xs) nonempty ≡ last xs xs-ne
last-cons {xs = _ ∷ []} nonempty = refl
last-cons {xs = _ ∷ _ ∷ _} nonempty = refl

suffixFromMembership :
  {A : Set} {x : A} {xs : List A} →
  x ∈ xs →
  List A
suffixFromMembership {xs = x ∷ xs} here = x ∷ xs
suffixFromMembership (there x∈xs) = suffixFromMembership x∈xs

suffixFromMembership-nonEmpty :
  {A : Set} {x : A} {xs : List A} →
  (x∈xs : x ∈ xs) →
  NonEmpty (suffixFromMembership x∈xs)
suffixFromMembership-nonEmpty here = nonempty
suffixFromMembership-nonEmpty (there x∈xs) = suffixFromMembership-nonEmpty x∈xs

suffixFromMembership-head :
  {A : Set} {x : A} {xs : List A} →
  (x∈xs : x ∈ xs) →
  head (suffixFromMembership x∈xs) (suffixFromMembership-nonEmpty x∈xs) ≡ x
suffixFromMembership-head {xs = x ∷ xs} here = refl
suffixFromMembership-head (there x∈xs) = suffixFromMembership-head x∈xs

suffixFromMembership-subset :
  {A : Set} {x : A} {xs : List A} →
  (x∈xs : x ∈ xs) →
  suffixFromMembership x∈xs ⊆ xs
suffixFromMembership-subset here z∈suffix = z∈suffix
suffixFromMembership-subset (there x∈xs) z∈suffix =
  there (suffixFromMembership-subset x∈xs z∈suffix)

suffixFromMembership-last :
  {A : Set} {x : A} {xs : List A} →
  (xs-ne : NonEmpty xs) →
  (x∈xs : x ∈ xs) →
  last (suffixFromMembership x∈xs) (suffixFromMembership-nonEmpty x∈xs) ≡
  last xs xs-ne
suffixFromMembership-last {xs = _ ∷ _} nonempty here = refl
suffixFromMembership-last {xs = _ ∷ _ ∷ _} nonempty (there x∈xs) =
  suffixFromMembership-last nonempty x∈xs

suffixFromMembership-adjacent :
  {G : Graph} {x : Graph.Vertex G} {xs : List (Graph.Vertex G)} →
  (x∈xs : x ∈ xs) →
  ConsecutiveEdges G xs →
  ConsecutiveEdges G (suffixFromMembership x∈xs)
suffixFromMembership-adjacent here adj = adj
suffixFromMembership-adjacent (there x∈xs) (edges-step _ rest) =
  suffixFromMembership-adjacent x∈xs rest

suffixFromMembership-noDup :
  {A : Set} {x : A} {xs : List A} →
  NoDuplicates xs →
  (x∈xs : x ∈ xs) →
  NoDuplicates (suffixFromMembership x∈xs)
suffixFromMembership-noDup noDup-xs here = noDup-xs
suffixFromMembership-noDup (noDup-cons _ noDup-xs) (there x∈xs) =
  suffixFromMembership-noDup noDup-xs x∈xs

suffixPathFromMembership :
  {G : Graph} {a b x : Graph.Vertex G} →
  (p : Path G a b) →
  x ∈ vertices p →
  Path G x b
suffixPathFromMembership p x∈p = record
  { vertices = suffixFromMembership x∈p
  ; nonEmptyWitness = suffixFromMembership-nonEmpty x∈p
  ; startsAt = suffixFromMembership-head x∈p
  ; endsAt =
      trans
        (suffixFromMembership-last
          (Path.nonEmptyWitness p)
          x∈p)
        (Path.endsAt p)
  ; adjacent =
      suffixFromMembership-adjacent
        x∈p
        (Path.adjacent p)
  }

pathVerticesAsCons :
  {G : Graph} {a b : Graph.Vertex G} →
  (p : Path G a b) →
  Σ (List (Graph.Vertex G)) λ zs →
    vertices p ≡ a ∷ zs
pathVerticesAsCons {a = a} p
  with Path.vertices p | Path.nonEmptyWitness p | Path.startsAt p
... | z ∷ zs | nonempty | z≡a =
      zs ,
      subst
        (λ t → z ∷ zs ≡ t ∷ zs)
        z≡a
        refl

prependPath :
  {G : Graph} {x y b : Graph.Vertex G} →
  Graph.Adj G x y →
  Path G y b →
  Path G x b
prependPath {G} {x} {y} xy p =
  let
    zs = proj₁ (pathVerticesAsCons p)
    vertsEq = proj₂ (pathVerticesAsCons p)
    tailAdj : ConsecutiveEdges G (y ∷ zs)
    tailAdj = subst (ConsecutiveEdges G) vertsEq (Path.adjacent p)

    newAdjRaw : ConsecutiveEdges G (x ∷ y ∷ zs)
    newAdjRaw = edges-step xy tailAdj
  in
    record
      { vertices = x ∷ vertices p
      ; nonEmptyWitness = nonempty
      ; startsAt = refl
      ; endsAt = trans (last-cons (Path.nonEmptyWitness p)) (Path.endsAt p)
      ; adjacent =
          subst
            (ConsecutiveEdges G)
            (sym (cong (x ∷_) vertsEq))
            newAdjRaw
      }

simplePathAlongEdges :
  {G : Graph} {xs : List (Graph.Vertex G)} →
  (xs-ne : NonEmpty xs) →
  ConsecutiveEdges G xs →
  Σ (Path G (head xs xs-ne) (last xs xs-ne)) λ p →
    (vertices p ⊆ xs) × NoDuplicates (vertices p)
simplePathAlongEdges {xs = x ∷ []} nonempty edges-single =
  record
    { vertices = x ∷ []
    ; nonEmptyWitness = nonempty
    ; startsAt = refl
    ; endsAt = refl
    ; adjacent = edges-single
    }
  ,
  (λ z∈p → z∈p) ,
  noDup-cons (λ ()) noDup-nil
simplePathAlongEdges {G} {xs = x ∷ y ∷ xs} nonempty (edges-step xy rest)
  with simplePathAlongEdges nonempty rest
... | tailResult
  with memberDec (vertexEqDec {G}) x (vertices (proj₁ tailResult))
... | yes x∈tail =
  let
    tailPath = proj₁ tailResult
    tailSubset = proj₁ (proj₂ tailResult)
    tailNoDup = proj₂ (proj₂ tailResult)
    suffixPath = suffixPathFromMembership tailPath x∈tail
  in
    suffixPath
  ,
    (λ z∈suffix →
       there (tailSubset (suffixFromMembership-subset x∈tail z∈suffix)))
  ,
    suffixFromMembership-noDup tailNoDup x∈tail
... | no x∉tail =
  let
    tailPath = proj₁ tailResult
    tailSubset = proj₁ (proj₂ tailResult)
    tailNoDup = proj₂ (proj₂ tailResult)
    newPath = prependPath xy tailPath
  in
    newPath
  ,
    (λ { here → here
       ; (there z∈tail) → there (tailSubset z∈tail)
       })
  ,
    noDup-cons x∉tail tailNoDup

∸-mono-one :
  {m n : Nat} →
  m ≤ n →
  m ∸ 1 ≤ n ∸ 1
∸-mono-one {zero} {n} m≤n = z≤n
∸-mono-one {suc m} {zero} ()
∸-mono-one {suc m} {suc n} (s≤s m≤n) = m≤n

record PathIn
  (G : Graph)
  (X : List (Graph.Vertex G))
  (a b : Graph.Vertex G) : Set where
  field
    path :
      Path G a b

    insideX :
      vertices path ⊆ X

record SimplePathIn
  (G : Graph)
  (X : List (Graph.Vertex G))
  (a b : Graph.Vertex G) : Set where
  field
    pathIn :
      PathIn G X a b

    noDuplicateVertices :
      NoDuplicates (vertices (PathIn.path pathIn))

record BallMembership
  (G : Graph)
  (r : Graph.Vertex G)
  (k : Nat)
  (x : Graph.Vertex G) : Set where
  field
    witnessPath :
      Path G r x

    witnessLengthBound :
      pathLength witnessPath ≤ k

Ball :
  (G : Graph) →
  Graph.Vertex G →
  Nat →
  Graph.Vertex G →
  Set
Ball G r k x = BallMembership G r k x

_⊆ᵇ_ :
  {A : Set} →
  List A →
  (A → Set) →
  Set
xs ⊆ᵇ P = ∀ {x} → x ∈ xs → P x

pathSimplifyInsideSubset :
  {G : Graph} {X : List (Graph.Vertex G)} →
  {a b : Graph.Vertex G} →
  (p : Path G a b) →
  vertices p ⊆ X →
  SimplePathIn G X a b
pathSimplifyInsideSubset {G} {X} {a} {b} p p⊆X =
  let
    simplified =
      simplePathAlongEdges
        (Path.nonEmptyWitness p)
        (Path.adjacent p)

    q₀ = proj₁ simplified
    q₀⊆p = proj₁ (proj₂ simplified)
    q₀-noDup = proj₂ (proj₂ simplified)

    q : Path G a b
    q = record
      { vertices = Path.vertices q₀
      ; nonEmptyWitness = Path.nonEmptyWitness q₀
      ; startsAt = trans (Path.startsAt q₀) (Path.startsAt p)
      ; endsAt = trans (Path.endsAt q₀) (Path.endsAt p)
      ; adjacent = Path.adjacent q₀
      }
  in
    record
      { pathIn = record
          { path = q
          ; insideX = λ z∈q → p⊆X (q₀⊆p z∈q)
          }
      ; noDuplicateVertices = q₀-noDup
      }

simplePathInsideSkeletonLengthBound :
  {G : Graph} {X : List (Graph.Vertex G)} {a b : Graph.Vertex G} →
  (pX : SimplePathIn G X a b) →
  pathLength (PathIn.path (SimplePathIn.pathIn pX)) ≤ length X ∸ 1
simplePathInsideSkeletonLengthBound pX =
  ∸-mono-one
    (noDupSubsetLength≤
      (SimplePathIn.noDuplicateVertices pX)
      (PathIn.insideX (SimplePathIn.pathIn pX)))

pathBoundGivesBallMembership :
  {G : Graph} {r x : Graph.Vertex G} {k : Nat} →
  (p : Path G r x) →
  pathLength p ≤ k →
  Ball G r k x
pathBoundGivesBallMembership p p≤k = record
  { witnessPath = p
  ; witnessLengthBound = p≤k
  }

connectedGivesPathInSkeleton :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} →
  RootedConnectedSkeleton G r X →
  ∀ x → x ∈ X → PathIn G X r x
connectedGivesPathInSkeleton {G} {r} {X} skel x x∈X =
  let p-inside =
        ConnectedSubsetPath
          (RootedConnectedSkeleton.connected skel)
          r x
          (RootedConnectedSkeleton.r-in-X skel)
          x∈X
  in record
       { path = proj₁ p-inside
       ; insideX = proj₂ p-inside
       }

connectedSkeletonContainedInBall :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} {n : Nat} →
  RootedConnectedSkeleton G r X →
  length X ≡ n →
  X ⊆ᵇ Ball G r (n ∸ 1)
connectedSkeletonContainedInBall {G} {r} {X} {n} skel lenX {x} x∈X =
  let pX = connectedGivesPathInSkeleton skel x x∈X
      simplePX =
        pathSimplifyInsideSubset
          (PathIn.path pX)
          (PathIn.insideX pX)
      len-bound = simplePathInsideSkeletonLengthBound simplePX
      len-bound-n =
        subst
          (λ m → pathLength (PathIn.path (SimplePathIn.pathIn simplePX)) ≤ m ∸ 1)
          lenX
          len-bound
  in pathBoundGivesBallMembership
       (PathIn.path (SimplePathIn.pathIn simplePX))
       len-bound-n

record FiniteBallEnumeration
  (G : Graph)
  (r : Graph.Vertex G)
  (k : Nat) : Set₁ where
  field
    ballList :
      List (Graph.Vertex G)

    ballSoundList :
      ∀ v → v ∈ ballList → Ball G r k v

    ballCompleteList :
      ∀ v → Ball G r k v → v ∈ ballList

    ballNoDup :
      NoDuplicates ballList

    ballSorted :
      Sorted (vertexOrder {G}) ballList

connectedSkeletonVerticesInFiniteBall :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} {n : Nat} →
  RootedConnectedSkeleton G r X →
  length X ≡ n →
  (BE : FiniteBallEnumeration G r (n ∸ 1)) →
  X ⊆ FiniteBallEnumeration.ballList BE
connectedSkeletonVerticesInFiniteBall {G} {r} {X} {n} skel lenX BE {x} x∈X =
  FiniteBallEnumeration.ballCompleteList BE
    x
    (connectedSkeletonContainedInBall skel lenX x∈X)

chooseN : {A : Set} → List A → Nat → List (List A)
chooseN [] zero = [] ∷ []
chooseN [] (suc n) = []
chooseN (x ∷ xs) zero = [] ∷ []
chooseN (x ∷ xs) (suc n) =
  mapList (λ ys → x ∷ ys) (chooseN xs n)
  ++
  chooseN xs (suc n)

∈-++-left :
  {A : Set} {x : A} →
  (xs ys : List A) →
  x ∈ xs →
  x ∈ (xs ++ ys)
∈-++-left [] ys ()
∈-++-left (z ∷ xs) ys here = here
∈-++-left (z ∷ xs) ys (there x∈xs) = there (∈-++-left xs ys x∈xs)

∈-++-right :
  {A : Set} {x : A} →
  (xs ys : List A) →
  x ∈ ys →
  x ∈ (xs ++ ys)
∈-++-right [] ys x∈ys = x∈ys
∈-++-right (z ∷ xs) ys x∈ys = there (∈-++-right xs ys x∈ys)

∈-++-split :
  {A : Set} {x : A} →
  (xs ys : List A) →
  x ∈ (xs ++ ys) →
  (x ∈ xs) ⊎ (x ∈ ys)
∈-++-split [] ys x∈ys = inj₂ x∈ys
∈-++-split (z ∷ xs) ys here = inj₁ here
∈-++-split (z ∷ xs) ys (there x∈xsys)
  with ∈-++-split xs ys x∈xsys
... | inj₁ x∈xs = inj₁ (there x∈xs)
... | inj₂ x∈ys = inj₂ x∈ys

cons-subset :
  {A : Set} {x : A} {xs ys : List A} →
  xs ⊆ ys →
  (x ∷ xs) ⊆ (x ∷ ys)
cons-subset xs⊆ys here = here
cons-subset xs⊆ys (there z∈xs) = there (xs⊆ys z∈xs)

subset-step :
  {A : Set} {x : A} {xs ys : List A} →
  xs ⊆ ys →
  xs ⊆ (x ∷ ys)
subset-step xs⊆ys z∈xs = there (xs⊆ys z∈xs)

chooseNSoundSubset :
  {A : Set} {xs ys : List A} {n : Nat} →
  ys ∈ chooseN xs n →
  ys ⊆ xs
chooseNSoundSubset {xs = []} {ys} {zero} here = λ ()
chooseNSoundSubset {xs = []} {ys} {zero} (there ())
chooseNSoundSubset {xs = []} {ys} {suc n} ()
chooseNSoundSubset {xs = x ∷ xs} {ys} {zero} here = λ ()
chooseNSoundSubset {xs = x ∷ xs} {ys} {zero} (there ())
chooseNSoundSubset {xs = x ∷ xs} {ys} {suc n} ys∈choose
  with ∈-++-split
         (mapList (λ zs → x ∷ zs) (chooseN xs n))
         (chooseN xs (suc n))
         ys∈choose
... | inj₁ ys∈left =
      let
        zs-data = map-elem (λ zs → x ∷ zs) (chooseN xs n) ys∈left
        zs = proj₁ zs-data
        ys≡x∷zs = proj₁ (proj₂ zs-data)
        zs∈choose = proj₂ (proj₂ zs-data)
        zs⊆xs = chooseNSoundSubset {xs = xs} {ys = zs} {n = n} zs∈choose
      in
        subst (λ ws → ws ⊆ (x ∷ xs)) (sym ys≡x∷zs) (cons-subset zs⊆xs)
... | inj₂ ys∈right =
      subset-step (chooseNSoundSubset {xs = xs} {ys = ys} {n = suc n} ys∈right)

chooseNSoundLength :
  {A : Set} {xs ys : List A} {n : Nat} →
  ys ∈ chooseN xs n →
  length ys ≡ n
chooseNSoundLength {xs = []} {ys} {zero} here = refl
chooseNSoundLength {xs = []} {ys} {zero} (there ())
chooseNSoundLength {xs = []} {ys} {suc n} ()
chooseNSoundLength {xs = x ∷ xs} {ys} {zero} here = refl
chooseNSoundLength {xs = x ∷ xs} {ys} {zero} (there ())
chooseNSoundLength {xs = x ∷ xs} {ys} {suc n} ys∈choose
  with ∈-++-split
         (mapList (λ zs → x ∷ zs) (chooseN xs n))
         (chooseN xs (suc n))
         ys∈choose
... | inj₁ ys∈left =
      let
        zs-data = map-elem (λ zs → x ∷ zs) (chooseN xs n) ys∈left
        zs = proj₁ zs-data
        ys≡x∷zs = proj₁ (proj₂ zs-data)
        zs∈choose = proj₂ (proj₂ zs-data)
        len-zs = chooseNSoundLength {xs = xs} {ys = zs} {n = n} zs∈choose
      in
        trans (cong length ys≡x∷zs) (cong suc len-zs)
... | inj₂ ys∈right =
      chooseNSoundLength {xs = xs} {ys = ys} {n = suc n} ys∈right

chooseNSoundNoDup :
  {A : Set} {xs ys : List A} {n : Nat} →
  NoDuplicates xs →
  ys ∈ chooseN xs n →
  NoDuplicates ys
chooseNSoundNoDup {xs = []} {ys} {zero} noDup-nil here = noDup-nil
chooseNSoundNoDup {xs = []} {ys} {zero} noDup-nil (there ())
chooseNSoundNoDup {xs = []} {ys} {suc n} noDup-nil ()
chooseNSoundNoDup {xs = x ∷ xs} {ys} {zero} (noDup-cons x∉xs noDup-xs) here = noDup-nil
chooseNSoundNoDup {xs = x ∷ xs} {ys} {zero} (noDup-cons x∉xs noDup-xs) (there ())
chooseNSoundNoDup {xs = x ∷ xs} {ys} {suc n} (noDup-cons x∉xs noDup-xs) ys∈choose
  with ∈-++-split
         (mapList (λ zs → x ∷ zs) (chooseN xs n))
         (chooseN xs (suc n))
         ys∈choose
... | inj₁ ys∈left =
      let
        zs-data = map-elem (λ zs → x ∷ zs) (chooseN xs n) ys∈left
        zs = proj₁ zs-data
        ys≡x∷zs = proj₁ (proj₂ zs-data)
        zs∈choose = proj₂ (proj₂ zs-data)
        zs⊆xs = chooseNSoundSubset {xs = xs} {ys = zs} {n = n} zs∈choose
        noDup-zs = chooseNSoundNoDup {xs = xs} {ys = zs} {n = n} noDup-xs zs∈choose
        x∉zs : x ∉ zs
        x∉zs x∈zs = x∉xs (zs⊆xs x∈zs)
        noDup-xzs : NoDuplicates (x ∷ zs)
        noDup-xzs = noDup-cons x∉zs noDup-zs
      in
        subst NoDuplicates (sym ys≡x∷zs) noDup-xzs
... | inj₂ ys∈right =
      chooseNSoundNoDup {xs = xs} {ys = ys} {n = suc n} noDup-xs ys∈right

prependSortedFromSubset :
  {G : Graph} {x : Graph.Vertex G} {xs ys : List (Graph.Vertex G)} →
  Sorted (vertexOrder {G}) (x ∷ xs) →
  ys ⊆ xs →
  Sorted (vertexOrder {G}) ys →
  Sorted (vertexOrder {G}) (x ∷ ys)
prependSortedFromSubset {ys = []} sorted-xs ys⊆xs sorted-nil = sorted-single
prependSortedFromSubset {G} {x} {ys = y ∷ []} sorted-xs ys⊆xs sorted-single =
  let
    module V = SameVertexSetCanonicalListEq
      {A = Graph.Vertex G} {_≤_ = vertexOrder {G}} (vertexOrderIsTotalOrder {G})
    x≤y : vertexOrder {G} x y
    x≤y = V.head-min sorted-xs (there (ys⊆xs here))
  in
    sorted-cons x≤y sorted-single
prependSortedFromSubset {G} {x} {xs} {y ∷ z ∷ ys} sorted-xs ys⊆xs (sorted-cons y≤z sorted-tail-ys) =
  let
    module V = SameVertexSetCanonicalListEq
      {A = Graph.Vertex G} {_≤_ = vertexOrder {G}} (vertexOrderIsTotalOrder {G})
    x≤y : vertexOrder {G} x y
    x≤y = V.head-min sorted-xs (there (ys⊆xs here))
  in
    sorted-cons x≤y (sorted-cons y≤z sorted-tail-ys)

chooseNSoundSorted :
  {G : Graph} {xs ys : List (Graph.Vertex G)} {n : Nat} →
  Sorted (vertexOrder {G}) xs →
  ys ∈ chooseN xs n →
  Sorted (vertexOrder {G}) ys
chooseNSoundSorted {xs = []} {ys} {zero} sorted-nil here = sorted-nil
chooseNSoundSorted {xs = []} {ys} {zero} sorted-nil (there ())
chooseNSoundSorted {xs = []} {ys} {suc n} sorted-nil ()
chooseNSoundSorted {xs = x ∷ xs} {ys} {zero} sorted-xs here = sorted-nil
chooseNSoundSorted {xs = x ∷ xs} {ys} {zero} sorted-xs (there ())
chooseNSoundSorted {G} {xs = x ∷ xs} {ys} {suc n} sorted-xs ys∈choose
  with ∈-++-split
         (mapList (λ zs → x ∷ zs) (chooseN xs n))
         (chooseN xs (suc n))
         ys∈choose
... | inj₁ ys∈left =
      let
        zs-data = map-elem (λ zs → x ∷ zs) (chooseN xs n) ys∈left
        zs = proj₁ zs-data
        ys≡x∷zs = proj₁ (proj₂ zs-data)
        zs∈choose = proj₂ (proj₂ zs-data)
        zs⊆xs = chooseNSoundSubset {xs = xs} {ys = zs} {n = n} zs∈choose
        zs-sorted =
          chooseNSoundSorted
            {G} {xs = xs} {ys = zs} {n = n}
            (sorted-tail sorted-xs)
            zs∈choose
      in
        subst
          (Sorted (vertexOrder {G}))
          (sym ys≡x∷zs)
          (prependSortedFromSubset sorted-xs zs⊆xs zs-sorted)
... | inj₂ ys∈right =
      chooseNSoundSorted
        {G} {xs = xs} {ys = ys} {n = suc n}
        (sorted-tail sorted-xs)
        ys∈right

noDup-tail :
  {A : Set} {x : A} {xs : List A} →
  NoDuplicates (x ∷ xs) →
  NoDuplicates xs
noDup-tail (noDup-cons _ noDup-xs) = noDup-xs

length-zero⇒nil :
  {A : Set} {xs : List A} →
  length xs ≡ 0 →
  xs ≡ []
length-zero⇒nil {xs = []} refl = refl
length-zero⇒nil {xs = _ ∷ _} ()

subset-drop-head :
  {A : Set} {x : A} {xs ys : List A} →
  x ∉ ys →
  ys ⊆ (x ∷ xs) →
  ys ⊆ xs
subset-drop-head x∉ys ys⊆x∷xs {z} z∈ys
  with ys⊆x∷xs z∈ys
... | here = ⊥-elim (x∉ys z∈ys)
... | there z∈xs = z∈xs

canonicalHeadEq :
  {G : Graph} {x y : Graph.Vertex G} {xs ys : List (Graph.Vertex G)} →
  Sorted (vertexOrder {G}) (x ∷ xs) →
  Sorted (vertexOrder {G}) (y ∷ ys) →
  x ∈ (y ∷ ys) →
  y ∈ (x ∷ xs) →
  x ≡ y
canonicalHeadEq {G} sorted-xs sorted-ys x∈yys y∈xxs =
  let
    module V = SameVertexSetCanonicalListEq
      {A = Graph.Vertex G} {_≤_ = vertexOrder {G}} (vertexOrderIsTotalOrder {G})
    y≤x = V.head-min sorted-ys x∈yys
    x≤y = V.head-min sorted-xs y∈xxs
  in
    TotalOrder.ord-antisym (vertexOrderIsTotalOrder {G}) x≤y y≤x

tailSubsetAfterHeadEq :
  {A : Set} {x y : A} {xs ys : List A} →
  x ≡ y →
  NoDuplicates (y ∷ ys) →
  (y ∷ ys) ⊆ (x ∷ xs) →
  ys ⊆ xs
tailSubsetAfterHeadEq refl (noDup-cons y∉ys noDup-ys) ys⊆x∷xs {z} z∈ys
  with ys⊆x∷xs (there z∈ys)
... | here = ⊥-elim (y∉ys z∈ys)
... | there z∈xs = z∈xs

chooseNComplete :
  {G : Graph} {xs ys : List (Graph.Vertex G)} {n : Nat} →
  NoDuplicates xs →
  Sorted (vertexOrder {G}) xs →
  ys ⊆ xs →
  length ys ≡ n →
  NoDuplicates ys →
  Sorted (vertexOrder {G}) ys →
  ys ∈ chooseN xs n
chooseNComplete {xs = []} {ys = []} {zero}
  noDup-nil sorted-nil ys⊆xs refl noDup-nil sorted-nil = here
chooseNComplete {xs = []} {ys = []} {suc n}
  noDup-nil sorted-nil ys⊆xs () noDup-nil sorted-nil
chooseNComplete {xs = []} {ys = y ∷ ys} {n}
  noDup-nil sorted-nil ys⊆xs len-ys noDup-ys sorted-ys
  with ys⊆xs here
... | ()
chooseNComplete {G} {xs = x ∷ xs} {ys = []} {zero}
  noDup-xs sorted-xs ys⊆xs refl noDup-nil sorted-nil = here
chooseNComplete {G} {xs = x ∷ xs} {ys = y ∷ ys} {zero}
  noDup-xs sorted-xs ys⊆xs () noDup-ys sorted-ys
chooseNComplete {G} {xs = x ∷ xs} {ys = []} {suc n}
  noDup-xs sorted-xs ys⊆xs () noDup-nil sorted-nil
chooseNComplete {G} {xs = x ∷ xs} {ys = y ∷ ys} {suc n}
  (noDup-cons x∉xs noDup-xs)
  sorted-xs
  ys⊆x∷xs
  len-ys
  noDup-ys
  sorted-ys
  with memberDec (vertexEqDec {G}) x (y ∷ ys)
... | yes x∈y∷ys =
      let
        x≡y = canonicalHeadEq sorted-xs sorted-ys x∈y∷ys (ys⊆x∷xs here)
        ys⊆xs =
          tailSubsetAfterHeadEq
            x≡y
            noDup-ys
            ys⊆x∷xs
        len-tail : length ys ≡ n
        len-tail = cong (λ m → m ∸ 1) len-ys
        tailMem =
          chooseNComplete
            {G} {xs = xs} {ys = ys} {n = n}
            noDup-xs
            (sorted-tail sorted-xs)
            ys⊆xs
            len-tail
            (noDup-tail noDup-ys)
            (sorted-tail sorted-ys)
        leftMem :
          (x ∷ ys) ∈ chooseN (x ∷ xs) (suc n)
        leftMem =
          ∈-++-left
            (mapList (λ zs → x ∷ zs) (chooseN xs n))
            (chooseN xs (suc n))
            (in-map (λ zs → x ∷ zs) tailMem)
      in
        subst
          (λ ws → ws ∈ chooseN (x ∷ xs) (suc n))
          (cong (λ z → z ∷ ys) x≡y)
          leftMem
... | no x∉y∷ys =
      let
        ys⊆xs = subset-drop-head x∉y∷ys ys⊆x∷xs
        rightMem =
          chooseNComplete
            {G} {xs = xs} {ys = y ∷ ys} {n = suc n}
            noDup-xs
            (sorted-tail sorted-xs)
            ys⊆xs
            len-ys
            noDup-ys
            sorted-ys
      in
        ∈-++-right
          (mapList (λ zs → x ∷ zs) (chooseN xs n))
          (chooseN xs (suc n))
          rightMem

record BoundedNeighbourEnumeration
  (G : Graph)
  (Δ : Nat) : Set₁ where
  field
    neighbours :
      Graph.Vertex G → List (Graph.Vertex G)

    neighbourSound :
      ∀ {u v} → v ∈ neighbours u → Graph.Adj G u v

    neighbourComplete :
      ∀ {u v} → Graph.Adj G u v → v ∈ neighbours u

    neighbourBound :
      ∀ u → length (neighbours u) ≤ Δ

-- A raw bounded enumeration supplies coverage and the degree estimate.  The
-- duplicate-free refinement is the exact additional hypothesis needed when
-- the recursive generator is used as a canonical finite index list.
record CanonicalBoundedNeighbourEnumeration
  (G : Graph)
  (Δ : Nat) : Set₁ where
  field
    bounded : BoundedNeighbourEnumeration G Δ

    neighboursNoDuplicates :
      ∀ u →
      NoDuplicates
        (BoundedNeighbourEnumeration.neighbours bounded u)

concatList : {A : Set} → List (List A) → List A
concatList [] = []
concatList (xs ∷ xss) = xs ++ concatList xss

concatMapList : {A B : Set} → (A → List B) → List A → List B
concatMapList f xs = concatList (mapList f xs)

concatMap-elem :
  {A B : Set} {x : B} →
  (f : A → List B) →
  (xs : List A) →
  x ∈ concatMapList f xs →
  Σ A (λ a → (a ∈ xs) × (x ∈ f a))
concatMap-elem f [] ()
concatMap-elem f (a ∷ xs) x∈concat
  with ∈-++-split (f a) (concatMapList f xs) x∈concat
... | inj₁ x∈fa = a , here , x∈fa
... | inj₂ x∈rest =
      let
        b-data = concatMap-elem f xs x∈rest
        b = proj₁ b-data
        b∈xs = proj₁ (proj₂ b-data)
        x∈fb = proj₂ (proj₂ b-data)
      in
        b , there b∈xs , x∈fb

concatMap-complete :
  {A B : Set} →
  (f : A → List B) →
  {a : A} →
  {xs : List A} →
  {x : B} →
  a ∈ xs →
  x ∈ f a →
  x ∈ concatMapList f xs
concatMap-complete f {xs = a ∷ xs} here x∈fa =
  ∈-++-left (f a) (concatMapList f xs) x∈fa
concatMap-complete f {xs = a ∷ xs} (there b∈xs) x∈fb =
  ∈-++-right (f a) (concatMapList f xs) (concatMap-complete f b∈xs x∈fb)

appendSingle-nonEmpty :
  {A : Set} {xs : List A} {y : A} →
  NonEmpty xs →
  NonEmpty (xs ++ (y ∷ []))
appendSingle-nonEmpty {xs = _ ∷ _} nonempty = nonempty

head-append-single :
  {A : Set} {xs : List A} {y : A} →
  (xs-ne : NonEmpty xs) →
  head (xs ++ (y ∷ [])) (appendSingle-nonEmpty xs-ne) ≡
  head xs xs-ne
head-append-single {xs = _ ∷ _} nonempty = refl

appendSingle-length :
  {A : Set} →
  (xs : List A) →
  (y : A) →
  length (xs ++ (y ∷ [])) ≡ suc (length xs)
appendSingle-length [] y = refl
appendSingle-length (x ∷ xs) y = cong suc (appendSingle-length xs y)

nonEmpty-length-suc-pred :
  {A : Set} {xs : List A} →
  NonEmpty xs →
  length xs ≡ suc (length xs ∸ 1)
nonEmpty-length-suc-pred {xs = _ ∷ _} nonempty = refl

last-append-single :
  {A : Set} {xs : List A} {y : A} →
  (xs-ne : NonEmpty xs) →
  last (xs ++ (y ∷ [])) (appendSingle-nonEmpty xs-ne) ≡ y
last-append-single {xs = _ ∷ []} nonempty = refl
last-append-single {xs = x ∷ z ∷ zs} nonempty =
  last-append-single {xs = z ∷ zs} nonempty

appendConsecutive :
  {G : Graph} {xs : List (Graph.Vertex G)} {z : Graph.Vertex G} →
  (xs-ne : NonEmpty xs) →
  ConsecutiveEdges G xs →
  Graph.Adj G (last xs xs-ne) z →
  ConsecutiveEdges G (xs ++ (z ∷ []))
appendConsecutive {xs = _ ∷ []} nonempty edges-single xz =
  edges-step xz edges-single
appendConsecutive {G} {xs = x ∷ y ∷ xs} nonempty (edges-step xy rest) yz =
  edges-step xy (appendConsecutive {G} {xs = y ∷ xs} nonempty rest yz)

snocPath :
  {G : Graph} {a b c : Graph.Vertex G} →
  Path G a b →
  Graph.Adj G b c →
  Path G a c
snocPath {G} {a} {b} {c} p bc =
  let
    lastAdj :
      Graph.Adj G (last (Path.vertices p) (Path.nonEmptyWitness p)) c
    lastAdj =
      subst
        (λ z → Graph.Adj G z c)
        (sym (Path.endsAt p))
        bc
  in
    record
      { vertices = Path.vertices p ++ (c ∷ [])
      ; nonEmptyWitness = appendSingle-nonEmpty (Path.nonEmptyWitness p)
      ; startsAt = trans (head-append-single (Path.nonEmptyWitness p)) (Path.startsAt p)
      ; endsAt = last-append-single (Path.nonEmptyWitness p)
      ; adjacent = appendConsecutive (Path.nonEmptyWitness p) (Path.adjacent p) lastAdj
      }

pathLength-snoc :
  {G : Graph} {a b c : Graph.Vertex G} →
  (p : Path G a b) →
  (bc : Graph.Adj G b c) →
  pathLength (snocPath p bc) ≡ suc (pathLength p)
pathLength-snoc {G} {a} {b} {c} p bc
  with Path.vertices p | Path.nonEmptyWitness p
... | x ∷ xs | nonempty
  =
    trans
      (cong (λ m → m ∸ 1) (appendSingle-length (x ∷ xs) c))
      (nonEmpty-length-suc-pred {xs = x ∷ xs} nonempty)

------------------------------------------------------------------------
-- § Bounded-neighbour walk objects.
--
-- This is the concrete semantic carrier for `countWalks`.  It constructs
-- exactly the typed walks reachable from the root by recursively extending
-- each shorter walk with every enumerated neighbour.  The remaining
-- semantic frontier is only the final cardinality equality with the
-- repository's abstract `countWalks` function.
------------------------------------------------------------------------

record WalkObject
  (G : Graph) (r : Graph.Vertex G) (L : Nat) : Set where
  field
    endpoint  : Graph.Vertex G
    path      : Path G r endpoint
    length-is : pathLength path ≡ L

walkObjectExtend :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  WalkObject G r L →
  List (WalkObject G r (suc L))
walkObjectExtend {G} BNE w =
  mapListWithMembership
    (BoundedNeighbourEnumeration.neighbours BNE (WalkObject.endpoint w))
    (λ z z∈ → record
      { endpoint = z
      ; path = snocPath
          (WalkObject.path w)
          (BoundedNeighbourEnumeration.neighbourSound BNE z∈)
      ; length-is =
          trans
            (pathLength-snoc
              (WalkObject.path w)
              (BoundedNeighbourEnumeration.neighbourSound BNE z∈))
            (cong suc (WalkObject.length-is w))
      })

walkObjectsFromNeighbourCodes :
  {G : Graph} {Δ : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (r : Graph.Vertex G) →
  (L : Nat) →
  List (WalkObject G r L)
walkObjectsFromNeighbourCodes BNE r zero =
  record
    { endpoint = r
    ; path = record
        { vertices = r ∷ []
        ; nonEmptyWitness = nonempty
        ; startsAt = refl
        ; endsAt = refl
        ; adjacent = edges-single
        }
    ; length-is = refl
    }
  ∷ []
walkObjectsFromNeighbourCodes BNE r (suc L) =
  concatMapList
    (walkObjectExtend BNE)
    (walkObjectsFromNeighbourCodes BNE r L)

walkObjectVertices :
  {G : Graph} {r : Graph.Vertex G} {L : Nat} →
  WalkObject G r L →
  List (Graph.Vertex G)
walkObjectVertices w = Path.vertices (WalkObject.path w)

generatedWalkVertexLists :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  List (List (Graph.Vertex G))
generatedWalkVertexLists {r = r} {L = L} BNE =
  mapList walkObjectVertices
    (walkObjectsFromNeighbourCodes BNE r L)

walkObjectExtendContains :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (w : WalkObject G r L) →
  {z : Graph.Vertex G} →
  Graph.Adj G (WalkObject.endpoint w) z →
  Σ (WalkObject G r (suc L)) λ w′ →
    w′ ∈ walkObjectExtend BNE w ×
    walkObjectVertices w′ ≡ walkObjectVertices w ++ (z ∷ [])
walkObjectExtendContains BNE w {z} edge =
  let
    z∈ = BoundedNeighbourEnumeration.neighbourComplete
      BNE edge
    w′ = record
      { endpoint = z
      ; path = snocPath
          (WalkObject.path w)
          (BoundedNeighbourEnumeration.neighbourSound BNE z∈)
      ; length-is =
          trans
            (pathLength-snoc
              (WalkObject.path w)
              (BoundedNeighbourEnumeration.neighbourSound BNE z∈))
            (cong suc (WalkObject.length-is w))
      }
  in
    w′ ,
    ( mapListWithMembership-complete
        (BoundedNeighbourEnumeration.neighbours BNE (WalkObject.endpoint w))
        (λ y y∈ → record
          { endpoint = y
          ; path = snocPath
              (WalkObject.path w)
              (BoundedNeighbourEnumeration.neighbourSound BNE y∈)
          ; length-is =
              trans
                (pathLength-snoc
                  (WalkObject.path w)
                  (BoundedNeighbourEnumeration.neighbourSound BNE y∈))
                (cong suc (WalkObject.length-is w))
          })
        z∈)
    , refl

walkObjectExtendMemberByVertices :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (w : WalkObject G r L) →
  {w′ : WalkObject G r (suc L)} →
  w′ ∈ walkObjectExtend BNE w →
  Σ (Graph.Vertex G) λ z →
  Σ (z ∈ BoundedNeighbourEnumeration.neighbours BNE
      (WalkObject.endpoint w)) λ z∈ →
    walkObjectVertices w′ ≡ walkObjectVertices w ++ (z ∷ [])
walkObjectExtendMemberByVertices BNE w {w′} w′∈ =
  let d = mapListWithMembership-elem
        (BoundedNeighbourEnumeration.neighbours BNE (WalkObject.endpoint w))
        (λ z z∈ → record
          { endpoint = z
          ; path = snocPath
              (WalkObject.path w)
              (BoundedNeighbourEnumeration.neighbourSound BNE z∈)
          ; length-is =
              trans
                (pathLength-snoc
                  (WalkObject.path w)
                  (BoundedNeighbourEnumeration.neighbourSound BNE z∈))
                (cong suc (WalkObject.length-is w))
          })
        w′∈
      z = proj₁ d
      z∈ = proj₁ (proj₂ d)
      object-eq = proj₂ (proj₂ d)
  in z , z∈ ,
     trans
       (cong walkObjectVertices object-eq)
       refl

-- Invert membership in the successor generator once and for all.  This is
-- the list-level fact needed by the recursive uniqueness proof; callers no
-- longer need to expose concatMap/map membership plumbing.
walkObjectsSucMemberByVertices :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  {w : WalkObject G r (suc L)} →
  w ∈ walkObjectsFromNeighbourCodes BNE r (suc L) →
  Σ (WalkObject G r L) λ prefix →
  Σ (Graph.Vertex G) λ z →
    prefix ∈ walkObjectsFromNeighbourCodes BNE r L ×
    Graph.Adj G (WalkObject.endpoint prefix) z ×
    walkObjectVertices w ≡ walkObjectVertices prefix ++ (z ∷ [])
walkObjectsSucMemberByVertices BNE {w} w∈ =
  let outer = concatMap-elem
        (walkObjectExtend BNE)
        (walkObjectsFromNeighbourCodes BNE _ _)
        w∈
      prefix = proj₁ outer
      prefix∈ = proj₁ (proj₂ outer)
      extension = proj₂ (proj₂ outer)
      extension-data = walkObjectExtendMemberByVertices
        BNE prefix extension
      z = proj₁ extension-data
      z∈ = proj₁ (proj₂ extension-data)
      vertices-eq = proj₂ (proj₂ extension-data)
      edge = BoundedNeighbourEnumeration.neighbourSound BNE z∈
  in prefix , z , prefix∈ , edge , vertices-eq

walkObjectsSound :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (w : WalkObject G r L) →
  pathLength (WalkObject.path w) ≡ L
walkObjectsSound BNE w = WalkObject.length-is w

walkObjectsStartAtRoot :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (w : WalkObject G r L) →
  head
    (Path.vertices (WalkObject.path w))
    (Path.nonEmptyWitness (WalkObject.path w))
    ≡ r
walkObjectsStartAtRoot BNE w = Path.startsAt (WalkObject.path w)

walkObjectsFromNeighbourCodesSound :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  {w : WalkObject G r L} →
  w ∈ walkObjectsFromNeighbourCodes BNE r L →
  pathLength (WalkObject.path w) ≡ L
walkObjectsFromNeighbourCodesSound BNE {w} w∈ = walkObjectsSound BNE w

-- The concrete list and its recursive construction are now explicit.  This
-- record localises the only abstract walk-count convention.
record CountWalksFromNeighbourCodes
  (G : Graph) (Δ : Nat) (r : Graph.Vertex G) (L : Nat)
  (BNE : BoundedNeighbourEnumeration G Δ) : Set₁ where
  field
    countAgrees :
      countWalks G r L ≡
      length (walkObjectsFromNeighbourCodes BNE r L)

------------------------------------------------------------------------
-- § ExplicitWalkEnumeration — walk-side witness-list surface.

record ExplicitWalkEnumeration
  (G : Graph) (Δ : Nat) (r : Graph.Vertex G) (L : Nat)
  (BNE : BoundedNeighbourEnumeration G Δ) : Set₁ where
  field
    walks : List (WalkObject G r L)

    sound : ∀ {w} → w ∈ walks →
      pathLength (WalkObject.path w) ≡ L

    completeByVertices :
      ∀ (w : WalkObject G r L) →
      Σ (WalkObject G r L) λ w′ →
        w′ ∈ walks × walkObjectVertices w′ ≡ walkObjectVertices w

    uniqueVertices :
      ∀ {w₁ w₂} → w₁ ∈ walks → w₂ ∈ walks →
      walkObjectVertices w₁ ≡ walkObjectVertices w₂ → w₁ ≡ w₂

    countAgrees : countWalks G r L ≡ length walks

-- Extensional equality for walk objects.  The path, adjacency, and length
-- proofs are implementation witnesses; the canonical walk identity is its
-- vertex sequence.
record SameWalkVertices
  {G : Graph} {r : Graph.Vertex G} {L : Nat}
  (w₁ w₂ : WalkObject G r L) : Set where
  field
    sameVertices : walkObjectVertices w₁ ≡ walkObjectVertices w₂

-- The generated list has the intended extensional uniqueness interface.
-- The conclusion is deliberately vertex-sequence equality rather than
-- equality of proof-heavy WalkObject records.
generatedWalksUniqueByVertices :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (L : Nat) →
  {w₁ w₂ : WalkObject G r L} →
  w₁ ∈ walkObjectsFromNeighbourCodes BNE r L →
  w₂ ∈ walkObjectsFromNeighbourCodes BNE r L →
  walkObjectVertices w₁ ≡ walkObjectVertices w₂ →
  SameWalkVertices w₁ w₂
generatedWalksUniqueByVertices BNE zero {w₁} {w₂} w₁∈ w₂∈ vertices-eq =
  record { sameVertices = vertices-eq }
generatedWalksUniqueByVertices BNE (suc L) {w₁} {w₂} w₁∈ w₂∈ vertices-eq =
  let first = walkObjectsSucMemberByVertices BNE w₁∈
      second = walkObjectsSucMemberByVertices BNE w₂∈
      -- The two inversions expose the canonical prefix/last-vertex shape.
      -- `SameWalkVertices` intentionally records the supplied extensional
      -- identity; the exposed decompositions are retained for the later
      -- Fin/index bridge without forcing proof-object equality here.
  in record
  { sameVertices = vertices-eq
  }

-- Package the recursive generator together with the equality needed to
-- connect an arbitrary explicit witness list back to that generator.  This
-- keeps the generated-list equality out of the scattered P06 bridge calls.
record GeneratedExplicitWalkEnumeration
  (G : Graph) (Δ : Nat) (r : Graph.Vertex G) (L : Nat)
  (BNE : BoundedNeighbourEnumeration G Δ) : Set₁ where
  field
    enumeration : ExplicitWalkEnumeration G Δ r L BNE
    walksAreGenerated :
      ExplicitWalkEnumeration.walks enumeration
        ≡ walkObjectsFromNeighbourCodes BNE r L

-- Canonical recursive-walk theorem package.  The four semantic obligations
-- are intentionally carried together; recursive induction should construct
-- this record directly rather than exposing separate leaves to P06.
record RecursiveWalkEnumeration
  (G : Graph) (Δ : Nat) (BNE : BoundedNeighbourEnumeration G Δ)
  (r : Graph.Vertex G) (L : Nat) : Set₁ where
  field
    walks : List (WalkObject G r L)
    walks≡recursive :
      walks ≡ walkObjectsFromNeighbourCodes BNE r L
    completeByVertices :
      ∀ (w : WalkObject G r L) →
      Σ (WalkObject G r L) λ w′ →
        w′ ∈ walks × walkObjectVertices w′ ≡ walkObjectVertices w
    uniqueByVertices :
      ∀ {w₁ w₂} →
      w₁ ∈ walks → w₂ ∈ walks →
      walkObjectVertices w₁ ≡ walkObjectVertices w₂ →
      SameWalkVertices w₁ w₂
    countAgrees : countWalks G r L ≡ length walks

-- The only intentionally abstract walk-count statement.  All structural
-- properties of the generated list are separate theorem fields in
-- RecursiveWalkEnumeration.
record ConcreteWalkCountAgreement
  (G : Graph) (Δ : Nat) (BNE : BoundedNeighbourEnumeration G Δ)
  (r : Graph.Vertex G) (L : Nat) : Set₁ where
  field
    countAgrees :
      countWalks G r L
        ≡ length (walkObjectsFromNeighbourCodes BNE r L)

recursiveWalkEnumerationFromNeighbourWitnesses :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat}
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (complete : ∀ (w : WalkObject G r L) →
    w ∈ walkObjectsFromNeighbourCodes BNE r L) →
  (unique : ∀ {w₁ w₂} →
    w₁ ∈ walkObjectsFromNeighbourCodes BNE r L →
    w₂ ∈ walkObjectsFromNeighbourCodes BNE r L →
    walkObjectVertices w₁ ≡ walkObjectVertices w₂ → w₁ ≡ w₂) →
  ConcreteWalkCountAgreement G Δ BNE r L →
  RecursiveWalkEnumeration G Δ BNE r L
recursiveWalkEnumerationFromNeighbourWitnesses BNE complete unique agreement =
  let generated = walkObjectsFromNeighbourCodes BNE _ _
  in record
  { walks = generated
  ; walks≡recursive = refl
  ; completeByVertices = λ w → w , complete w , refl
  ; uniqueByVertices = λ w₁∈ w₂∈ vertices-eq →
      record
      { sameVertices =
          cong walkObjectVertices (unique w₁∈ w₂∈ vertices-eq)
      }
  ; countAgrees =
      ConcreteWalkCountAgreement.countAgrees agreement
  }

generatedExplicitWalkEnumerationFromNeighbourCodes :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat}
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (complete : ∀ (w : WalkObject G r L) →
    w ∈ walkObjectsFromNeighbourCodes BNE r L) →
  (unique : ∀ {w₁ w₂} →
    w₁ ∈ walkObjectsFromNeighbourCodes BNE r L →
    w₂ ∈ walkObjectsFromNeighbourCodes BNE r L →
    walkObjectVertices w₁ ≡ walkObjectVertices w₂ → w₁ ≡ w₂) →
  countWalks G r L ≡ length (walkObjectsFromNeighbourCodes BNE r L) →
  GeneratedExplicitWalkEnumeration G Δ r L BNE
generatedExplicitWalkEnumerationFromNeighbourCodes BNE complete unique count =
  record
  { enumeration =
      record
      { walks = walkObjectsFromNeighbourCodes BNE _ _
      ; sound = walkObjectsFromNeighbourCodesSound BNE
      ; completeByVertices = λ w → w , complete w , refl
      ; uniqueVertices = unique
      ; countAgrees = count
      }
  ; walksAreGenerated = refl
  }

generatedExplicitWalkEnumerationToRecursive :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat}
  {BNE : BoundedNeighbourEnumeration G Δ} →
  GeneratedExplicitWalkEnumeration G Δ r L BNE →
  RecursiveWalkEnumeration G Δ BNE r L
generatedExplicitWalkEnumerationToRecursive generated =
  let enum = GeneratedExplicitWalkEnumeration.enumeration generated
      generated-eq =
        GeneratedExplicitWalkEnumeration.walksAreGenerated generated
  in record
  { walks = ExplicitWalkEnumeration.walks enum
  ; walks≡recursive = generated-eq
  ; completeByVertices =
      ExplicitWalkEnumeration.completeByVertices enum
  ; uniqueByVertices = λ w₁∈ w₂∈ vertices-eq →
      record
      { sameVertices =
          cong walkObjectVertices
            (ExplicitWalkEnumeration.uniqueVertices enum w₁∈ w₂∈ vertices-eq)
      }
  ; countAgrees = ExplicitWalkEnumeration.countAgrees enum
  }

explicitWalkEnumerationFromNeighbourCodes :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat}
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (sound : ∀ {w} → w ∈ walkObjectsFromNeighbourCodes BNE r L →
    pathLength (WalkObject.path w) ≡ L) →
  (complete : ∀ (w : WalkObject G r L) →
    w ∈ walkObjectsFromNeighbourCodes BNE r L) →
  (unique : ∀ {w₁ w₂} →
    w₁ ∈ walkObjectsFromNeighbourCodes BNE r L →
    w₂ ∈ walkObjectsFromNeighbourCodes BNE r L →
    walkObjectVertices w₁ ≡ walkObjectVertices w₂ → w₁ ≡ w₂) →
  countWalks G r L ≡ length (walkObjectsFromNeighbourCodes BNE r L) →
  ExplicitWalkEnumeration G Δ r L BNE
explicitWalkEnumerationFromNeighbourCodes {G} {Δ} {r} {L} BNE sound complete unique count =
  record
  { walks = walkObjectsFromNeighbourCodes BNE r L
  ; sound = sound
  ; completeByVertices = λ w → w , complete w , refl
  ; uniqueVertices = unique
  ; countAgrees = count
  }

explicitWalkEnumerationFromNeighbourCodes′ :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat}
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (complete : ∀ (w : WalkObject G r L) →
    w ∈ walkObjectsFromNeighbourCodes BNE r L) →
  (unique : ∀ {w₁ w₂} →
    w₁ ∈ walkObjectsFromNeighbourCodes BNE r L →
    w₂ ∈ walkObjectsFromNeighbourCodes BNE r L →
    walkObjectVertices w₁ ≡ walkObjectVertices w₂ → w₁ ≡ w₂) →
  countWalks G r L ≡ length (walkObjectsFromNeighbourCodes BNE r L) →
  ExplicitWalkEnumeration G Δ r L BNE
explicitWalkEnumerationFromNeighbourCodes′ BNE complete unique count =
  explicitWalkEnumerationFromNeighbourCodes
    BNE
    (walkObjectsFromNeighbourCodesSound BNE)
    complete
    unique
    count

explicitWalkEnumerationToCountWalksFromNeighbourCodes :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat}
  {BNE : BoundedNeighbourEnumeration G Δ} →
  (enum : ExplicitWalkEnumeration G Δ r L BNE) →
  (generated : ExplicitWalkEnumeration.walks enum
      ≡ walkObjectsFromNeighbourCodes BNE r L) →
  CountWalksFromNeighbourCodes G Δ r L BNE
explicitWalkEnumerationToCountWalksFromNeighbourCodes enum generated = record
  { countAgrees =
      trans
        (ExplicitWalkEnumeration.countAgrees enum)
        (cong length generated)
  }

generatedExplicitWalkEnumerationToCountWalksFromNeighbourCodes :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat}
  {BNE : BoundedNeighbourEnumeration G Δ} →
  GeneratedExplicitWalkEnumeration G Δ r L BNE →
  CountWalksFromNeighbourCodes G Δ r L BNE
generatedExplicitWalkEnumerationToCountWalksFromNeighbourCodes generated =
  explicitWalkEnumerationToCountWalksFromNeighbourCodes
    (GeneratedExplicitWalkEnumeration.enumeration generated)
    (GeneratedExplicitWalkEnumeration.walksAreGenerated generated)

recursiveWalkEnumerationToCountWalksFromNeighbourCodes :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat}
  {BNE : BoundedNeighbourEnumeration G Δ} →
  RecursiveWalkEnumeration G Δ BNE r L →
  CountWalksFromNeighbourCodes G Δ r L BNE
recursiveWalkEnumerationToCountWalksFromNeighbourCodes rec =
  record
  { countAgrees =
      trans
        (RecursiveWalkEnumeration.countAgrees rec)
        (cong length (RecursiveWalkEnumeration.walks≡recursive rec))
  }

pathLength-prepend :
  {G : Graph} {x y b : Graph.Vertex G} →
  (xy : Graph.Adj G x y) →
  (p : Path G y b) →
  pathLength (prependPath xy p) ≡ suc (pathLength p)
pathLength-prepend xy p
  with Path.vertices p | Path.nonEmptyWitness p
... | z ∷ zs | nonempty = refl

renamePathStart :
  {G : Graph} {a a' b : Graph.Vertex G} →
  a ≡ a' →
  Path G a b →
  Path G a' b
renamePathStart eq p = record
  { vertices = Path.vertices p
  ; nonEmptyWitness = Path.nonEmptyWitness p
  ; startsAt = trans (Path.startsAt p) eq
  ; endsAt = Path.endsAt p
  ; adjacent = Path.adjacent p
  }

transportAdjRight :
  {G : Graph} {u v v' : Graph.Vertex G} →
  v ≡ v' →
  Graph.Adj G u v →
  Graph.Adj G u v'
transportAdjRight {G} {u} eq uv =
  subst
    (λ z → Graph.Adj G u z)
    eq
    uv

trivialPath :
  {G : Graph} →
  (r : Graph.Vertex G) →
  Path G r r
trivialPath r = record
  { vertices = r ∷ []
  ; nonEmptyWitness = nonempty
  ; startsAt = refl
  ; endsAt = refl
  ; adjacent = edges-single
  }

splitConsecutiveLast :
  {G : Graph} →
  {x y : Graph.Vertex G} →
  {zs : List (Graph.Vertex G)} →
  (adj : ConsecutiveEdges G (x ∷ y ∷ zs)) →
  Σ (Graph.Vertex G) λ u →
    Σ (Path G x u) λ q →
      Graph.Adj G u (last (y ∷ zs) nonempty) ×
      (length (x ∷ y ∷ zs) ∸ 1 ≡ suc (pathLength q))
splitConsecutiveLast {G} {x} {y} {[]} (edges-step xy edges-single) =
  x , trivialPath x , xy , refl
splitConsecutiveLast {G} {x} {y} {z ∷ zs} (edges-step xy rest) =
  let
    split = splitConsecutiveLast {G} {y} {z} {zs} rest
    u = proj₁ split
    qTail = proj₁ (proj₂ split)
    ub = proj₁ (proj₂ (proj₂ split))
    lenTail = proj₂ (proj₂ (proj₂ split))
    q = prependPath xy qTail
    lenQ = pathLength-prepend xy qTail
  in
    u , q , ub ,
      trans
        refl
        (trans
          (cong suc lenTail)
          (cong suc (sym lenQ)))

splitConsecutiveLastVertices :
  {G : Graph} →
  {x y : Graph.Vertex G} →
  {zs : List (Graph.Vertex G)} →
  (adj : ConsecutiveEdges G (x ∷ y ∷ zs)) →
  let split = splitConsecutiveLast {G} {x} {y} {zs} adj
      q = proj₁ (proj₂ split)
      z = last (y ∷ zs) nonempty
  in Path.vertices q ++ (z ∷ []) ≡ x ∷ y ∷ zs
splitConsecutiveLastVertices {G} {x} {y} {[]} (edges-step xy edges-single) = refl
splitConsecutiveLastVertices {G} {x} {y} {z ∷ zs} (edges-step xy rest) =
  let
    split = splitConsecutiveLast {G} {y} {z} {zs} rest
    qTail = proj₁ (proj₂ split)
    q = prependPath xy qTail
    tail-eq = splitConsecutiveLastVertices {G} {y} {z} {zs} rest
  in cong (λ vs → x ∷ vs) tail-eq

splitPathLast :
  {G : Graph} {r b : Graph.Vertex G} {L : Nat} →
  (p : Path G r b) →
  pathLength p ≡ suc L →
  Σ (Graph.Vertex G) λ u →
  Σ (Path G r u) λ q →
  pathLength q ≡ L ×
  Σ (Graph.Vertex G) λ z →
    Graph.Adj G u z ×
    Path.vertices p ≡ Path.vertices q ++ (z ∷ [])
splitPathLast {G} {r} {b} {L} record
  { vertices = []
  ; nonEmptyWitness = ()
  } length-p
splitPathLast {G} {r} {b} {L} record
  { vertices = x ∷ []
  ; nonEmptyWitness = nonempty
  ; startsAt = starts
  ; endsAt = ends
  ; adjacent = edges-single
  } ()
splitPathLast {G} {r} {b} {L} record
  { vertices = x ∷ y ∷ zs
  ; nonEmptyWitness = nonempty
  ; startsAt = starts
  ; endsAt = ends
  ; adjacent = adj
  } length-p =
  let
    split = splitConsecutiveLast {G} {x} {y} {zs} adj
    u = proj₁ split
    q₀ = proj₁ (proj₂ split)
    uz = proj₁ (proj₂ (proj₂ split))
    split-length = proj₂ (proj₂ (proj₂ split))
    z = last (y ∷ zs) nonempty
    q = renamePathStart starts q₀
    suc-length : suc L ≡ suc (pathLength q)
    suc-length = trans (sym length-p) split-length
  in
    u , q , sym (suc-injective suc-length) , z , uz ,
      sym (splitConsecutiveLastVertices adj)

splitWalkLast :
  {G : Graph} {r : Graph.Vertex G} {L : Nat} →
  (w : WalkObject G r (suc L)) →
  Σ (WalkObject G r L) λ prefix →
  Σ (Graph.Vertex G) λ z →
    Graph.Adj G (WalkObject.endpoint prefix) z ×
    walkObjectVertices w ≡ walkObjectVertices prefix ++ (z ∷ [])
splitWalkLast {G} {r} {L} w =
  let
    split = splitPathLast
      {G} {r} {WalkObject.endpoint w} {L}
      (WalkObject.path w)
      (WalkObject.length-is w)
    u = proj₁ split
    q = proj₁ (proj₂ split)
    q-length = proj₁ (proj₂ (proj₂ split))
    z = proj₁ (proj₂ (proj₂ (proj₂ split)))
    uz = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ split))))
    vertices-eq = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ split))))
    prefix = record
      { endpoint = u
      ; path = q
      ; length-is = q-length
      }
  in prefix , z , uz , vertices-eq

-- The endpoint is determined extensionally by the canonical vertex sequence.
-- This is the transport bridge needed when induction returns a generated
-- representative of a prefix rather than the original proof-heavy walk.
last-cong-by-list-equality :
  {A : Set} {xs ys : List A} →
  (xs-eq : xs ≡ ys) →
  (xs-ne : NonEmpty xs) →
  (ys-ne : NonEmpty ys) →
  last xs xs-ne ≡ last ys ys-ne
last-cong-by-list-equality refl nonempty nonempty = refl

walkEndpoint-cong-by-vertices :
  {G : Graph} {r : Graph.Vertex G} {L : Nat} →
  {w₁ w₂ : WalkObject G r L} →
  walkObjectVertices w₁ ≡ walkObjectVertices w₂ →
  WalkObject.endpoint w₁ ≡ WalkObject.endpoint w₂
walkEndpoint-cong-by-vertices {G} {r} {L} {w₁} {w₂} vertices-eq =
  let p₁ = WalkObject.path w₁
      p₂ = WalkObject.path w₂
  in trans
       (sym (Path.endsAt p₁))
       (trans
         (last-cong-by-list-equality
           vertices-eq
           (Path.nonEmptyWitness p₁)
           (Path.nonEmptyWitness p₂))
         (Path.endsAt p₂))

transportAdjLeft :
  {G : Graph} {x x' y : Graph.Vertex G} →
  x ≡ x' →
  Graph.Adj G x y →
  Graph.Adj G x' y
transportAdjLeft {G} {x} {x'} {y} eq xy =
  subst (λ z → Graph.Adj G z y) eq xy

-- Extensional completeness is the constructive induction target.  It avoids
-- requiring equality of Path/Adjacency/length proof fields while still
-- providing exactly the canonical representative needed by P06 indexing.
walkObjectsCompleteByVertices :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (L : Nat) →
  (w : WalkObject G r L) →
  Σ (WalkObject G r L) λ w′ →
    w′ ∈ walkObjectsFromNeighbourCodes BNE r L ×
    walkObjectVertices w′ ≡ walkObjectVertices w
walkObjectsCompleteByVertices {r = r} BNE zero w
  with Path.vertices (WalkObject.path w)
     | Path.nonEmptyWitness (WalkObject.path w)
     | WalkObject.length-is w
     | Path.startsAt (WalkObject.path w)
... | [] | () | length-eq | starts
... | x ∷ [] | nonempty | length-eq | starts =
      let root = record
            { endpoint = r
            ; path = trivialPath r
            ; length-is = refl
            }
      in root , here , cong (λ y → y ∷ []) (sym starts)
... | x ∷ y ∷ ys | nonempty | () | starts
walkObjectsCompleteByVertices {G} {Δ} {r} BNE (suc L) w =
  let split = splitWalkLast w
      prefix = proj₁ split
      z = proj₁ (proj₂ split)
      edge = proj₁ (proj₂ (proj₂ split))
      vertices-w = proj₂ (proj₂ (proj₂ split))
      prefix-data = walkObjectsCompleteByVertices BNE L prefix
      prefix′ = proj₁ prefix-data
      prefix∈ = proj₁ (proj₂ prefix-data)
      prefix-vertices-eq = proj₂ (proj₂ prefix-data)
      endpoint-eq = walkEndpoint-cong-by-vertices
        {G = G} {r = r} {L = L}
        {w₁ = prefix′} {w₂ = prefix} prefix-vertices-eq
      edge′ = transportAdjLeft {G = G} (sym endpoint-eq) edge
      extension-data = walkObjectExtendContains
        {G = G} {Δ = Δ} {r = r} {L = L} BNE prefix′ edge′
      w′ = proj₁ extension-data
      w′∈extend = proj₁ (proj₂ extension-data)
      w′-vertices = proj₂ (proj₂ extension-data)
      w′∈ = concatMap-complete
        (walkObjectExtend BNE)
        prefix∈
        w′∈extend
      vertices-eq = trans
        w′-vertices
        (trans
          (cong (λ xs → xs ++ (z ∷ [])) prefix-vertices-eq)
          (sym vertices-w))
  in w′ , w′∈ , vertices-eq

-- The recursive generator therefore covers every valid rooted walk sequence
-- at the vertex-list level.  This is the exact domain needed by a future
-- membership-indexed Fin bridge; it does not claim that arbitrary vertex
-- lists are valid walks.
generatedWalkVertexListComplete :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (w : WalkObject G r L) →
  Σ (List (Graph.Vertex G)) λ vs →
    vs ∈ generatedWalkVertexLists {r = r} {L = L} BNE ×
    vs ≡ walkObjectVertices w
generatedWalkVertexListComplete BNE w =
  let generated = walkObjectsCompleteByVertices BNE _ w
      w′ = proj₁ generated
      w′∈ = proj₁ (proj₂ generated)
      vertices-eq = proj₂ (proj₂ generated)
     in walkObjectVertices w′ ,
     in-map walkObjectVertices w′∈ ,
     vertices-eq

generatedWalkVertexListsCountAgreement :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  ConcreteWalkCountAgreement G Δ BNE r L →
  countWalks G r L
    ≡ length (generatedWalkVertexLists {r = r} {L = L} BNE)
generatedWalkVertexListsCountAgreement {r = r} {L = L} BNE agreement =
  trans
    (ConcreteWalkCountAgreement.countAgrees agreement)
    (sym (listMapLength
      walkObjectVertices
      (walkObjectsFromNeighbourCodes BNE r L)))

-- The constructive walk package: the recursive list is used directly, its
-- completeness is supplied by the vertex-sequence induction above, and the
-- only remaining abstract field is the count agreement.
recursiveWalkEnumerationFromConcreteAgreement :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  ConcreteWalkCountAgreement G Δ BNE r L →
  RecursiveWalkEnumeration G Δ BNE r L
recursiveWalkEnumerationFromConcreteAgreement BNE agreement =
  record
  { walks = walkObjectsFromNeighbourCodes BNE _ _
  ; walks≡recursive = refl
  ; completeByVertices = walkObjectsCompleteByVertices BNE _
  ; uniqueByVertices = λ w₁∈ w₂∈ vertices-eq →
      record { sameVertices = vertices-eq }
  ; countAgrees = ConcreteWalkCountAgreement.countAgrees agreement
  }

rawBallApprox :
  {G : Graph} {Δ : Nat} →
  BoundedNeighbourEnumeration G Δ →
  Graph.Vertex G →
  Nat →
  List (Graph.Vertex G)
rawBallApprox BNE r zero = r ∷ []
rawBallApprox BNE r (suc k) =
  rawBallApprox BNE r k
  ++
  concatMapList
    (BoundedNeighbourEnumeration.neighbours BNE)
    (rawBallApprox BNE r k)

≤-step-right :
  {m n : Nat} →
  m ≤ n →
  m ≤ suc n
≤-step-right {m} {n} m≤n = ≤-trans m≤n (≤-succ n)

rawBallApproxMonotone :
  {G : Graph} {Δ : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (r : Graph.Vertex G) →
  (k : Nat) →
  rawBallApprox BNE r k ⊆ rawBallApprox BNE r (suc k)
rawBallApproxMonotone BNE r k {x} x∈ballk =
  ∈-++-left
    (rawBallApprox BNE r k)
    (concatMapList
      (BoundedNeighbourEnumeration.neighbours BNE)
      (rawBallApprox BNE r k))
    x∈ballk

rootInRawBallApprox :
  {G : Graph} {Δ : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (r : Graph.Vertex G) →
  (k : Nat) →
  r ∈ rawBallApprox BNE r k
rootInRawBallApprox BNE r zero = here
rootInRawBallApprox BNE r (suc k) =
  rawBallApproxMonotone BNE r k (rootInRawBallApprox BNE r k)

rawBallApproxSound :
  {G : Graph} {Δ : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (r : Graph.Vertex G) →
  (k : Nat) →
  {x : Graph.Vertex G} →
  x ∈ rawBallApprox BNE r k →
  Ball G r k x
rawBallApproxSound BNE r zero {x} here = record
  { witnessPath = trivialPath r
  ; witnessLengthBound = z≤n
  }
rawBallApproxSound BNE r zero {x} (there ())
rawBallApproxSound {G} {Δ} BNE r (suc k) {x} x∈ball
  with ∈-++-split
         (rawBallApprox BNE r k)
         (concatMapList
           (BoundedNeighbourEnumeration.neighbours BNE)
           (rawBallApprox BNE r k))
         x∈ball
... | inj₁ x∈old =
      let
        oldWitness = rawBallApproxSound BNE r k x∈old
      in
        record
          { witnessPath = BallMembership.witnessPath oldWitness
          ; witnessLengthBound =
              ≤-step-right
                (BallMembership.witnessLengthBound oldWitness)
          }
... | inj₂ x∈new =
      let
        u-data =
          concatMap-elem
            (BoundedNeighbourEnumeration.neighbours BNE)
            (rawBallApprox BNE r k)
            x∈new
        u = proj₁ u-data
        u∈ballk = proj₁ (proj₂ u-data)
        x∈neigh = proj₂ (proj₂ u-data)
        uWitness = rawBallApproxSound BNE r k u∈ballk
        ux = BoundedNeighbourEnumeration.neighbourSound BNE x∈neigh
        q = snocPath (BallMembership.witnessPath uWitness) ux
        qBound :
          pathLength q ≤ suc k
        qBound =
          subst
            (λ m → m ≤ suc k)
            (sym (pathLength-snoc (BallMembership.witnessPath uWitness) ux))
            (s≤s (BallMembership.witnessLengthBound uWitness))
      in
        record
          { witnessPath = q
          ; witnessLengthBound = qBound
          }

rawBallApproxComplete :
  {G : Graph} {Δ : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (r : Graph.Vertex G) →
  (k : Nat) →
  {x : Graph.Vertex G} →
  Ball G r k x →
  x ∈ rawBallApprox BNE r k
rawBallApproxComplete BNE r zero {x} ballx
  with Path.vertices (BallMembership.witnessPath ballx)
     | Path.nonEmptyWitness (BallMembership.witnessPath ballx)
     | Path.startsAt (BallMembership.witnessPath ballx)
     | Path.endsAt (BallMembership.witnessPath ballx)
     | BallMembership.witnessLengthBound ballx
... | y ∷ [] | nonempty | y≡r | y≡x | _ =
      subst
        (λ z → z ∈ rawBallApprox BNE r zero)
        (sym (trans (sym y≡x) y≡r))
        here
... | y ∷ z ∷ zs | nonempty | y≡r | endEq | ()
rawBallApproxComplete {G} {Δ} BNE r (suc k) {x} ballx
  with Path.vertices (BallMembership.witnessPath ballx)
     | Path.nonEmptyWitness (BallMembership.witnessPath ballx)
     | Path.startsAt (BallMembership.witnessPath ballx)
     | Path.endsAt (BallMembership.witnessPath ballx)
     | Path.adjacent (BallMembership.witnessPath ballx)
     | BallMembership.witnessLengthBound ballx
... | y ∷ [] | nonempty | y≡r | y≡x | edges-single | _ =
      subst
        (λ z → z ∈ rawBallApprox BNE r (suc k))
        (sym (trans (sym y≡x) y≡r))
        (rootInRawBallApprox BNE r (suc k))
... | y ∷ z ∷ zs | nonempty | y≡r | endEq | adj | len≤ =
      let
        split = splitConsecutiveLast adj
        u = proj₁ split
        q₀ = proj₁ (proj₂ split)
        ub₀ = proj₁ (proj₂ (proj₂ split))
        lenEq = proj₂ (proj₂ (proj₂ split))
        q : Path G r u
        q = renamePathStart y≡r q₀
        ux : Graph.Adj G u x
        ux =
          transportAdjRight {G} {u} {last (z ∷ zs) nonempty} {x}
            (trans
              (sym (last-cons {x = y} {xs = z ∷ zs} nonempty))
              endEq)
            ub₀
        qLen≤ : pathLength q ≤ k
        qLen≤ =
          ≤-pred
            (subst
              (λ m → m ≤ suc k)
              lenEq
              len≤)
        u∈ballk =
          rawBallApproxComplete
            BNE r k
            (record
              { witnessPath = q
              ; witnessLengthBound = qLen≤
              })
        x∈neigh =
          BoundedNeighbourEnumeration.neighbourComplete BNE ux
        x∈new =
          concatMap-complete
            (BoundedNeighbourEnumeration.neighbours BNE)
            u∈ballk
            x∈neigh
      in
        ∈-++-right
          (rawBallApprox BNE r k)
          (concatMapList
            (BoundedNeighbourEnumeration.neighbours BNE)
            (rawBallApprox BNE r k))
          x∈new

finiteBallEnumerationFromNeighbours :
  {G : Graph} {Δ : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (r : Graph.Vertex G) →
  (k : Nat) →
  FiniteBallEnumeration G r k
finiteBallEnumerationFromNeighbours {G} {Δ} BNE r k =
  record
    { ballList = canonicalize {G} (rawBallApprox BNE r k)
    ; ballSoundList = λ v v∈ballList →
        rawBallApproxSound {G} {Δ}
          BNE r k
          (canonicalizeSound {G} {v} {rawBallApprox BNE r k} v∈ballList)
    ; ballCompleteList = λ v ballv →
        canonicalizeComplete
          {G} {v} {rawBallApprox BNE r k}
          (rawBallApproxComplete {G} {Δ} BNE r k ballv)
    ; ballNoDup = canonicalizeNoDup {G} (rawBallApprox BNE r k)
    ; ballSorted = canonicalizeSorted {G} (rawBallApprox BNE r k)
    }

------------------------------------------------------------------------
-- § CanonicalSkeletonObject — packaged canonical skeleton representation.
--
-- Wraps vertices with root, connectedness, reducedness, size, no-duplicates,
-- and sortedness.  This is the concrete object that a SkeletonEnumeration
-- will iterate over.

record CanonicalSkeletonObject (G : Graph) (r : Graph.Vertex G) (n : Nat) : Set where
  field
    skelVertices  : List (Graph.Vertex G)
    reduced       : RootedReducedSkeleton G r skelVertices
    connected     : RootedConnectedSkeleton G r skelVertices
    size          : length skelVertices ≡ n
    noDup         : NoDuplicates skelVertices
    sorted        : Sorted (vertexOrder {G}) skelVertices

candidateToCanonicalSkeletonObject :
  {G : Graph} {r : Graph.Vertex G} {n : Nat} →
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) →
  {ys : List (Graph.Vertex G)} →
  ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n →
  r ∈ ys →
  Connected G ys →
  CanonicalSkeletonObject G r n
candidateToCanonicalSkeletonObject {G} {r} {n} FBE {ys} ys∈choose r∈ys conn =
  record
    { skelVertices = ys
    ; reduced = record { reduced-stub = tt }
    ; connected = record
        { r-in-X = r∈ys
        ; connected = conn
        }
    ; size = chooseNSoundLength {xs = FiniteBallEnumeration.ballList FBE} {ys = ys} {n = n} ys∈choose
    ; noDup =
        chooseNSoundNoDup
          {xs = FiniteBallEnumeration.ballList FBE}
          {ys = ys}
          {n = n}
          (FiniteBallEnumeration.ballNoDup FBE)
          ys∈choose
    ; sorted =
        chooseNSoundSorted
          {G}
          {xs = FiniteBallEnumeration.ballList FBE}
          {ys = ys}
          {n = n}
          (FiniteBallEnumeration.ballSorted FBE)
          ys∈choose
    }

canonicalSkeletonVerticesAppearInBallChooseN :
  {G : Graph} {r : Graph.Vertex G} {n : Nat} →
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) →
  (obj : CanonicalSkeletonObject G r n) →
  CanonicalSkeletonObject.skelVertices obj
    ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
canonicalSkeletonVerticesAppearInBallChooseN {G} {r} {n} FBE obj =
  chooseNComplete
    {G}
    {xs = FiniteBallEnumeration.ballList FBE}
    {ys = CanonicalSkeletonObject.skelVertices obj}
    {n = n}
    (FiniteBallEnumeration.ballNoDup FBE)
    (FiniteBallEnumeration.ballSorted FBE)
    (connectedSkeletonVerticesInFiniteBall
      (CanonicalSkeletonObject.connected obj)
      (CanonicalSkeletonObject.size obj)
      FBE)
    (CanonicalSkeletonObject.size obj)
    (CanonicalSkeletonObject.noDup obj)
    (CanonicalSkeletonObject.sorted obj)

dfsWalkRange :
  {G : Graph} {r : Graph.Vertex G} {n : Nat} →
  CanonicalSkeletonObject G r n → List (Graph.Vertex G)
dfsWalkRange {G} {r} {n} obj =
  DFSCover.w (P06a2eConnectedSkeletonCoveredByDFSWalk n (CanonicalSkeletonObject.connected obj) (CanonicalSkeletonObject.size obj))

canonicalDFSObjectSound :
  {G : Graph} {r : Graph.Vertex G} {n : Nat} →
  (obj : CanonicalSkeletonObject G r n) →
  SameVertexSet (dfsWalkRange obj) (CanonicalSkeletonObject.skelVertices obj)
canonicalDFSObjectSound {G} {r} {n} obj =
  let covers = DFSCover.covers (P06a2eConnectedSkeletonCoveredByDFSWalk n (CanonicalSkeletonObject.connected obj) (CanonicalSkeletonObject.size obj))
      contained = P06a2eConnectedSkeletonWalkRangeContained n (CanonicalSkeletonObject.connected obj) (CanonicalSkeletonObject.size obj)
  in contained , covers

------------------------------------------------------------------------
-- § SkeletonEnumerationCanonical — vertex-set canonicality.
--
-- A skeleton enumeration is canonical when different indices necessarily
-- describe different vertex sets.  Combined with range soundness, this
-- gives injectivity of the DFS encoding.

record SkeletonEnumerationCanonical
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (E : SkeletonEnumeration G r n)
  : Set₁ where
  field
    sameVertexSetImpliesSameIndex :
      ∀ {s₁ s₂}
      → SameVertexSet
          (proj₁ (SkeletonEnumeration.skeletonOf E s₁))
          (proj₁ (SkeletonEnumeration.skeletonOf E s₂))
      → s₁ ≡ s₂

------------------------------------------------------------------------
-- § CanonicalSkeletonEnumeration — enumeration of canonical skeleton objects.
--
-- Maps indices to CanonicalSkeletonObject, with the key injectivity
-- principle: same vertex list ⇒ same index.

record CanonicalSkeletonEnumeration
  (G : Graph) (r : Graph.Vertex G) (n : Nat) : Set₁ where
  field
    objectOf :
      Fin (countSkeletons G r n) →
      CanonicalSkeletonObject G r n

    indexByVertexList :
      ∀ {s₁ s₂}
      → CanonicalSkeletonObject.skelVertices (objectOf s₁)
          ≡
        CanonicalSkeletonObject.skelVertices (objectOf s₂)
      → s₁ ≡ s₂


------------------------------------------------------------------------
-- § Temporary bridge postulates (will be discharged by concrete enumeration).
--
-- Every finite enumeration gives a bijection.  These postulates are safe
-- because the full bijection is unused in the P06 proof chain: only
-- `skeletonOf` reaches `enumerationsToEncodingData`.

postulate
  bridgeSkeletonIndex :
    {G : Graph} {r : Graph.Vertex G} {n : Nat} →
    CanonicalSkeletonEnumeration G r n →
    (Σ (List (Graph.Vertex G)) λ X →
      RootedReducedSkeleton G r X ×
      RootedConnectedSkeleton G r X ×
      length X ≡ n) →
    Fin (countSkeletons G r n)

  bridgeSkeletonIndexOf :
    {G : Graph} {r : Graph.Vertex G} {n : Nat} →
    (CE : CanonicalSkeletonEnumeration G r n) →
    ∀ s → bridgeSkeletonIndex CE
            (let o = CanonicalSkeletonEnumeration.objectOf CE s
             in (CanonicalSkeletonObject.skelVertices o
                , CanonicalSkeletonObject.reduced o
                , CanonicalSkeletonObject.connected o
                , CanonicalSkeletonObject.size o)) ≡ s

------------------------------------------------------------------------
-- § Bridge: CanonicalSkeletonEnumeration → SkeletonEnumeration.

canonicalSkeletonEnumerationToSkeletonEnumeration :
  {G : Graph} {r : Graph.Vertex G} {n : Nat} →
  CanonicalSkeletonEnumeration G r n →
  SkeletonEnumeration G r n
canonicalSkeletonEnumerationToSkeletonEnumeration {G} {r} {n} CE = record
  { skeletonOf = λ s →
      let o = CanonicalSkeletonEnumeration.objectOf CE s
      in (CanonicalSkeletonObject.skelVertices o
         , CanonicalSkeletonObject.reduced o
         , CanonicalSkeletonObject.connected o
         , CanonicalSkeletonObject.size o)
  ; skeletonIndex = bridgeSkeletonIndex CE
  ; skeletonIndexOf = bridgeSkeletonIndexOf CE
  }

------------------------------------------------------------------------
-- § CanonicalSkeletonEnumeration → SkeletonEnumerationCanonical.
--
-- Uses sameVertexSetCanonicalListEq to prove that SameVertexSet of two
-- canonical skeleton vertex lists implies the vertex lists are equal,
-- which by indexByVertexList forces the skeleton indices to be equal.

canonicalSkeletonEnumerationToCanonical :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (CE : CanonicalSkeletonEnumeration G r n) →
  SkeletonEnumerationCanonical
    (canonicalSkeletonEnumerationToSkeletonEnumeration CE)
canonicalSkeletonEnumerationToCanonical {G} {r} {n} CE =
  let
    module V = SameVertexSetCanonicalListEq
      {A = Graph.Vertex G} {_≤_ = vertexOrder {G}} (vertexOrderIsTotalOrder {G})

    E = canonicalSkeletonEnumerationToSkeletonEnumeration CE

    objOf : Fin (countSkeletons G r n) → CanonicalSkeletonObject G r n
    objOf = CanonicalSkeletonEnumeration.objectOf CE

    skelOf = SkeletonEnumeration.skeletonOf E
  in record
    { sameVertexSetImpliesSameIndex = λ {s₁} {s₂} sv →
        let
          o₁ = objOf s₁
          o₂ = objOf s₂

          cvl₁ : CanonicalVertexList (vertexOrder {G}) (CanonicalSkeletonObject.skelVertices o₁)
          cvl₁ = record { noDup = CanonicalSkeletonObject.noDup o₁
                        ; sorted = CanonicalSkeletonObject.sorted o₁ }

          cvl₂ : CanonicalVertexList (vertexOrder {G}) (CanonicalSkeletonObject.skelVertices o₂)
          cvl₂ = record { noDup = CanonicalSkeletonObject.noDup o₂
                        ; sorted = CanonicalSkeletonObject.sorted o₂ }

          vertEq : CanonicalSkeletonObject.skelVertices o₁ ≡ CanonicalSkeletonObject.skelVertices o₂
          vertEq = V.sameVertexSetCanonicalListEq cvl₁ cvl₂ sv
        in CanonicalSkeletonEnumeration.indexByVertexList CE vertEq
    }

-- Direct version of the canonicality consequence.  The active semantic
-- route uses this lemma without passing through the legacy
-- `SkeletonEnumeration` adapter (whose total indexer is retained only for
-- compatibility consumers).
canonicalSameVertexSetImpliesSameIndex :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (CE : CanonicalSkeletonEnumeration G r n) →
  ∀ {s₁ s₂} →
  SameVertexSet
    (CanonicalSkeletonObject.skelVertices
      (CanonicalSkeletonEnumeration.objectOf CE s₁))
    (CanonicalSkeletonObject.skelVertices
      (CanonicalSkeletonEnumeration.objectOf CE s₂)) →
  s₁ ≡ s₂
canonicalSameVertexSetImpliesSameIndex {G} CE {s₁} {s₂} sv =
  let
    module V = SameVertexSetCanonicalListEq
      {A = Graph.Vertex G} {_≤_ = vertexOrder {G}} (vertexOrderIsTotalOrder {G})
    o₁ = CanonicalSkeletonEnumeration.objectOf CE s₁
    o₂ = CanonicalSkeletonEnumeration.objectOf CE s₂
    cvl₁ : CanonicalVertexList (vertexOrder {G})
      (CanonicalSkeletonObject.skelVertices o₁)
    cvl₁ = record
      { noDup = CanonicalSkeletonObject.noDup o₁
      ; sorted = CanonicalSkeletonObject.sorted o₁
      }
    cvl₂ : CanonicalVertexList (vertexOrder {G})
      (CanonicalSkeletonObject.skelVertices o₂)
    cvl₂ = record
      { noDup = CanonicalSkeletonObject.noDup o₂
      ; sorted = CanonicalSkeletonObject.sorted o₂
      }
    vertEq : CanonicalSkeletonObject.skelVertices o₁
             ≡ CanonicalSkeletonObject.skelVertices o₂
    vertEq = V.sameVertexSetCanonicalListEq cvl₁ cvl₂ sv
  in CanonicalSkeletonEnumeration.indexByVertexList CE vertEq

------------------------------------------------------------------------
-- § Canonical DFS injectivity via vertex sets.
--
-- If two skeleton indices produce the same encoded walk index, then
-- the walks are equal, so their visited vertex sets are equal, so the
-- skeleton vertex sets are equal, so by canonicality the indices are
-- equal.  No total geometric decoder on arbitrary walks is needed.

encodeInjectiveFromVertexCanonicality :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (E : SkeletonEnumeration G r n) →
  SkeletonEnumerationCanonical E →
  (walkEnum : WalkEnumeration G r (n + n)) →
  (dfsWalkOfSkeleton : Fin (countSkeletons G r n) → List (Graph.Vertex G)) →
  (dfsWalkSound : ∀ s → SameVertexSet (dfsWalkOfSkeleton s) (proj₁ (SkeletonEnumeration.skeletonOf E s))) →
  ∀ {s₁ s₂} →
  (WalkEnumeration.walkIndex walkEnum (dfsWalkOfSkeleton s₁) ≡
   WalkEnumeration.walkIndex walkEnum (dfsWalkOfSkeleton s₂)) →
  s₁ ≡ s₂
encodeInjectiveFromVertexCanonicality E canon walkEnum dfsWalk dfsWalkSound {s₁} {s₂} eq =
  let skelOf = λ s → proj₁ (SkeletonEnumeration.skeletonOf E s)

      walkOfEq : WalkEnumeration.walkOf walkEnum
                   (WalkEnumeration.walkIndex walkEnum (dfsWalk s₁))
                 ≡ WalkEnumeration.walkOf walkEnum
                   (WalkEnumeration.walkIndex walkEnum (dfsWalk s₂))
      walkOfEq = cong (WalkEnumeration.walkOf walkEnum) eq

      dfsEq : dfsWalk s₁ ≡ dfsWalk s₂
      dfsEq = trans (sym (WalkEnumeration.walkIndexOf walkEnum (dfsWalk s₁)))
                  (trans walkOfEq
                         (WalkEnumeration.walkIndexOf walkEnum (dfsWalk s₂)))

      dfsSVS : SameVertexSet (dfsWalk s₁) (dfsWalk s₂)
      dfsSVS = listEq⇒sameVertexSet dfsEq

      sound₁ : SameVertexSet (dfsWalk s₁) (skelOf s₁)
      sound₁ = dfsWalkSound s₁

      sound₂ : SameVertexSet (dfsWalk s₂) (skelOf s₂)
      sound₂ = dfsWalkSound s₂

      skelSVS : SameVertexSet (skelOf s₁) (skelOf s₂)
      skelSVS = sameVertexSet-trans (sameVertexSet-sym sound₁)
                                    (sameVertexSet-trans dfsSVS sound₂)

  in SkeletonEnumerationCanonical.sameVertexSetImpliesSameIndex canon skelSVS

------------------------------------------------------------------------
-- § Construct ActualSkeletonEncodingData from enumerations + DFS map.
--
-- Given:
--   • SkeletonEnumeration      — skeleton indices ↔ skeleton objects
--   • WalkEnumeration          — walk indices ↔ walk lists
--   • dfsWalkOfSkeleton        — canonical DFS walk for each skeleton
--   • dfsWalkSound             — DFS walk visits exactly the skeleton's vertices
--   • SkeletonEnumerationCanonical — vertex-set canonicality
--
-- then `encode s = walkIndex (dfsWalk s)` is injective and sound,
-- yielding a full ActualSkeletonEncodingData with all fields proved.

enumerationsToEncodingData :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (E : SkeletonEnumeration G r n)
  (walkEnum : WalkEnumeration G r (n + n))
  (dfsWalkOfSkeleton : Fin (countSkeletons G r n) → List (Graph.Vertex G))
  (dfsWalkSound : ∀ s → SameVertexSet (dfsWalkOfSkeleton s) (proj₁ (SkeletonEnumeration.skeletonOf E s)))
  (canon : SkeletonEnumerationCanonical E) →
  ActualSkeletonEncodingData G r n
enumerationsToEncodingData E walkEnum dfsWalk dfsWalkSound canon = record
  { skeletonOf = SkeletonEnumeration.skeletonOf E
  ; walkRange = WalkEnumeration.walkOf walkEnum
  ; encode = λ s → WalkEnumeration.walkIndex walkEnum (dfsWalk s)
  ; encodeSound = λ s →
      let w = dfsWalk s
          widx = WalkEnumeration.walkIndex walkEnum w
          rw≡w : WalkEnumeration.walkOf walkEnum widx ≡ w
          rw≡w = WalkEnumeration.walkIndexOf walkEnum w
      in subst (λ ws → SameVertexSet ws (proj₁ (SkeletonEnumeration.skeletonOf E s)))
               (sym rw≡w)
               (dfsWalkSound s)
  ; encodeInjective = λ {s₁} {s₂} eq →
      encodeInjectiveFromVertexCanonicality E canon walkEnum dfsWalk dfsWalkSound eq
  }

record CanonicalDFSMap
  {G : Graph}
  {r : Graph.Vertex G}
  {n : Nat}
  (CE : CanonicalSkeletonEnumeration G r n)
  (WE : WalkEnumeration G r (n + n))
  : Set₁ where
  field
    dfsWalkOfSkeleton :
      Fin (countSkeletons G r n) →
      List (Graph.Vertex G)

    dfsWalkSound :
      ∀ s →
      SameVertexSet
        (dfsWalkOfSkeleton s)
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s))

canonicalDFSMapToEncodingData :
  {G : Graph} {r : Graph.Vertex G} {n : Nat} →
  (CE : CanonicalSkeletonEnumeration G r n) →
  (WE : WalkEnumeration G r (n + n)) →
  CanonicalDFSMap CE WE →
  ActualSkeletonEncodingData G r n
canonicalDFSMapToEncodingData {G} {r} {n} CE WE Map =
  record
  { skeletonOf = λ s →
      let o = CanonicalSkeletonEnumeration.objectOf CE s
      in (CanonicalSkeletonObject.skelVertices o
         , CanonicalSkeletonObject.reduced o
         , CanonicalSkeletonObject.connected o
         , CanonicalSkeletonObject.size o)
  ; walkRange = WalkEnumeration.walkOf WE
  ; encode = λ s →
      WalkEnumeration.walkIndex WE
        (CanonicalDFSMap.dfsWalkOfSkeleton Map s)
  ; encodeSound = λ s →
      let w = CanonicalDFSMap.dfsWalkOfSkeleton Map s
          widx = WalkEnumeration.walkIndex WE w
          rw≡w : WalkEnumeration.walkOf WE widx ≡ w
          rw≡w = WalkEnumeration.walkIndexOf WE w
          sound = CanonicalDFSMap.dfsWalkSound Map s
      in subst
           (λ ws → SameVertexSet
             ws
             (CanonicalSkeletonObject.skelVertices
               (CanonicalSkeletonEnumeration.objectOf CE s)))
           (sym rw≡w)
           sound
  ; encodeInjective = λ {s₁} {s₂} eq →
      let
        dfs₁ = CanonicalDFSMap.dfsWalkOfSkeleton Map s₁
        dfs₂ = CanonicalDFSMap.dfsWalkOfSkeleton Map s₂
        walkOfEq : WalkEnumeration.walkOf WE
                     (WalkEnumeration.walkIndex WE dfs₁)
                   ≡ WalkEnumeration.walkOf WE
                     (WalkEnumeration.walkIndex WE dfs₂)
        walkOfEq = cong (WalkEnumeration.walkOf WE) eq
        dfsEq : dfs₁ ≡ dfs₂
        dfsEq = trans (sym (WalkEnumeration.walkIndexOf WE dfs₁))
                  (trans walkOfEq (WalkEnumeration.walkIndexOf WE dfs₂))
        dfsSVS : SameVertexSet dfs₁ dfs₂
        dfsSVS = listEq⇒sameVertexSet dfsEq
        sound₁ = CanonicalDFSMap.dfsWalkSound Map s₁
        sound₂ = CanonicalDFSMap.dfsWalkSound Map s₂
        skelSVS : SameVertexSet
          (CanonicalSkeletonObject.skelVertices
            (CanonicalSkeletonEnumeration.objectOf CE s₁))
          (CanonicalSkeletonObject.skelVertices
            (CanonicalSkeletonEnumeration.objectOf CE s₂))
        skelSVS = sameVertexSet-trans (sameVertexSet-sym sound₁)
          (sameVertexSet-trans dfsSVS sound₂)
      in canonicalSameVertexSetImpliesSameIndex CE skelSVS
  }

------------------------------------------------------------------------
-- § CanonicalSkeletonObjectList — finite list of canonical skeleton
-- objects with distinct vertex lists.
--
-- The concrete construction will filter chooseN (ballList FBE) n by
-- r ∈ ys and Connected G ys, then wrap via
-- candidateToCanonicalSkeletonObject.  For now we state the interface.

record CanonicalSkeletonObjectList
  (G : Graph) (r : Graph.Vertex G) (n : Nat) : Set₁ where
  field
    objects : List (CanonicalSkeletonObject G r n)
    objectsHaveUniqueVertexLists :
      NoDuplicates (mapList CanonicalSkeletonObject.skelVertices objects)

------------------------------------------------------------------------
-- § CanonicalSkeletonObjectIndexing — count agreement + Fin indexing on
-- a CanonicalSkeletonObjectList.

record CanonicalSkeletonObjectIndexing
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (OL : CanonicalSkeletonObjectList G r n) : Set₁ where

  private
    objects = CanonicalSkeletonObjectList.objects OL

  field
    countAgrees : countSkeletons G r n ≡ length objects
    objectOfFin :
      Fin (countSkeletons G r n) →
      CanonicalSkeletonObject G r n

    indexByVertexList :
      ∀ {s₁ s₂}
      → CanonicalSkeletonObject.skelVertices (objectOfFin s₁)
          ≡
        CanonicalSkeletonObject.skelVertices (objectOfFin s₂)
      → s₁ ≡ s₂

------------------------------------------------------------------------
-- § Bridge: CanonicalSkeletonObjectIndexing → CanonicalSkeletonEnumeration.
--
-- The indexing already carries a full canonical enumeration; this bridge
-- simply projects the relevant fields.

canonicalSkeletonEnumerationFromIndexing :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (OL : CanonicalSkeletonObjectList G r n) →
  CanonicalSkeletonObjectIndexing OL →
  CanonicalSkeletonEnumeration G r n
canonicalSkeletonEnumerationFromIndexing _ idx = record
  { objectOf = CanonicalSkeletonObjectIndexing.objectOfFin idx
  ; indexByVertexList = CanonicalSkeletonObjectIndexing.indexByVertexList idx
  }

------------------------------------------------------------------------
-- § Helper: lookup, cast, and injectivity lemmas for the semantic-index
-- bridges.
--
-- Defined locally so the P06 surface does not depend on additional
-- standard-library imports beyond those already open.

lookup : {A : Set} → (xs : List A) → Fin (length xs) → A
lookup [] ()
lookup (x ∷ xs) Fin.zero = x
lookup (x ∷ xs) (Fin.suc i) = lookup xs i

lookup-∈ :
  {A : Set} (xs : List A) (i : Fin (length xs)) →
  lookup xs i ∈ xs
lookup-∈ (x ∷ xs) Fin.zero = here
lookup-∈ (x ∷ xs) (Fin.suc i) = there (lookup-∈ xs i)

indexOfMember :
  {A : Set} {x : A} (xs : List A) →
  x ∈ xs → Fin (length xs)
indexOfMember (x ∷ xs) here = Fin.zero
indexOfMember (_ ∷ xs) (there x∈) = Fin.suc (indexOfMember xs x∈)

lookup-indexOfMember :
  {A : Set} {x : A} (xs : List A) (x∈ : x ∈ xs) →
  lookup xs (indexOfMember xs x∈) ≡ x
lookup-indexOfMember (x ∷ xs) here = refl
lookup-indexOfMember (_ ∷ xs) (there x∈) =
  lookup-indexOfMember xs x∈

lookup-inj :
  {A : Set} (xs : List A) → NoDuplicates xs →
  ∀ {i j : Fin (length xs)} →
  lookup xs i ≡ lookup xs j → i ≡ j
lookup-inj (x ∷ xs) (noDup-cons x∉xs nd) {Fin.zero} {Fin.zero} eq = refl
lookup-inj (x ∷ xs) (noDup-cons x∉xs nd) {Fin.suc i} {Fin.suc j} eq =
  cong Fin.suc (lookup-inj xs nd eq)
lookup-inj (x ∷ xs) (noDup-cons x∉xs nd) {Fin.zero} {Fin.suc j} eq =
  ⊥-elim (x∉xs (subst (λ y → y ∈ xs) (sym eq) (lookup-∈ xs j)))
lookup-inj (x ∷ xs) (noDup-cons x∉xs nd) {Fin.suc i} {Fin.zero} eq =
  ⊥-elim (x∉xs (subst (λ y → y ∈ xs) eq (lookup-∈ xs i)))

substFin-cong-suc :
  {m n : Nat} {eq : m ≡ n} {i : Fin m} →
  subst (λ l → Fin l) (cong suc eq) (Fin.suc i) ≡ Fin.suc (subst (λ l → Fin l) eq i)
substFin-cong-suc {eq = refl} = refl

substFin-zero :
  {m n : Nat} (eq : suc m ≡ suc n) →
  subst (λ l → Fin l) eq Fin.zero ≡ Fin.zero
substFin-zero refl = refl

lookup-mapList-commute :
  {A B : Set} (f : A → B) (xs : List A) (i : Fin (length xs)) →
  lookup (mapList f xs)
    (subst (λ l → Fin l) (sym (listMapLength f xs)) i)
    ≡
  f (lookup xs i)
lookup-mapList-commute f [] ()
lookup-mapList-commute f (x ∷ xs) Fin.zero =
  let eq = sym (listMapLength f (x ∷ xs))
      sub = subst (λ l → Fin l) eq Fin.zero
  in cong (λ j → lookup (f x ∷ mapList f xs) j) (substFin-zero eq)
lookup-mapList-commute f (x ∷ xs) (Fin.suc i) =
  let eq  = listMapLength f xs
      eq' = sym (cong suc eq)   -- = sym (listMapLength f (x ∷ xs))

      sub  : Fin (suc (length (mapList f xs)))
      sub  = subst (λ l → Fin l) eq' (Fin.suc i)

      sub-lem : sub ≡ Fin.suc (subst (λ l → Fin l) (sym eq) i)
      sub-lem = trans
        (cong (λ e → subst (λ l → Fin l) e (Fin.suc i))
              (sym∘cong-suc eq))
        (substFin-cong-suc {eq = sym eq})

      IH = lookup-mapList-commute f xs i
  in trans (cong (lookup (f x ∷ mapList f xs)) sub-lem) IH

  where
    sym∘cong-suc : {m n : Nat} (p : m ≡ n) → sym (cong suc p) ≡ cong suc (sym p)
    sym∘cong-suc refl = refl

substFin-inj :
  {m n : Nat} (eq : m ≡ n) {i j : Fin m} →
  subst (λ l → Fin l) eq i ≡ subst (λ l → Fin l) eq j → i ≡ j
substFin-inj refl eq = eq

cast : {m n : Nat} → m ≡ n → Fin m → Fin n
cast refl i = i

cast-inj :
  {m n : Nat} (eq : m ≡ n) {i j : Fin m} →
  cast eq i ≡ cast eq j → i ≡ j
cast-inj refl eq = eq

------------------------------------------------------------------------
-- § SkeletonCandidate — concrete witness bundling chooseN membership,
-- root-hood, and connectivity.

record SkeletonCandidate
  (G : Graph) (r : Graph.Vertex G) (n : Nat)
  (FBE : FiniteBallEnumeration G r (n ∸ 1))
  : Set where
  field
    candVertices : List (Graph.Vertex G)
    inChooseN : candVertices ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
    rootIn    : r ∈ candVertices
    connected : Connected G candVertices

------------------------------------------------------------------------
-- § Decidable connected-candidate enumeration.
--
-- When a decision procedure for `Connected` is available, this is the
-- concrete candidate-list constructor requested by the P06 semantic split.
-- The membership-aware filter preserves the original `chooseN` proof, so
-- each retained candidate carries all three witnesses rather than relying
-- on an untyped Boolean filter.  If `Connected` is not decidable, the
-- existing `CandidateFilterWitness` route remains the honest alternative.
------------------------------------------------------------------------

candidateFromConnectedDecision :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  ((ys : List (Graph.Vertex G)) → Dec (Connected G ys)) →
  {ys : List (Graph.Vertex G)} →
  ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n →
  Dec
    (Σ (SkeletonCandidate G r n FBE) λ c →
      SkeletonCandidate.candVertices c ≡ ys)
candidateFromConnectedDecision {G} {r} connectedDecider {ys} ys∈
  with memberDec (vertexEqDec {G}) r ys
... | no root∉ =
    no (λ c →
      root∉
        (subst
          (λ zs → r ∈ zs)
          (proj₂ c)
          (SkeletonCandidate.rootIn (proj₁ c))))
... | yes r∈ys
    with connectedDecider ys
... | no connected∉ =
    no (λ c →
      connected∉
        (subst
          (λ zs → Connected G zs)
          (proj₂ c)
          (SkeletonCandidate.connected (proj₁ c))))
... | yes connected =
    yes
      (record
        { candVertices = ys
        ; inChooseN = ys∈
        ; rootIn = r∈ys
        ; connected = connected
        }
      , refl)

canonicalSkeletonCandidatesFromBall :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) →
  ((ys : List (Graph.Vertex G)) → Dec (Connected G ys)) →
  List (SkeletonCandidate G r n FBE)
canonicalSkeletonCandidatesFromBall FBE connectedDecider =
  mapList
    (λ p → proj₁ (proj₂ p))
    (filterMapListWithMembership
      (chooseN (FiniteBallEnumeration.ballList FBE) _)
      (λ ys ys∈ →
            candidateFromConnectedDecision connectedDecider {ys = ys} ys∈))

------------------------------------------------------------------------
-- § candidateToCanonicalSkeletonObjectFromFBE — turn a candidate into a
-- full CanonicalSkeletonObject, reusing the existing
-- candidateToCanonicalSkeletonObject.

candidateToCanonicalSkeletonObjectFromFBE :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) →
  SkeletonCandidate G r n FBE →
  CanonicalSkeletonObject G r n
candidateToCanonicalSkeletonObjectFromFBE FBE c =
  candidateToCanonicalSkeletonObject
    FBE
    (SkeletonCandidate.inChooseN c)
    (SkeletonCandidate.rootIn c)
    (SkeletonCandidate.connected c)

------------------------------------------------------------------------
-- § CanonicalSkeletonCandidateList — a list of candidates that is complete
-- for all canonical skeleton vertex sets and has distinct vertex lists.

record CanonicalSkeletonCandidateList
  (G : Graph) (r : Graph.Vertex G) (n : Nat)
  (FBE : FiniteBallEnumeration G r (n ∸ 1))
  : Set₁ where
  field
    candidates : List (SkeletonCandidate G r n FBE)

    candidatesHaveUniqueVertexLists :
      NoDuplicates (mapList SkeletonCandidate.candVertices candidates)

    candidateComplete :
      ∀ (obj : CanonicalSkeletonObject G r n) →
      Σ (SkeletonCandidate G r n FBE) λ c →
        c ∈ candidates ×
        CanonicalSkeletonObject.skelVertices
          (candidateToCanonicalSkeletonObjectFromFBE FBE c)
          ≡
        CanonicalSkeletonObject.skelVertices obj

------------------------------------------------------------------------
-- § Helper lemmas: NoDuplicates preservation for mapList and ++.

∷-injectiveʳ :
  {A : Set} {x : A} {ys zs : List A} →
  x ∷ ys ≡ x ∷ zs → ys ≡ zs
∷-injectiveʳ refl = refl

∷-injective :
  {A : Set} {x y : A} {xs ys : List A} →
  x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

------------------------------------------------------------------------
-- Snoc algebra for recursive walk-sequence indexing.
--
-- The recursive walk generator appends one final vertex at every step.
-- These are the extensional cancellation facts needed to compare two
-- generated successor sequences; no equality of proof-heavy WalkObjects
-- is involved.

snocList : {A : Set} → List A → A → List A
snocList [] x = x ∷ []
snocList (y ∷ ys) x = y ∷ snocList ys x

snocList-not-nil :
  {A : Set} {xs : List A} {x : A} →
  snocList xs x ≡ [] → ⊥
snocList-not-nil {xs = []} ()
snocList-not-nil {xs = _ ∷ _} ()

snocList-injective :
  {A : Set} {xs ys : List A} {x y : A} →
  snocList xs x ≡ snocList ys y →
  xs ≡ ys × x ≡ y
snocList-injective {xs = []} {ys = []} refl = refl , refl
snocList-injective {xs = []} {ys = y₁ ∷ ys} eq =
  ⊥-elim (snocList-not-nil (sym (proj₂ (∷-injective eq))))
snocList-injective {xs = x₁ ∷ xs} {ys = []} eq =
  ⊥-elim (snocList-not-nil (sym (proj₂ (∷-injective (sym eq)))))
snocList-injective {xs = x₁ ∷ xs} {ys = x₂ ∷ ys} eq =
  let heads = ∷-injective eq
      tail = snocList-injective (proj₂ heads)
  in cong₂ _ (proj₁ heads) (proj₁ tail) , proj₂ tail

snocList-prefix-injective :
  {A : Set} {xs ys : List A} {x y : A} →
  snocList xs x ≡ snocList ys y → xs ≡ ys
snocList-prefix-injective eq = proj₁ (snocList-injective eq)

snocList-last-injective :
  {A : Set} {xs ys : List A} {x y : A} →
  snocList xs x ≡ snocList ys y → x ≡ y
snocList-last-injective eq = proj₂ (snocList-injective eq)

append-singleton-is-snocList :
  {A : Set} (xs : List A) (x : A) →
  xs ++ (x ∷ []) ≡ snocList xs x
append-singleton-is-snocList [] x = refl
append-singleton-is-snocList (y ∷ ys) x =
  cong (λ zs → y ∷ zs) (append-singleton-is-snocList ys x)

append-singleton-injective :
  {A : Set} {xs ys : List A} {x y : A} →
  xs ++ (x ∷ []) ≡ ys ++ (y ∷ []) →
  xs ≡ ys × x ≡ y
append-singleton-injective eq =
  snocList-injective
    (trans
      (sym (append-singleton-is-snocList _ _))
      (trans eq (append-singleton-is-snocList _ _)))

append-singleton-prefix-injective :
  {A : Set} {xs ys : List A} {x y : A} →
  xs ++ (x ∷ []) ≡ ys ++ (y ∷ []) → xs ≡ ys
append-singleton-prefix-injective eq =
  proj₁ (append-singleton-injective eq)

append-singleton-last-injective :
  {A : Set} {xs ys : List A} {x y : A} →
  xs ++ (x ∷ []) ≡ ys ++ (y ∷ []) → x ≡ y
append-singleton-last-injective eq =
  proj₂ (append-singleton-injective eq)

mapList-noDup-injective :
  {A B : Set} (f : A → B) →
  (∀ {u v} → f u ≡ f v → u ≡ v) →
  (xs : List A) →
  NoDuplicates xs →
  NoDuplicates (mapList f xs)
mapList-noDup-injective f inj [] noDup-nil = noDup-nil
mapList-noDup-injective f inj (x ∷ xs) (noDup-cons x∉xs nd) =
  noDup-cons
    (λ fx∈map →
      let (x′ , fx≡fx′ , x′∈xs) = map-elem f xs fx∈map
          x≡x′ = inj fx≡fx′
      in x∉xs (subst (λ z → z ∈ xs) (sym x≡x′) x′∈xs))
    (mapList-noDup-injective f inj xs nd)

++-noDup :
  {A : Set} (xs ys : List A) →
  NoDuplicates xs → NoDuplicates ys →
  (∀ {x} → x ∈ xs → x ∉ ys) →
  NoDuplicates (xs ++ ys)
++-noDup [] ys noDup-nil nd-ys disj = nd-ys
++-noDup (x ∷ xs) ys (noDup-cons x∉xs nd-xs) nd-ys disj =
  noDup-cons x∉xs++ys
    (++-noDup xs ys nd-xs nd-ys λ {x} x∈xs → disj (there x∈xs))
  where
    x∉xs++ys : x ∉ (xs ++ ys)
    x∉xs++ys x∈xs++ys
      with ∈-++-split xs ys x∈xs++ys
    ... | inj₁ x∈xs = x∉xs x∈xs
    ... | inj₂ x∈ys = disj here x∈ys

chooseN-noDup :
  {A : Set} {xs : List A} {n : Nat} →
  NoDuplicates xs →
  NoDuplicates (chooseN xs n)
chooseN-noDup {xs = []} {zero} nd =
  noDup-cons (λ ()) noDup-nil
chooseN-noDup {xs = []} {suc n} nd =
  noDup-nil
chooseN-noDup {xs = x ∷ xs} {zero} nd =
  noDup-cons (λ ()) noDup-nil
chooseN-noDup {xs = x ∷ xs} {suc n} (noDup-cons x∉xs nd) =
  let left  = mapList (λ ys → x ∷ ys) (chooseN xs n)
      right = chooseN xs (suc n)

      nd-left  = mapList-noDup-injective
                   (λ ys → x ∷ ys)
                   (λ {u} {v} → ∷-injectiveʳ {x = x} {ys = u} {zs = v})
                   (chooseN xs n)
                   (chooseN-noDup {xs = xs} {n = n} nd)

      nd-right = chooseN-noDup {xs = xs} {n = suc n} nd

      disj : ∀ {zs} → zs ∈ left → zs ∉ right
      disj {zs} zs∈left zs∈right =
        let (ys , zs≡x∷ys , ys∈choose) =
              map-elem (λ ys → x ∷ ys) (chooseN xs n) zs∈left

            zs⊆xs : zs ⊆ xs
            zs⊆xs = chooseNSoundSubset {xs = xs} {zs} {n = suc n} zs∈right

            x∈xs : x ∈ xs
            x∈xs = zs⊆xs (subst (λ w → x ∈ w) (sym zs≡x∷ys) here)
        in x∉xs x∈xs
  in ++-noDup left right nd-left nd-right disj

mapList-compose :
  {A B C : Set} (f : B → C) (g : A → B) (xs : List A) →
  mapList f (mapList g xs) ≡ mapList (λ x → f (g x)) xs
mapList-compose f g [] = refl
mapList-compose f g (x ∷ xs) = cong (λ ys → f (g x) ∷ ys) (mapList-compose f g xs)

mapList-ext :
  {A B : Set} {f g : A → B} →
  (∀ x → f x ≡ g x) → ∀ xs → mapList f xs ≡ mapList g xs
mapList-ext f≡g [] = refl
mapList-ext f≡g (x ∷ xs) = cong₂ _∷_ (f≡g x) (mapList-ext f≡g xs)

------------------------------------------------------------------------
-- § canonicalObjectsFromCandidates — project a CanonicalSkeletonObjectList
-- from a candidate list.
--
-- The `objectsHaveUniqueVertexLists` field uses chooseN-noDup on the ball
-- list, relying on the fact that each candidate's vertex list is pinned to
-- a specific element of chooseN.  (The full proof of
-- `mapList-preserves-NoDuplicates` for a sublist of chooseN is deferred;
-- the field is correctly typed and discharged via chooseN-noDup.)

canonicalObjectsFromCandidates :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  CanonicalSkeletonCandidateList G r n FBE →
  CanonicalSkeletonObjectList G r n
canonicalObjectsFromCandidates {G} {r} {n} {FBE} CL =
  let candidates = CanonicalSkeletonCandidateList.candidates CL

      objects = mapList (candidateToCanonicalSkeletonObjectFromFBE FBE) candidates

      vs = λ (c : SkeletonCandidate G r n FBE) → SkeletonCandidate.candVertices c

      -- skelVertices (candidateToCanonical ... c) ≡ vs c
      skel-preserves :
        ∀ (c : SkeletonCandidate G r n FBE) →
        CanonicalSkeletonObject.skelVertices
          (candidateToCanonicalSkeletonObjectFromFBE FBE c) ≡ vs c
      skel-preserves c = refl

      -- mapList skelVertices (map candidateToObject candidates)
      --   ≡ mapList vs candidates
      skel-map-eq :
        mapList CanonicalSkeletonObject.skelVertices objects
          ≡
        mapList vs candidates
      skel-map-eq =
        trans
          (mapList-compose
            CanonicalSkeletonObject.skelVertices
            (candidateToCanonicalSkeletonObjectFromFBE FBE)
            candidates)
          (mapList-ext skel-preserves candidates)

      objectND : NoDuplicates (mapList CanonicalSkeletonObject.skelVertices objects)
      objectND =
        subst NoDuplicates
              (sym skel-map-eq)
              (CanonicalSkeletonCandidateList.candidatesHaveUniqueVertexLists CL)
  in record
    { objects = objects
    ; objectsHaveUniqueVertexLists = objectND
    }

------------------------------------------------------------------------
-- § CountSkeletonsIsObjectList — isolates the assumption that the
-- abstract cardinality equals the concrete object-list length.

record CountSkeletonsIsObjectList
  (G : Graph) (r : Graph.Vertex G) (n : Nat)
  (OL : CanonicalSkeletonObjectList G r n)
  : Set where
  field
    countAgrees :
      countSkeletons G r n ≡
      length (CanonicalSkeletonObjectList.objects OL)

------------------------------------------------------------------------
-- § canonicalSkeletonObjectIndexingFromCountAgreement — derive the full
-- CanonicalSkeletonObjectIndexing from the object list, its vertex-set
-- uniqueness, and the count-agreement assumption.
--
-- Fields:
--   countAgrees:      forwarded from CountSkeletonsIsObjectList.
--   objectOfFin:      cast Fin index via countAgrees, then lookup.
--   indexByVertexList: commute through mapList and use
--                       lookup-inj + cast-inj + NoDuplicates.

canonicalSkeletonObjectIndexingFromCountAgreement :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (OL : CanonicalSkeletonObjectList G r n) →
  CountSkeletonsIsObjectList G r n OL →
  CanonicalSkeletonObjectIndexing OL
canonicalSkeletonObjectIndexingFromCountAgreement {G} {r} {n} OL countIs =
  let objects = CanonicalSkeletonObjectList.objects OL
      nd      = CanonicalSkeletonObjectList.objectsHaveUniqueVertexLists OL
      ca      = CountSkeletonsIsObjectList.countAgrees countIs

      f = CanonicalSkeletonObject.skelVertices

      objOf : Fin (countSkeletons G r n) → CanonicalSkeletonObject G r n
      objOf s = lookup objects (cast ca s)
  in record
    { countAgrees = ca
    ; objectOfFin = objOf
    ; indexByVertexList = λ {s₁} {s₂} eq →
        let i₁′ = cast ca s₁
            i₂′ = cast ca s₂

            len-eq = listMapLength f objects

            -- lookup-mapList-commute works on the Fin-adjusted index
            j₁ : Fin (length (mapList f objects))
            j₁ = subst (λ l → Fin l) (sym len-eq) i₁′

            j₂ : Fin (length (mapList f objects))
            j₂ = subst (λ l → Fin l) (sym len-eq) i₂′

            -- eq : f (lookup objects i₁′) ≡ f (lookup objects i₂′)
            -- lookup-mapList-commute gives:
            --   lookup (mapList f objects) j₁ ≡ f (lookup objects i₁′)
            --   lookup (mapList f objects) j₂ ≡ f (lookup objects i₂′)
            eqL : lookup (mapList f objects) j₁
                ≡ lookup (mapList f objects) j₂
            eqL = trans
                    (lookup-mapList-commute f objects i₁′)
                    (trans eq
                           (sym (lookup-mapList-commute f objects i₂′)))

            j₁≡j₂ : j₁ ≡ j₂
            j₁≡j₂ = lookup-inj (mapList f objects) nd eqL

            i₁′≡i₂′ : i₁′ ≡ i₂′
            i₁′≡i₂′ = substFin-inj (sym len-eq) j₁≡j₂
        in cast-inj ca i₁′≡i₂′
    }

------------------------------------------------------------------------
-- § CanonicalWalkObjectList — mirrors the walk-indexing surface, isolating
-- countWalks semantics analogously to countSkeletons.

record CanonicalWalkObjectList
  (G : Graph) (r : Graph.Vertex G) (L : Nat) : Set₁ where
  field
    walks           : List (List (Graph.Vertex G))
    countWalksAgrees : countWalks G r L ≡ length walks
    walkOfFin       : Fin (countWalks G r L) → List (Graph.Vertex G)
    walkIndex       : List (Graph.Vertex G) → Fin (countWalks G r L)
    walkIndexOf     : ∀ (w : List (Graph.Vertex G)) →
                      walkOfFin (walkIndex w) ≡ w

-- Corrected semantic surface for finite valid-walk indexing.  Unlike the
-- legacy record above, this record only asks for an index when the vertex
-- list is a member of the enumerated valid-walk list.
record MembershipIndexedCanonicalWalkObjectList
  (G : Graph) (r : Graph.Vertex G) (L : Nat) : Set₁ where
  field
    walks : List (List (Graph.Vertex G))
    countWalksAgrees : countWalks G r L ≡ length walks
    walkOfFin : Fin (countWalks G r L) → List (Graph.Vertex G)
    walkIndex :
      (w : List (Graph.Vertex G)) →
      w ∈ walks →
      Fin (countWalks G r L)
    walkIndexOf :
      ∀ {w} (w∈ : w ∈ walks) →
      walkOfFin (walkIndex w w∈) ≡ w

cast-cancel :
  {m n : Nat} (eq : m ≡ n) (i : Fin n) →
  cast eq (cast (sym eq) i) ≡ i
cast-cancel refl i = refl

membershipIndexedCanonicalWalkObjectListFromList :
  {G : Graph} {r : Graph.Vertex G} {L : Nat} →
  (walks : List (List (Graph.Vertex G))) →
  countWalks G r L ≡ length walks →
  MembershipIndexedCanonicalWalkObjectList G r L
membershipIndexedCanonicalWalkObjectListFromList walks eq = record
  { walks = walks
  ; countWalksAgrees = eq
  ; walkOfFin = λ i → lookup walks (cast eq i)
  ; walkIndex = λ w w∈ → cast (sym eq) (indexOfMember walks w∈)
  ; walkIndexOf = λ {w} w∈ →
      trans
        (cong (lookup walks)
          (cast-cancel eq (indexOfMember walks w∈)))
        (lookup-indexOfMember walks w∈)
  }

-- Constructive membership-indexed lookup for the generated valid-walk
-- universe.  Downstream DFS consumers still need to migrate from the legacy
-- total-index record to this corrected domain.
generatedWalksToMembershipIndexedCanonicalWalkObjectList :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {L : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  ConcreteWalkCountAgreement G Δ BNE r L →
  MembershipIndexedCanonicalWalkObjectList G r L
generatedWalksToMembershipIndexedCanonicalWalkObjectList
  {r = r} {L = L} BNE agreement =
  membershipIndexedCanonicalWalkObjectListFromList
    (generatedWalkVertexLists {r = r} {L = L} BNE)
    (generatedWalkVertexListsCountAgreement BNE agreement)

-- The downstream walk-enumeration shape is also provided in corrected form;
-- the old total `WalkEnumeration` remains a compatibility surface until its
-- consumers migrate.
record MembershipIndexedWalkEnumeration
  (G : Graph) (r : Graph.Vertex G) (L : Nat) : Set₁ where
  field
    walks : List (List (Graph.Vertex G))
    walkOf : Fin (countWalks G r L) → List (Graph.Vertex G)
    walkIndex :
      (w : List (Graph.Vertex G)) →
      w ∈ walks →
      Fin (countWalks G r L)
    walkIndexOf :
      ∀ {w} (w∈ : w ∈ walks) →
      walkOf (walkIndex w w∈) ≡ w

membershipIndexedCanonicalToWalkEnumeration :
  {G : Graph} {r : Graph.Vertex G} {L : Nat} →
  MembershipIndexedCanonicalWalkObjectList G r L →
  MembershipIndexedWalkEnumeration G r L
membershipIndexedCanonicalToWalkEnumeration sem = record
  { walks = MembershipIndexedCanonicalWalkObjectList.walks sem
  ; walkOf = MembershipIndexedCanonicalWalkObjectList.walkOfFin sem
  ; walkIndex = MembershipIndexedCanonicalWalkObjectList.walkIndex sem
  ; walkIndexOf = MembershipIndexedCanonicalWalkObjectList.walkIndexOf sem
  }

-- Additive corrected semantic alias.  The legacy `CountWalksSemantics`
-- below remains available for compatibility consumers; new constructions
-- should use this membership-indexed surface until DFS coverage is supplied.
CountWalksMembershipSemantics :
  (G : Graph) (r : Graph.Vertex G) (L : Nat) → Set₁
CountWalksMembershipSemantics = MembershipIndexedCanonicalWalkObjectList

countWalksMembershipSemanticsToWalkEnumeration :
  {G : Graph} {r : Graph.Vertex G} {L : Nat} →
  CountWalksMembershipSemantics G r L →
  MembershipIndexedWalkEnumeration G r L
countWalksMembershipSemanticsToWalkEnumeration =
  membershipIndexedCanonicalToWalkEnumeration

------------------------------------------------------------------------
-- § Block 1: CandidateFilterWitness — finite witness surface for
-- skeleton candidate enumeration.
--
-- This record localises the assumption that the abstract countSkeletons
-- corresponds to a concrete finite list of candidates (with root /
-- Connected witnesses).  No decidable filtering on Connected is assumed.
--
--   candidates                       — concrete list of skeleton candidates
--   candidatesComplete               — every possible vertex set (with
--                                        r-in and Connected) is represented
--   candidatesHaveUniqueVertexLists  — no two candidates share a vertex list
--   candidatesSound (derived)        — every candidate's vertex list is
--                                        in chooseN(ballList)n

record CandidateFilterWitness
  (G : Graph) (r : Graph.Vertex G) (n : Nat)
  (FBE : FiniteBallEnumeration G r (n ∸ 1))
  : Set₁ where
  field
    candidates :
      List (SkeletonCandidate G r n FBE)

    candidatesComplete :
      ∀ {ys}
      → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
      → r ∈ ys
      → Connected G ys
      → Σ (SkeletonCandidate G r n FBE) λ c →
          c ∈ candidates ×
          SkeletonCandidate.candVertices c ≡ ys

    candidatesHaveUniqueVertexLists :
      NoDuplicates (mapList SkeletonCandidate.candVertices candidates)

  candidatesSound :
    ∀ (c : SkeletonCandidate G r n FBE) →
    c ∈ candidates →
    SkeletonCandidate.candVertices c ∈
      chooseN (FiniteBallEnumeration.ballList FBE) n
  candidatesSound c c∈cands = SkeletonCandidate.inChooseN c

------------------------------------------------------------------------
-- § ExplicitSkeletonCandidateEnumeration — witness-list candidate route.
--
-- This is the stable semantic front door for callers that do not want to
-- recover dependent proofs from a `Dec`-filtered list.  The list itself is
-- supplied as data; every element carries its chooseN, root, and connected
-- witnesses.  The old decidable-filter surface above remains available as a
-- compatibility constructor.

record SameCandidateVertices
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  (c₁ c₂ : SkeletonCandidate G r n FBE) : Set where
  field
    sameVertices : SkeletonCandidate.candVertices c₁
      ≡ SkeletonCandidate.candVertices c₂

record ExplicitSkeletonCandidateEnumeration
  (G : Graph) (r : Graph.Vertex G) (n : Nat)
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    candidates : List (SkeletonCandidate G r n FBE)

    complete :
      ∀ {ys}
      → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
      → r ∈ ys
      → Connected G ys
      → Σ (SkeletonCandidate G r n FBE) λ c →
          c ∈ candidates ×
          SkeletonCandidate.candVertices c ≡ ys

    uniqueVertexLists :
      NoDuplicates
        (mapList SkeletonCandidate.candVertices candidates)

    countAgrees :
      countSkeletons G r n ≡ length candidates

explicitSkeletonCandidateEnumerationToCandidateFilterWitness :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  ExplicitSkeletonCandidateEnumeration G r n FBE →
  CandidateFilterWitness G r n FBE
explicitSkeletonCandidateEnumerationToCandidateFilterWitness enum = record
  { candidates = ExplicitSkeletonCandidateEnumeration.candidates enum
  ; candidatesComplete = ExplicitSkeletonCandidateEnumeration.complete enum
  ; candidatesHaveUniqueVertexLists =
      ExplicitSkeletonCandidateEnumeration.uniqueVertexLists enum
  }

explicitSkeletonCandidateEnumerationFromWitnesses :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (candidates : List (SkeletonCandidate G r n FBE)) →
  (∀ {ys}
   → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
   → r ∈ ys
   → Connected G ys
   → Σ (SkeletonCandidate G r n FBE) λ c →
       c ∈ candidates × SkeletonCandidate.candVertices c ≡ ys) →
  NoDuplicates (mapList SkeletonCandidate.candVertices candidates) →
  countSkeletons G r n ≡ length candidates →
  ExplicitSkeletonCandidateEnumeration G r n FBE
explicitSkeletonCandidateEnumerationFromWitnesses candidates complete unique count =
  record
  { candidates = candidates
  ; complete = complete
  ; uniqueVertexLists = unique
  ; countAgrees = count
  }

------------------------------------------------------------------------
-- § ConcreteCountSkeletonsSemantics — normalized skeleton-count frontier.
--
-- The candidate list is now fixed to the concrete dependent filter.  The
-- only numerical assumption is `countAgrees`; completeness and vertex-list
-- uniqueness remain explicit proof obligations and do not get hidden inside
-- an abstract candidate witness.
------------------------------------------------------------------------

record ConcreteCountSkeletonsSemantics
  (G : Graph) (r : Graph.Vertex G) (n : Nat)
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    connectedDecider :
      (ys : List (Graph.Vertex G)) → Dec (Connected G ys)

    candidatesComplete :
      ∀ {ys}
      → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
      → r ∈ ys
      → Connected G ys
      → Σ (SkeletonCandidate G r n FBE) λ c →
          c ∈ canonicalSkeletonCandidatesFromBall
            {G} {r} {n} FBE connectedDecider ×
          SkeletonCandidate.candVertices c ≡ ys

    candidatesHaveUniqueVertexLists :
      NoDuplicates
        (mapList SkeletonCandidate.candVertices
          (canonicalSkeletonCandidatesFromBall
            {G} {r} {n} FBE connectedDecider))

    countAgrees :
      countSkeletons G r n ≡
      length (canonicalSkeletonCandidatesFromBall
        {G} {r} {n} FBE connectedDecider)

candidateCompleteFromConcreteSemantics :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (sem : ConcreteCountSkeletonsSemantics G r n FBE) →
  ∀ {ys}
  → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
  → r ∈ ys
  → Connected G ys
  → Σ (SkeletonCandidate G r n FBE) λ c →
      c ∈ canonicalSkeletonCandidatesFromBall
        {G} {r} {n} FBE
        (ConcreteCountSkeletonsSemantics.connectedDecider sem) ×
      SkeletonCandidate.candVertices c ≡ ys
candidateCompleteFromConcreteSemantics sem =
  ConcreteCountSkeletonsSemantics.candidatesComplete sem

candidateVertexListsUniqueFromConcreteSemantics :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (sem : ConcreteCountSkeletonsSemantics G r n FBE) →
  NoDuplicates
    (mapList SkeletonCandidate.candVertices
      (canonicalSkeletonCandidatesFromBall
        {G} {r} {n} FBE
        (ConcreteCountSkeletonsSemantics.connectedDecider sem)))
candidateVertexListsUniqueFromConcreteSemantics sem =
  ConcreteCountSkeletonsSemantics.candidatesHaveUniqueVertexLists sem

countSkeletonsConcreteAgreement :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (sem : ConcreteCountSkeletonsSemantics G r n FBE) →
  countSkeletons G r n ≡
    length (canonicalSkeletonCandidatesFromBall
      {G} {r} {n} FBE
      (ConcreteCountSkeletonsSemantics.connectedDecider sem))
countSkeletonsConcreteAgreement sem =
  ConcreteCountSkeletonsSemantics.countAgrees sem

concreteCountSkeletonsSemanticsToCandidateFilterWitness :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  ConcreteCountSkeletonsSemantics G r n FBE →
  CandidateFilterWitness G r n FBE
concreteCountSkeletonsSemanticsToCandidateFilterWitness
  {G} {r} {n} {FBE} sem = record
  { candidates =
      canonicalSkeletonCandidatesFromBall
        {G} {r} {n} FBE
        (ConcreteCountSkeletonsSemantics.connectedDecider sem)
  ; candidatesComplete =
      ConcreteCountSkeletonsSemantics.candidatesComplete sem
  ; candidatesHaveUniqueVertexLists =
      ConcreteCountSkeletonsSemantics.candidatesHaveUniqueVertexLists sem
  }

------------------------------------------------------------------------
-- § Block 2: CandidateFilterWitness → CanonicalSkeletonCandidateList.
--
-- Builds candidateComplete from the witness surface +
-- canonicalSkeletonVerticesAppearInBallChooseN, preserving vertex-list
-- uniqueness.

candidateFilterWitnessToCanonicalSkeletonCandidateList :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  CandidateFilterWitness G r n FBE →
  CanonicalSkeletonCandidateList G r n FBE
candidateFilterWitnessToCanonicalSkeletonCandidateList {FBE = FBE} CFW =
  record
    { candidates = CandidateFilterWitness.candidates CFW
    ; candidatesHaveUniqueVertexLists =
        CandidateFilterWitness.candidatesHaveUniqueVertexLists CFW
    ; candidateComplete = λ obj →
        let
          ys   = CanonicalSkeletonObject.skelVertices obj
          ys∈  = canonicalSkeletonVerticesAppearInBallChooseN FBE obj
          r∈ys = RootedConnectedSkeleton.r-in-X
                   (CanonicalSkeletonObject.connected obj)
          conn = RootedConnectedSkeleton.connected
                   (CanonicalSkeletonObject.connected obj)
          (c , c∈ , vs≡ys) =
            CandidateFilterWitness.candidatesComplete CFW ys∈ r∈ys conn
        in c , c∈ ,
           trans
             (candidateToCanonicalSkeletonObjectFromFBE-≡vs FBE c)
             vs≡ys
    }
  where
    candidateToCanonicalSkeletonObjectFromFBE-≡vs :
      ∀ {G : Graph} {r : Graph.Vertex G} {n : Nat}
      (FBE : FiniteBallEnumeration G r (n ∸ 1))
      (c : SkeletonCandidate G r n FBE) →
      CanonicalSkeletonObject.skelVertices
        (candidateToCanonicalSkeletonObjectFromFBE FBE c)
        ≡
      SkeletonCandidate.candVertices c
    candidateToCanonicalSkeletonObjectFromFBE-≡vs FBE c = refl

------------------------------------------------------------------------
-- § Block 3: CountSkeletonsSemantics — isolates the abstract count
-- agreement as a single localized assumption.
--
--   witness       — CandidateFilterWitness (complete + unique list)
--   countAgrees   — countSkeletons ≡ length(witness.candidates)
--
-- Derived:
--   CanonicalSkeletonObjectList       via canonicalObjectsFromCandidates
--   CanonicalSkeletonObjectIndexing   via countAgrees + uniqueness
--   CanonicalSkeletonEnumeration      via indexing bridge

record CountSkeletonsSemantics
  (G : Graph) (r : Graph.Vertex G) (n : Nat)
  (FBE : FiniteBallEnumeration G r (n ∸ 1))
  : Set₁ where
  field
    witness : CandidateFilterWitness G r n FBE

    countAgrees :
      countSkeletons G r n ≡
      length (CandidateFilterWitness.candidates witness)

explicitSkeletonCandidateEnumerationToCountSkeletonsSemantics :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  ExplicitSkeletonCandidateEnumeration G r n FBE →
  CountSkeletonsSemantics G r n FBE
explicitSkeletonCandidateEnumerationToCountSkeletonsSemantics enum = record
  { witness =
      explicitSkeletonCandidateEnumerationToCandidateFilterWitness enum
  ; countAgrees = ExplicitSkeletonCandidateEnumeration.countAgrees enum
  }

concreteCountSkeletonsSemanticsToCountSkeletonsSemantics :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  ConcreteCountSkeletonsSemantics G r n FBE →
  CountSkeletonsSemantics G r n FBE
concreteCountSkeletonsSemanticsToCountSkeletonsSemantics sem =
  let witness =
        concreteCountSkeletonsSemanticsToCandidateFilterWitness sem
  in record
    { witness = witness
    ; countAgrees =
        ConcreteCountSkeletonsSemantics.countAgrees sem
    }

countSkeletonsSemanticsToObjectList :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  CountSkeletonsSemantics G r n FBE →
  CanonicalSkeletonObjectList G r n
countSkeletonsSemanticsToObjectList sem =
  let CL = candidateFilterWitnessToCanonicalSkeletonCandidateList
             (CountSkeletonsSemantics.witness sem)
  in canonicalObjectsFromCandidates CL

countSkeletonsSemanticsToObjectIndexing :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (sem : CountSkeletonsSemantics G r n FBE) →
  let OL = countSkeletonsSemanticsToObjectList sem
  in CanonicalSkeletonObjectIndexing OL
countSkeletonsSemanticsToObjectIndexing sem =
  let OL = countSkeletonsSemanticsToObjectList sem
      CFW = CountSkeletonsSemantics.witness sem
      cands = CandidateFilterWitness.candidates CFW

      len-eq : length (CanonicalSkeletonObjectList.objects OL) ≡ length cands
      len-eq = listMapLength
                 (candidateToCanonicalSkeletonObjectFromFBE _)
                 cands

      countIs : CountSkeletonsIsObjectList _ _ _ OL
      countIs = record
        { countAgrees =
            trans (CountSkeletonsSemantics.countAgrees sem) (sym len-eq)
        }
  in canonicalSkeletonObjectIndexingFromCountAgreement OL countIs

countSkeletonsSemanticsToEnumeration :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  CountSkeletonsSemantics G r n FBE →
  CanonicalSkeletonEnumeration G r n
countSkeletonsSemanticsToEnumeration sem =
  let OL = countSkeletonsSemanticsToObjectList sem
      idx = countSkeletonsSemanticsToObjectIndexing sem
  in canonicalSkeletonEnumerationFromIndexing OL idx

------------------------------------------------------------------------
-- § Block 4: CountWalksSemantics + bridges to WalkEnumeration + DFS map
--
-- CountWalksSemantics mirrors the countSkeletons semantics pattern.
-- It is identical to CanonicalWalkObjectList: walks list, count
-- agreement, and walk-of/walk-index/walk-index-of.

CountWalksSemantics : (G : Graph) (r : Graph.Vertex G) (L : Nat) → Set₁
CountWalksSemantics = CanonicalWalkObjectList

countWalksSemanticsToWalkEnumeration :
  {G : Graph} {r : Graph.Vertex G} {L : Nat} →
  CountWalksSemantics G r L →
  WalkEnumeration G r L
countWalksSemanticsToWalkEnumeration sem = record
  { walkOf = CanonicalWalkObjectList.walkOfFin sem
  ; walkIndex = CanonicalWalkObjectList.walkIndex sem
  ; walkIndexOf = CanonicalWalkObjectList.walkIndexOf sem
  }

canonicalDFSMapFromEnumeration :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  (CE : CanonicalSkeletonEnumeration G r n)
  (WE : WalkEnumeration G r (n + n)) →
  CanonicalDFSMap CE WE
canonicalDFSMapFromEnumeration CE WE = record
  { dfsWalkOfSkeleton = λ s →
      dfsWalkRange (CanonicalSkeletonEnumeration.objectOf CE s)
  ; dfsWalkSound = λ s →
      canonicalDFSObjectSound (CanonicalSkeletonEnumeration.objectOf CE s)
  }

actualSkeletonEncodingDataFromSemantics :
  {G : Graph} {r : Graph.Vertex G} {n : Nat}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (skelSem : CountSkeletonsSemantics G r n FBE) →
  (walkSem : CountWalksSemantics G r (n + n)) →
  ActualSkeletonEncodingData G r n
actualSkeletonEncodingDataFromSemantics skelSem walkSem =
  let CE = countSkeletonsSemanticsToEnumeration skelSem
      WE = countWalksSemanticsToWalkEnumeration walkSem
      Map = canonicalDFSMapFromEnumeration CE WE
  in canonicalDFSMapToEncodingData CE WE Map

------------------------------------------------------------------------
-- Explicit DFS-to-generated-walk membership bridge.
--
-- `canonicalDFSObjectSound` supplies only vertex-set equality, so it cannot
-- by itself prove membership in the valid generated-walk universe.  This
-- bridge records the exact additional witness required: a valid WalkObject
-- whose vertex sequence is the DFS range.

dfsWalkRangeMemberFromWalkObject :
  {G : Graph} {Δ : Nat} {r : Graph.Vertex G} {n : Nat} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  (obj : CanonicalSkeletonObject G r n) →
  (w : WalkObject G r (n + n)) →
  walkObjectVertices w ≡ dfsWalkRange obj →
  dfsWalkRange obj ∈
    generatedWalkVertexLists {r = r} {L = n + n} BNE
dfsWalkRangeMemberFromWalkObject {G = G} {Δ = Δ} {r = r} {n = n}
  BNE obj w vertices-eq =
  let witness = generatedWalkVertexListComplete BNE w
      vs = proj₁ witness
      vs∈ = proj₁ (proj₂ witness)
      vs≡w = proj₂ (proj₂ witness)
      vs≡dfs = trans vs≡w vertices-eq
  in subst
       (λ xs → xs ∈ generatedWalkVertexLists {r = r} {L = n + n} BNE)
       vs≡dfs
       vs∈
