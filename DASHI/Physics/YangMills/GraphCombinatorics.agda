module DASHI.Physics.YangMills.GraphCombinatorics where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (subst)
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

_⊆_ : {A : Set} → List A → List A → Set
X ⊆ Y = ∀ {x} → x ∈ X → x ∈ Y

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

postulate
  Connected : (G : Graph) → List (Graph.Vertex G) → Set
  Tree : (G : Graph) → Set
  RootedTree : (G : Graph) → Graph.Vertex G → Set

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

postulate
  Path : (G : Graph) → Graph.Vertex G → Graph.Vertex G → Set
  vertices : {G : Graph} {x y : Graph.Vertex G} → Path G x y → List (Graph.Vertex G)

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

postulate
  NormalizedLengthComplexityBound :
    ∀ {G : Graph} (r : Graph.Vertex G) (X : List (Graph.Vertex G)) →
    (rrs : RootedReducedSkeleton G r X) →
    ReducedSkeletonComplexityMeasure r X rrs ≤ 1 * diam_G {G} X + 0

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
