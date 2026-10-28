import HornedC3.ThreeArmRadiusConnectedHatcherTransport
import Mathlib.Topology.Compactness.Compact

/-!
# Hatcher stage-to-wild-limit compact absorption

Source: Allen Hatcher, Algebraic Topology Example 2B.2, pp. 171-172:
the increasing OPEN exteriors Y_n exhaust the complement E of the
limiting horned ball; every compact loop and loop homotopy image
therefore lies in a single Y_n. This is an elementary consequence of
the exact Mathlib theorem IsCompact.elim_directed_cover.

The theorem below closes ONLY the topological compact-absorption
step for a supplied monotone open exhaustion. It does not construct
Hatcher's 3D linked handlebodies, identify the finite-stage free
generators or prove the group colimit injective. It does not conflate
the tame finite ball B_n with the handlebody X_n.

Proof owner: Mathlib IsCompact.elim_directed_cover.
Historical source owner: Hatcher (and Alexander 1924 for the wild ball).
Selected stage consumer: DASHI #1244, source-written; Lean kernel
compilation is not claimed without an exact-head receipt.
-/

noncomputable section

namespace DASHI.AlexanderHornedC3

universe u v
variable {X : Type u} [TopologicalSpace X]

/-- Every compact subset of an increasing open cover sits inside
one finite stage. Monotonicity and openness are indispensable: a
mere set-theoretic union does not suffice. -/
theorem compactSetAbsorbedByOpenStages
    (Y : ℕ → Set X) (hopen : ∀ n, IsOpen (Y n))
    (hmono : Monotone Y)
    (K : Set X) (hcompact : IsCompact K)
    (hcover : K ⊆ ⋃ n, Y n) :
    ∃ n, K ⊆ Y n := by
  apply hcompact.elim_directed_cover Y hopen hcover
  intro i j
  refine ⟨max i j, hmono (le_max_left i j),
    hmono (le_max_right i j)⟩

/-- Continuous images of arbitrary compact source spaces (the
unit interval and its square among them) are absorbed in one
finite-stage exterior. Thus both loops and their homotopies
factor through a finite Y_n at the SET LEVEL. -/
theorem compactMapAbsorbedByOpenStages
    {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, X))
    (Y : ℕ → Set X) (hopen : ∀ n, IsOpen (Y n))
    (hmono : Monotone Y) (hcover : Set.univ ⊆ ⋃ n, Y n) :
    ∃ n, ∀ t, f t ∈ Y n := by
  have hk : IsCompact (Set.range f) := by
    simpa only [Set.image_univ] using
      ((isCompact_univ : IsCompact (Set.univ : Set T)).image f.continuous)
  obtain ⟨n, hn⟩ :=
    compactSetAbsorbedByOpenStages Y hopen hmono
      (Set.range f) hk (Set.Subset.trans (Set.subset_univ _) hcover)
  exact ⟨n, fun t => hn (Set.mem_range_self t)⟩


/-- Stronger constructive factorization: every continuous map from
any compact source T factors via a genuine continuous map into one
specific Y_n. For T = I this applies to loops; for T=I×I it
applies to their homotopies, subject to their existing endpoint
conditions. No new homotopy or meridian generators are supplied. -/
theorem compactMapFactorsThroughOpenStage
    {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, X))
    (Y : ℕ → Set X) (hopen : ∀ n, IsOpen (Y n))
    (hmono : Monotone Y) (hcover : Set.univ ⊆ ⋃ n, Y n) :
    ∃ n, ∃ (g : C(T, Y n)), ∀ t, (g t : X) = f t := by
  obtain ⟨n, hn⟩ :=
    compactMapAbsorbedByOpenStages f Y hopen hmono hcover
  refine ⟨n, ⟨fun t => ⟨f t, hn t⟩,
    f.continuous.subtype_mk _⟩, ?_⟩
  intro t
  rfl


/-- Relative version of compact-map absorption: the increasing open sets
need cover only the IMAGE of the map, not the whole ambient space.
For Hatcher's Y_n = ℝ³ \ X_n this distinction is essential, because
their union is the exterior E, a proper subset of ℝ³. -/
theorem compactMapAbsorbedByOpenStagesRelative
    {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, X))
    (Y : ℕ → Set X) (hopen : ∀ n, IsOpen (Y n))
    (hmono : Monotone Y)
    (himage : Set.range f ⊆ ⋃ n, Y n) :
    ∃ n, ∀ t, f t ∈ Y n := by
  have hk : IsCompact (Set.range f) := by
    simpa only [Set.image_univ] using
      ((isCompact_univ : IsCompact (Set.univ : Set T)).image f.continuous)
  obtain ⟨n, hn⟩ :=
    compactSetAbsorbedByOpenStages Y hopen hmono
      (Set.range f) hk himage
  exact ⟨n, fun t => hn (Set.mem_range_self t)⟩

/-- Factor a compact-source map into ONE open stage, requiring only
that its own image lie in the union. Endpoint or relative-boundary
equalities are preserved because the underlying map is definitionally
unchanged after coercion to the ambient type. -/
theorem compactMapFactorsThroughOpenStageRelative
    {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, X))
    (Y : ℕ → Set X) (hopen : ∀ n, IsOpen (Y n))
    (hmono : Monotone Y)
    (himage : Set.range f ⊆ ⋃ n, Y n) :
    ∃ n, ∃ (g : C(T, Y n)), ∀ t, (g t : X) = f t := by
  obtain ⟨n, hn⟩ :=
    compactMapAbsorbedByOpenStagesRelative f Y hopen hmono himage
  refine ⟨n, ⟨fun t => ⟨f t, hn t⟩,
    f.continuous.subtype_mk _⟩, ?_⟩
  intro t
  rfl

/-- Consumer shaped exactly for Hatcher's NESTED CLOSED handlebodies
X_n: any continuous map from a compact domain whose image misses
the LIMIT intersection of X_n factors into the complement of some
single finite-stage X_n. The input X_n is still a required, actual
geometric construction; this theorem does NOT construct it, infer
meridian injections, or form the fundamental-group colimit.

The same theorem applies to loop images (compact interval) and
loop-homotopy images (compact square) without assuming that their
images exhaust the ambient 3-space. -/
theorem compactMapFactorsThroughNestedClosedExteriors
    {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, X))
    (H : ℕ → Set X) (hclosed : ∀ n, IsClosed (H n))
    (hanti : Antitone H)
    (havoid : ∀ t, f t ∉ ⋂ n, H n) :
    ∃ n, ∃ (g : C(T, (H n)ᶜ)),
      ∀ t, (g t : X) = f t := by
  have hopen : ∀ n, IsOpen ((H n)ᶜ) :=
    fun n => (hclosed n).isOpen_compl
  have hmono : Monotone (fun n => (H n)ᶜ) := by
    intro i j hij x hx hxin
    exact hx (hanti hij hxin)
  have himage : Set.range f ⊆ ⋃ n, (H n)ᶜ := by
    rw [← Set.compl_iInter]
    rintro x ⟨t, rfl⟩
    exact havoid t
  exact compactMapFactorsThroughOpenStageRelative
    f (fun n => (H n)ᶜ) hopen hmono himage

end DASHI.AlexanderHornedC3
