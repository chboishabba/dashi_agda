import HornedC3.ThreeArmVanKampen

/-!
# Exact set-theoretic collar overlap computation

The cover members are U_i = C ∪ S_i, with a shared central region C and
pairwise disjoint satellite-only regions S_i. This proof establishes
U_i ∩ U_j = C for distinct i,j, and triple intersections equal C
whenever at least two indices differ. These are the actual set identities
needed before applying the already formalized Hatcher van Kampen theorem.

The disjointness hypothesis has a concrete Euclidean envelope regression
in scripts/alexander_horned_c3_collars_audit.py. That finite regression is
NOT a formal proof about the wild-ball embedding or a complete collar.
-/

open Set

namespace DASHI.AlexanderHornedC3

universe u

variable {X : Type u}

/-- Central collar plus one sector, expressed with actual subsets. -/
def collarMember (C : Set X) (S : Fin 3 → Set X) (i : Fin 3) :
    Set X := C ∪ S i

theorem collarPairIntersectionEq
    (C : Set X) (S : Fin 3 → Set X)
    (separate : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i j : Fin 3) (hij : i ≠ j) :
    collarMember C S i ∩ collarMember C S j = C := by
  ext x
  constructor
  · intro hx
    rcases hx.1 with hc | hs
    · exact hc
    rcases hx.2 with hc | ht
    · exact hc
    exact False.elim (Set.disjoint_left.mp (separate i j hij) hs ht)
  · intro hc
    exact ⟨Or.inl hc, Or.inl hc⟩

theorem collarTripleIntersectionEq
    (C : Set X) (S : Fin 3 → Set X)
    (separate : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i j k : Fin 3) (hij : i ≠ j) :
    collarMember C S i ∩ collarMember C S j ∩
      collarMember C S k = C := by
  rw [collarPairIntersectionEq C S separate i j hij]
  ext x
  constructor
  · intro h
    exact h.1
  · intro hc
    exact ⟨hc, Or.inl hc⟩

theorem collarCoverOpen
    [TopologicalSpace X] (C : Set X) (S : Fin 3 → Set X)
    (hc : IsOpen C) (hs : ∀ i, IsOpen (S i)) :
    ∀ i, IsOpen (collarMember C S i) := by
  intro i
  exact hc.union (hs i)

theorem collarBasepoint
    (C : Set X) (S : Fin 3 → Set X)
    (x₀ : X) (hx₀ : x₀ ∈ C) :
    ∀ i, x₀ ∈ collarMember C S i := by
  intro i
  exact Or.inl hx₀

end DASHI.AlexanderHornedC3
