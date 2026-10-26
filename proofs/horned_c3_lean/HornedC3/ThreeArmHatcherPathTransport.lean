import HornedC3.ThreeArmHatcherHomotopyTransport

/-!
# Based-path version of the geometric Hatcher satellite endgame

Actual geometry: each source W_i -> actual open member U_i must be a
homotopy equivalence, and a REAL path in U_i must carry its image
basepoint to the fixed common x₀. Reusing Mathlib's
FundamentalGroup.fundamentalGroupMulEquivOfPath avoids the artificial
requirement that e_i(w_i) be definitionally/equationally x₀.

The existing DASHI paths γ_i through central C should eventually
instantiate these U_i paths, after establishing the source points.

Source roots: Hatcher Algebraic Topology Example 2B.2 and §1.1
basepoint change, Alexander 1924, classical van Kampen.
Implementation donors: pinned Deicyde/hatcher-at and Mathlib.
No proof of actual wild satellite source equivalences is asserted.
-/

noncomputable section
open scoped ContinuousMap
open Hatcher.VanKampen
namespace DASHI.AlexanderHornedC3

universe u v
variable {X : Type u} [TopologicalSpace X]

def threeArmHomotopyPathSourcesEquivPi1
    (x₀ : X) (C : Set X) (S : Fin 3 → Set X)
    (h : CentralPi1CoverCertificates x₀ C S)
    (W : Fin 3 → Type v) [∀ i, TopologicalSpace (W i)]
    (w : ∀ i, W i)
    (e : ∀ i, W i ≃ₕ (collarMember C S i))
    (p : ∀ i,
      Path ((e i).toFun (w i))
        (⟨x₀, collarBasepoint C S x₀ h.central_basepoint i⟩ :
          collarMember C S i)) :
    Monoid.CoprodI (fun i : Fin 3 =>
      FundamentalGroup (W i) (w i)) ≃* FundamentalGroup X x₀ :=
  (Hatcher.coprodIEquiv
    (fun i =>
      (Hatcher.fundamentalGroupMulEquivOfHomotopyEquiv
        (e i) (w i)).trans
        (FundamentalGroup.fundamentalGroupMulEquivOfPath (p i)))).trans
    (centralPi1CoverFreeProduct x₀ C S h)

end DASHI.AlexanderHornedC3
