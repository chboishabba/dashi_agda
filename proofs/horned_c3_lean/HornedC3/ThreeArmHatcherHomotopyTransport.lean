import HornedC3.ThreeArmRadiusCutHatcherTransport

/-! Homotopy-source transport for the existing 3-arm cover.
Original roots: Alexander 1924, Hatcher Algebraic Topology Example 2B.2,
and classical van Kampen. Exact Lean implementation donor:
Deicyde/hatcher-at, pinned WedgeFundamentalGroup.lean.
All source-space homotopy equivalences remain geometric INPUTS. -/

noncomputable section
open scoped ContinuousMap
open Hatcher.VanKampen
namespace DASHI.AlexanderHornedC3

universe u v
variable {X : Type u} [TopologicalSpace X]

def threeArmHomotopySourcesEquivPi1
    (x₀ : X) (C : Set X) (S : Fin 3 → Set X)
    (h : CentralPi1CoverCertificates x₀ C S)
    (W : Fin 3 → Type v) [∀ i, TopologicalSpace (W i)]
    (w : ∀ i, W i)
    (e : ∀ i, W i ≃ₕ (collarMember C S i))
    (hb : ∀ i, (e i).toFun (w i) =
      (⟨x₀, collarBasepoint C S x₀ h.central_basepoint i⟩ :
        collarMember C S i)) :
    Monoid.CoprodI (fun i : Fin 3 =>
      FundamentalGroup (W i) (w i)) ≃* FundamentalGroup X x₀ :=
  (Hatcher.coprodIEquiv
    (fun i => Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq
      (e i) (w i)
      (⟨x₀, collarBasepoint C S x₀ h.central_basepoint i⟩ :
        collarMember C S i)
      (hb i))).trans
    (centralPi1CoverFreeProduct x₀ C S h)

end DASHI.AlexanderHornedC3
