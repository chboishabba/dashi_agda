import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.CWComplex.Abstract.Basic

/-!
# Real CW structures: Mathlib reuse, not a surrogate finite-cell type

The Mathlib primary proof dependency defines genuine point-set CW structures
via disk maps, cell disjointness, frontiers, closure finiteness and weak topology:
  * Topology.CWComplex / RelCWComplex (classical)
  * TopCat.CWComplex (categorical colimit)

This consumer requires an ACTUAL Mathlib CW structure and does NOT infer
one from DASHI's finite 27-cell data, CP1 rational cochains, or ternary
pants address correspondence. Constructing the particular surfaces or their
topological CW structures remains an external supplier obligation.

Mathematical sources: J.H.C. Whitehead, Combinatorial Homotopy (1949);
A. Hatcher, Algebraic Topology, Appendix; Mathlib contributors.
No Whitehead weak-homotopy equivalence theorem is claimed.
-/

namespace DASHI.ExoticTopology

universe u
variable {X : Type u} [TopologicalSpace X]

/-- Source-bound recognition of a *genuine* topological CW subset.
    Inhabitance requires Mathlib CW data; no Boolean promotion token. -/
structure RealisedCW where
  carrier : Set X
  cw : Topology.CWComplex carrier

/-- Only accept an already proved Mathlib CW structure. -/
def RealisedCW.ofMathlib (C : Set X) [Topology.CWComplex C] :
    RealisedCW (X := X) :=
  ⟨C, inferInstance⟩

/-- Reexport the proof obligation in the source's own type. -/
def RealisedCW.hasCW (R : RealisedCW (X := X)) :
    Topology.CWComplex R.carrier :=
  R.cw

/-- The acceptance type for a named object has no constructor that
    converts a finite combinatorial cell receipt to a CW theorem. -/
structure RecognisedExoticCW where
  underlying : Set X
  realised : RealisedCW (X := X)
  sameCarrier : realised.carrier = underlying

def RecognisedExoticCW.provedCW
    (R : RecognisedExoticCW (X := X)) :
    Topology.CWComplex R.underlying := by
  rw [← R.sameCarrier]
  exact R.realised.cw

end DASHI.ExoticTopology
