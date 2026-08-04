module DASHI.Reasoning.SinthomeFiniteWitness where

open import DASHI.Core.Prelude

import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Reasoning.SinthomeTypedStabilisation as Sinthome

------------------------------------------------------------------------
-- Finite executable witness for the sinthomatic coherence theorem surface.
--
-- The integrated state is coherent, retains the declared residual and keeps
-- the rupture trace.  It is provably not equivalent to the erasure state.
------------------------------------------------------------------------

data FabricState : Set where
  rupturedState integratedState erasedState : FabricState

data Coherent : FabricState → Set where
  integratedCoherent : Coherent integratedState
  erasedCoherent : Coherent erasedState

data ResidualPresent : Residual.ResidualLevel → FabricState → Set where
  integratedResidual : ResidualPresent Residual.partial integratedState

data MemoryPreserved : FabricState → FabricState → Set where
  ruptureTracePreserved : MemoryPreserved rupturedState integratedState

data Equivalent : FabricState → FabricState → Set where
  sameState : ∀ {state} → Equivalent state state

integratedNotEquivalentToErasure :
  ¬ Equivalent integratedState erasedState
integratedNotEquivalentToErasure ()

canonicalIntegrationPath : Sinthome.StabilisationPath
canonicalIntegrationPath = record
  { pathSteps =
      "retain rupture trace"
      ∷ "change incidence role"
      ∷ "restore declared coherence"
      ∷ []
  ; sourceVersion = "ruptured"
  ; targetVersion = "integrated"
  ; pathProvenance = "finite sinthome witness" ∷ []
  ; pathReceipt = "path-indexed finite stabilisation"
  }

canonicalFiniteSinthome :
  Sinthome.AdmissibleSinthome
    FabricState Coherent ResidualPresent MemoryPreserved Equivalent
canonicalFiniteSinthome = record
  { before = rupturedState
  ; after = integratedState
  ; erasureCandidate = erasedState
  ; residual = Residual.partial
  ; path = canonicalIntegrationPath
  ; coherenceAfter = integratedCoherent
  ; residualAfter = integratedResidual
  ; memoryFromBefore = ruptureTracePreserved
  ; notEquivalentToErasure = integratedNotEquivalentToErasure
  ; mode = Sinthome.sinthomaticIntegrationMode
  ; modeIsSinthomatic = refl
  ; stabilisationReceipt =
      "Concrete finite witness: coherence is restored with residual and memory retained, and the result is not erasure."
  }

finiteSinthomeCoherent : Coherent integratedState
finiteSinthomeCoherent =
  Sinthome.sinthomeRestoresCoherence canonicalFiniteSinthome

finiteSinthomeRetainsResidual :
  ResidualPresent Residual.partial integratedState
finiteSinthomeRetainsResidual =
  Sinthome.sinthomeRetainsResidual canonicalFiniteSinthome

finiteSinthomePreservesTrace :
  MemoryPreserved rupturedState integratedState
finiteSinthomePreservesTrace =
  Sinthome.sinthomePreservesMemory canonicalFiniteSinthome

finiteSinthomeNotErasure :
  ¬ Equivalent integratedState erasedState
finiteSinthomeNotErasure =
  Sinthome.sinthomeIsNotErasure canonicalFiniteSinthome
