module DASHI.Core.FormalStructureKind where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole

-- Mathematical structure is kept distinct from the contextual job played by a
-- term.  A Hamiltonian may play an operator, observable, invariant, or
-- optimization role; the role and the structure therefore cannot be collapsed.
data FormalStructureKind : Set where
  plainCarrierStructure : FormalStructureKind
  algebraStructure : FormalStructureKind
  groupStructure : FormalStructureKind
  categoryStructure : FormalStructureKind
  graphStructure : FormalStructureKind
  topologyStructure : FormalStructureKind
  geometryStructure : FormalStructureKind
  metricStructure : FormalStructureKind
  operatorStructure : FormalStructureKind
  hamiltonianStructure : FormalStructureKind
  spectralStructure : FormalStructureKind
  statisticalStructure : FormalStructureKind
  probabilityStructure : FormalStructureKind
  dynamicalStructure : FormalStructureKind
  controlStructure : FormalStructureKind
  provenanceStructure : FormalStructureKind
  governanceStructure : FormalStructureKind
  historicalStructure : FormalStructureKind
  namedStructure : FormalStructureKind

record StructuredRole (D : RoleFamily) : Set₁ where
  field
    structuredRole    : FormalRole
    structureKind     : FormalStructureKind
    structuredPayload : RoleType D structuredRole

open StructuredRole public

-- Structure relabelling requires an explicit witness.  Merely reusing the same
-- payload does not identify two mathematical structures.
record StructureBridge (from to : FormalStructureKind) : Set where
  field
    structureBridgeWitness : Set

open StructureBridge public
