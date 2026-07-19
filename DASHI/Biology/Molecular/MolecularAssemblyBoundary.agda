module DASHI.Biology.Molecular.MolecularAssemblyBoundary where

open import DASHI.Biology.Core.ContextIndexedSystem

-- Atomic shell recovery supplies admissible valence data, but a molecule also
-- requires bond, geometry, charge, stereochemical, and environmental witnesses.
record MolecularAssemblySystem : Set₁ where
  field
    Atom          : Set
    AtomicState   : Set
    Bond          : Set
    Geometry      : Set
    Stereochemistry : Set
    Environment   : Set
    Molecule      : Set

    atomicState   : Atom → AtomicState
    assemble      : Environment → Molecule

    BondAdmissible : Atom → Atom → Bond → Set
    GeometryAdmissible : Molecule → Geometry → Set
    StereoAdmissible   : Molecule → Stereochemistry → Set
    ChargeBalanced     : Molecule → Set
    ElectronCompatible : Molecule → Set

    StableIn      : Environment → Molecule → Set

record MolecularAssemblyWitness
  (M : MolecularAssemblySystem) : Set₁ where
  open MolecularAssemblySystem M
  field
    environment : Environment
    molecule    : Molecule
    geometry    : Geometry
    stereo      : Stereochemistry

    geometryAdmissible : GeometryAdmissible molecule geometry
    stereoAdmissible   : StereoAdmissible molecule stereo
    chargeBalanced     : ChargeBalanced molecule
    electronCompatible : ElectronCompatible molecule
    stable              : StableIn environment molecule

-- Reactions are context-indexed rewrites.  A stable molecule does not by itself
-- determine a unique reaction path or product.
record MolecularReactionSystem
  (M : MolecularAssemblySystem) : Set₁ where
  open MolecularAssemblySystem M
  field
    ReactionContext : Set
    ReactionPath    : Set

    ReactsTo : ReactionContext → Molecule → Molecule → Set
    pathFor  : ReactionContext → Molecule → Molecule → ReactionPath

    ConservedQuantity : Set
    conserved : ReactionContext → Molecule → Molecule → ConservedQuantity → Set

-- Bridge obligation from the atomic layer.  The atomic periodic-table theorem
-- must be consumed explicitly rather than assumed from atom names.
record AtomicToMolecularBridge
  (M : MolecularAssemblySystem) : Set₁ where
  field
    AtomicChemistryRecovered : Set
    atomicChemistryWitness   : AtomicChemistryRecovered

    valenceSupportsAssembly :
      MolecularAssemblySystem.Molecule M → Set

    orbitalOverlapSupportsBonding :
      MolecularAssemblySystem.Molecule M → Set

    manyBodyGeometryControlled :
      MolecularAssemblySystem.Molecule M → Set
