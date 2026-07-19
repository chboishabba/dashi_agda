module DASHI.Biology.Protein.ProteinConformationAttractor where

-- A protein sequence determines a constrained conformational system, not a
-- definitionally unique static structure.  Environment and history remain
-- explicit because folding may be metastable, assisted, or path-dependent.
record ProteinConformationSystem : Set₁ where
  field
    Sequence      : Set
    Conformation  : Set
    Environment   : Set
    Perturbation  : Set
    Attractor     : Set

    step          : Sequence → Environment → Conformation → Conformation
    perturb       : Perturbation → Conformation → Conformation

    ChemicallyAdmissible : Sequence → Conformation → Set
    StericallyAdmissible : Conformation → Set
    CovalentlyCompatible : Sequence → Conformation → Set
    InBasin       : Attractor → Conformation → Set
    StableAt      : Sequence → Environment → Attractor → Set
    MetastableAt  : Sequence → Environment → Attractor → Set

record ConformationalAttractorWitness
  (P : ProteinConformationSystem) : Set₁ where
  open ProteinConformationSystem P
  field
    sequence    : Sequence
    environment : Environment
    attractor   : Attractor

    stable      : StableAt sequence environment attractor

    forwardInvariant :
      (x : Conformation) → InBasin attractor x →
      InBasin attractor (step sequence environment x)

    admissibleInBasin :
      (x : Conformation) → InBasin attractor x →
      ChemicallyAdmissible sequence x

record FoldingRecoveryWitness
  (P : ProteinConformationSystem) : Set₁ where
  open ProteinConformationSystem P
  field
    sequence    : Sequence
    environment : Environment
    initial     : Conformation
    folded      : Conformation
    attractor   : Attractor

    initialAdmissible : ChemicallyAdmissible sequence initial
    foldedAdmissible  : ChemicallyAdmissible sequence folded
    foldedInBasin     : InBasin attractor folded
    attractorStable   : StableAt sequence environment attractor

    Reachable : Conformation → Conformation → Set
    foldingPath : Reachable initial folded

-- Distinct attractors may coexist for the same sequence and environment.  This
-- is the interface consumed by misfolding, amyloid, chaperone, and allostery
-- lanes; no uniqueness theorem is manufactured here.
record MultipleAttractorWitness
  (P : ProteinConformationSystem) : Set₁ where
  open ProteinConformationSystem P
  field
    sequence    : Sequence
    environment : Environment
    attractor₁ attractor₂ : Attractor
    distinctAttractors : Set
    firstStable  : StableAt sequence environment attractor₁
    secondStable : StableAt sequence environment attractor₂
