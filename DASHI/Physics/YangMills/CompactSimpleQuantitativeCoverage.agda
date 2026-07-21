module DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Compact-simple group coverage for the group-parametric Balaban stack.
--
-- The classification is represented directly at the compact-group level.
-- SU n, odd/even SO n, and Sp n are kept separate so that the low-rank
-- identifications do not have to be quotient-bookkept in downstream RG code.
------------------------------------------------------------------------

data CompactSimpleLieGroup : Set where
  SU : Nat → CompactSimpleLieGroup
  SOodd : Nat → CompactSimpleLieGroup
  SOeven : Nat → CompactSimpleLieGroup
  Sp : Nat → CompactSimpleLieGroup
  G2 F4 E6 E7 E8 : CompactSimpleLieGroup

------------------------------------------------------------------------
-- Uniform local analytic package.
------------------------------------------------------------------------

record QuantitativeCompactLiePackage
    (Scalar LieElement GroupElement : Set)
    (G : CompactSimpleLieGroup) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set
    norm : LieElement → Scalar
    distance : GroupElement → GroupElement → Scalar
    bracket : LieElement → LieElement → LieElement
    bch : LieElement → LieElement → LieElement
    exp : LieElement → GroupElement
    log : GroupElement → LieElement
    adjoint : GroupElement → LieElement → LieElement
    haarDensity : LieElement → Scalar

    localRadius bracketConstant bchConstant expLogConstant
      adjointConstant haarDensityConstant : Scalar

    localRadiusPositive : StrictLess zero localRadius

    bracketBound : ∀ left right →
      LessEqual (norm (bracket left right))
        (multiply bracketConstant (multiply (norm left) (norm right)))

    bchRemainder : LieElement → LieElement → LieElement
    bchRemainderBound : ∀ left right →
      LessEqual (norm (bchRemainder left right))
        (multiply bchConstant
          (multiply (add (norm left) (norm right))
            (multiply (add (norm left) (norm right))
              (add (norm left) (norm right)))))

    InLocalLieChart : LieElement → Set
    InLocalGroupChart : GroupElement → Set

    expLogLocalEquivalence :
      (∀ element → InLocalLieChart element → log (exp element) ≡ element) ×
      (∀ element → InLocalGroupChart element → exp (log element) ≡ element)

    adjointBound : ∀ group element →
      LessEqual (norm (adjoint group element))
        (multiply adjointConstant (norm element))

    haarLocalDensityBound : ∀ element →
      InLocalLieChart element →
      LessEqual (haarDensity element) haarDensityConstant

open QuantitativeCompactLiePackage public

------------------------------------------------------------------------
-- Standard compact-Lie analytic authority.
------------------------------------------------------------------------

record CompactSimpleQuantitativeAuthority
    (Scalar LieElement GroupElement : Set) : Set₁ where
  field
    suPackage : ∀ rank →
      QuantitativeCompactLiePackage Scalar LieElement GroupElement (SU rank)
    soOddPackage : ∀ rank →
      QuantitativeCompactLiePackage Scalar LieElement GroupElement (SOodd rank)
    soEvenPackage : ∀ rank →
      QuantitativeCompactLiePackage Scalar LieElement GroupElement (SOeven rank)
    spPackage : ∀ rank →
      QuantitativeCompactLiePackage Scalar LieElement GroupElement (Sp rank)

    g2Package : QuantitativeCompactLiePackage Scalar LieElement GroupElement G2
    f4Package : QuantitativeCompactLiePackage Scalar LieElement GroupElement F4
    e6Package : QuantitativeCompactLiePackage Scalar LieElement GroupElement E6
    e7Package : QuantitativeCompactLiePackage Scalar LieElement GroupElement E7
    e8Package : QuantitativeCompactLiePackage Scalar LieElement GroupElement E8

open CompactSimpleQuantitativeAuthority public

------------------------------------------------------------------------
-- N1. Classical-family quantitative packages.
------------------------------------------------------------------------

suNHasQuantitativePackage :
  ∀ {Scalar LieElement GroupElement} →
  CompactSimpleQuantitativeAuthority Scalar LieElement GroupElement →
  ∀ rank →
  QuantitativeCompactLiePackage Scalar LieElement GroupElement (SU rank)
suNHasQuantitativePackage authority = suPackage authority

soNHasQuantitativePackage :
  ∀ {Scalar LieElement GroupElement} →
  CompactSimpleQuantitativeAuthority Scalar LieElement GroupElement →
  ∀ rank →
  QuantitativeCompactLiePackage Scalar LieElement GroupElement (SOodd rank) ×
  QuantitativeCompactLiePackage Scalar LieElement GroupElement (SOeven rank)
soNHasQuantitativePackage authority rank =
  soOddPackage authority rank , soEvenPackage authority rank

spNHasQuantitativePackage :
  ∀ {Scalar LieElement GroupElement} →
  CompactSimpleQuantitativeAuthority Scalar LieElement GroupElement →
  ∀ rank →
  QuantitativeCompactLiePackage Scalar LieElement GroupElement (Sp rank)
spNHasQuantitativePackage authority = spPackage authority

------------------------------------------------------------------------
-- N2. Exceptional-family quantitative packages.
------------------------------------------------------------------------

g2HasQuantitativePackage :
  ∀ {Scalar LieElement GroupElement} →
  CompactSimpleQuantitativeAuthority Scalar LieElement GroupElement →
  QuantitativeCompactLiePackage Scalar LieElement GroupElement G2
g2HasQuantitativePackage = g2Package

f4HasQuantitativePackage :
  ∀ {Scalar LieElement GroupElement} →
  CompactSimpleQuantitativeAuthority Scalar LieElement GroupElement →
  QuantitativeCompactLiePackage Scalar LieElement GroupElement F4
f4HasQuantitativePackage = f4Package

e6HasQuantitativePackage :
  ∀ {Scalar LieElement GroupElement} →
  CompactSimpleQuantitativeAuthority Scalar LieElement GroupElement →
  QuantitativeCompactLiePackage Scalar LieElement GroupElement E6
e6HasQuantitativePackage = e6Package

e7HasQuantitativePackage :
  ∀ {Scalar LieElement GroupElement} →
  CompactSimpleQuantitativeAuthority Scalar LieElement GroupElement →
  QuantitativeCompactLiePackage Scalar LieElement GroupElement E7
e7HasQuantitativePackage = e7Package

e8HasQuantitativePackage :
  ∀ {Scalar LieElement GroupElement} →
  CompactSimpleQuantitativeAuthority Scalar LieElement GroupElement →
  QuantitativeCompactLiePackage Scalar LieElement GroupElement E8
e8HasQuantitativePackage = e8Package

------------------------------------------------------------------------
-- N3. Classification coverage.
------------------------------------------------------------------------

compactSimpleHasQuantitativePackage :
  ∀ {Scalar LieElement GroupElement} →
  CompactSimpleQuantitativeAuthority Scalar LieElement GroupElement →
  (G : CompactSimpleLieGroup) →
  QuantitativeCompactLiePackage Scalar LieElement GroupElement G
compactSimpleHasQuantitativePackage authority (SU rank) =
  suNHasQuantitativePackage authority rank
compactSimpleHasQuantitativePackage authority (SOodd rank) =
  soOddPackage authority rank
compactSimpleHasQuantitativePackage authority (SOeven rank) =
  soEvenPackage authority rank
compactSimpleHasQuantitativePackage authority (Sp rank) =
  spNHasQuantitativePackage authority rank
compactSimpleHasQuantitativePackage authority G2 =
  g2HasQuantitativePackage authority
compactSimpleHasQuantitativePackage authority F4 =
  f4HasQuantitativePackage authority
compactSimpleHasQuantitativePackage authority E6 =
  e6HasQuantitativePackage authority
compactSimpleHasQuantitativePackage authority E7 =
  e7HasQuantitativePackage authority
compactSimpleHasQuantitativePackage authority E8 =
  e8HasQuantitativePackage authority

------------------------------------------------------------------------
-- N4. Group constants independent of lattice/cutoff/background data.
------------------------------------------------------------------------

record GroupConstantIndependence
    (Scalar Lattice Scale Background Patch : Set)
    (G : CompactSimpleLieGroup) : Set₁ where
  field
    Constants : Set
    constants : Constants
    LocalConstants :
      CompactSimpleLieGroup → Lattice → Scale → Background → Patch → Scalar
    constantValue : Constants → Scalar
    LessEqual : Scalar → Scalar → Set
    localConstantsBound : ∀ lattice scale background patch →
      LessEqual
        (LocalConstants G lattice scale background patch)
        (constantValue constants)

open GroupConstantIndependence public

groupConstantsIndependentOfLattice :
  ∀ {Scalar Lattice Scale Background Patch} →
  (G : CompactSimpleLieGroup) →
  (dataSet : GroupConstantIndependence
    Scalar Lattice Scale Background Patch G) →
  Σ (Constants dataSet)
    (λ constants →
      ∀ lattice scale background patch →
      LessEqual dataSet
        (LocalConstants dataSet G lattice scale background patch)
        (constantValue dataSet constants))
groupConstantsIndependentOfLattice G dataSet =
  constants dataSet , localConstantsBound dataSet

------------------------------------------------------------------------
-- Proof-level ledger.
------------------------------------------------------------------------

compactSimpleClassificationEliminationLevel : ProofLevel
compactSimpleClassificationEliminationLevel = machineChecked

classicalFamilyPackageAssemblyLevel : ProofLevel
classicalFamilyPackageAssemblyLevel = machineChecked

exceptionalFamilyPackageAssemblyLevel : ProofLevel
exceptionalFamilyPackageAssemblyLevel = machineChecked

latticeIndependenceExtractionLevel : ProofLevel
latticeIndependenceExtractionLevel = machineChecked

compactSimpleQuantitativeAuthorityLevel : ProofLevel
compactSimpleQuantitativeAuthorityLevel = standardImported
