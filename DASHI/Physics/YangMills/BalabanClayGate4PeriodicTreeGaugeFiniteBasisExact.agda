module DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeFiniteBasisExact where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (_∈_; PositiveBond)

import DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeCoordinatesExact as Tree
import DASHI.Physics.YangMills.BalabanClayGate4FiniteTangentMatrixRepresentationExact as Matrix
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support

------------------------------------------------------------------------
-- Off-tree labels as a finite tangent basis index list.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions",
-- Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- The tree combinatorics already computes the exact off-tree bond list.  This
-- module attaches a vector assigned to each positive bond, coordinates and a
-- reconstruction formula to the existing finite basis carrier.  The actual
-- analytic content is reduced to reconstruction and linear independence on the
-- selected off-tree list.
------------------------------------------------------------------------

data Truth : Set where
  truth : Truth

record PeriodicTreeGaugeBasisInputs
    (n : Nat) (Scalar Vector : Set) : Set₁ where
  field
    treeCoordinates : Tree.CertifiedPeriodicTreeGaugeCoordinates n

    basisVector : PositiveBond (suc n) → Vector
    coordinates : Vector → PositiveBond (suc n) → Scalar
    linearCombination :
      List (PositiveBond (suc n)) →
      (PositiveBond (suc n) → Scalar) → Vector

    reconstruction : ∀ vector →
      vector ≡ linearCombination
        (Tree.offTreePositiveBonds (Tree.tree treeCoordinates))
        (coordinates vector)

    LinearlyIndependentOn :
      List (PositiveBond (suc n)) →
      (PositiveBond (suc n) → Vector) → Set

    offTreeBasisIndependent :
      LinearlyIndependentOn
        (Tree.offTreePositiveBonds (Tree.tree treeCoordinates))
        basisVector

open PeriodicTreeGaugeBasisInputs public

asFiniteTangentBasis :
  ∀ {n Scalar Vector} →
  PeriodicTreeGaugeBasisInputs n Scalar Vector →
  Matrix.FiniteTangentBasis
    (PositiveBond (suc n)) Vector Scalar
asFiniteTangentBasis inputs = record
  { Matrix.FiniteTangentBasis.indices =
      Tree.offTreePositiveBonds (Tree.tree (treeCoordinates inputs))
  ; Matrix.FiniteTangentBasis.basisVector = basisVector inputs
  ; Matrix.FiniteTangentBasis.coordinates = coordinates inputs
  ; Matrix.FiniteTangentBasis.linearCombination = linearCombination inputs
  ; Matrix.FiniteTangentBasis.BasisIndexComplete = λ index → Truth
  ; Matrix.FiniteTangentBasis.basisIndexComplete = λ index → truth
  ; Matrix.FiniteTangentBasis.basisComplete = reconstruction inputs
  ; Matrix.FiniteTangentBasis.LinearlyIndependent = λ selectedBasis →
      LinearlyIndependentOn inputs
        (Tree.offTreePositiveBonds (Tree.tree (treeCoordinates inputs)))
        selectedBasis
  ; Matrix.FiniteTangentBasis.basisIndependent =
      offTreeBasisIndependent inputs
  }

listedBasisIndexIsOffTree :
  ∀ {n Scalar Vector}
    (inputs : PeriodicTreeGaugeBasisInputs n Scalar Vector)
    bond →
  bond ∈ Matrix.indices (asFiniteTangentBasis inputs) →
  Tree.OffTreeBond (Tree.tree (treeCoordinates inputs)) bond
listedBasisIndexIsOffTree inputs bond =
  Tree.offTreePositiveBondsSound
    (Tree.tree (treeCoordinates inputs)) bond

periodicTreeGaugeBasisDimension :
  ∀ {n Scalar Vector} →
  PeriodicTreeGaugeBasisInputs n Scalar Vector → Nat
periodicTreeGaugeBasisDimension inputs =
  Support.listLength
    (Matrix.indices (asFiniteTangentBasis inputs))

periodicTreeGaugeBasisCarrierLevel : ProofLevel
periodicTreeGaugeBasisCarrierLevel = machineChecked

periodicTreeGaugeBasisSupportLevel : ProofLevel
periodicTreeGaugeBasisSupportLevel = machineChecked

periodicTreeGaugeBasisDimensionDefinitionLevel : ProofLevel
periodicTreeGaugeBasisDimensionDefinitionLevel = computed

physicalOffTreeBasisReconstructionInputsLevel : ProofLevel
physicalOffTreeBasisReconstructionInputsLevel = conditional

physicalOffTreeBasisIndependenceInputsLevel : ProofLevel
physicalOffTreeBasisIndependenceInputsLevel = conditional
