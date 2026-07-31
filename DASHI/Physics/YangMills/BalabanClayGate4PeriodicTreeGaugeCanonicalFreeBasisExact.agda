module DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeCanonicalFreeBasisExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Empty; Dec; yes; no; _∈_; here; there; PositiveBond)

import DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeCoordinatesExact as Tree
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4FiniteTangentMatrixRepresentationExact as Matrix

------------------------------------------------------------------------
-- Canonical finite free basis on the exact off-tree list.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press; open-access
-- reissue (2022). DOI: 10.1017/9781009290395.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- The earlier adapter left reconstruction and independence as fields of a
-- physical fluctuation carrier.  This module closes the genuinely finite part:
-- the computed off-tree list has a canonical position index Fin n, its scalar
-- coordinate tuples have standard coordinate vectors, coordinate extraction
-- and reconstruction are mutual inverses, and the standard vectors are
-- biorthogonal to coordinate extraction.  Relating this free coordinate space
-- to Bałaban's analytic fluctuation fibre remains a separate physical map.
------------------------------------------------------------------------

data Fin : Nat → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc : ∀ {n} → Fin n → Fin (suc n)

finZeroNotSuccessor : ∀ {n} {index : Fin n} →
  fzero ≡ fsuc index → Empty
finZeroNotSuccessor ()

finSuccessorNotZero : ∀ {n} {index : Fin n} →
  fsuc index ≡ fzero → Empty
finSuccessorNotZero ()

finSuccessorInjective : ∀ {n} {left right : Fin n} →
  fsuc left ≡ fsuc right → left ≡ right
finSuccessorInjective refl = refl

finDecidableEquality : ∀ {n} (left right : Fin n) →
  Dec (left ≡ right)
finDecidableEquality fzero fzero = yes refl
finDecidableEquality fzero (fsuc right) = no finZeroNotSuccessor
finDecidableEquality (fsuc left) fzero = no finSuccessorNotZero
finDecidableEquality (fsuc left) (fsuc right)
  with finDecidableEquality left right
... | yes equality = yes (cong fsuc equality)
... | no inequality =
  no (λ equality → inequality (finSuccessorInjective equality))

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

mapMembership :
  ∀ {A B : Set} (function : A → B)
    {value : A} {values : List A} →
  value ∈ values → function value ∈ mapList function values
mapMembership function here = here
mapMembership function (there membership) =
  there (mapMembership function membership)

allFin : (n : Nat) → List (Fin n)
allFin zero = []
allFin (suc n) = fzero ∷ mapList fsuc (allFin n)

allFinComplete : ∀ {n} (index : Fin n) → index ∈ allFin n
allFinComplete {zero} ()
allFinComplete {suc n} fzero = here
allFinComplete {suc n} (fsuc index) =
  there (mapMembership fsuc (allFinComplete index))

data Vec (Scalar : Set) : Nat → Set where
  vnil : Vec Scalar zero
  _v∷_ : ∀ {n} → Scalar → Vec Scalar n → Vec Scalar (suc n)

infixr 20 _v∷_

lookupVec : ∀ {Scalar n} → Vec Scalar n → Fin n → Scalar
lookupVec (value v∷ values) fzero = value
lookupVec (value v∷ values) (fsuc index) = lookupVec values index

tabulateVec : ∀ {Scalar n} → (Fin n → Scalar) → Vec Scalar n
tabulateVec {n = zero} function = vnil
tabulateVec {n = suc n} function =
  function fzero v∷ tabulateVec (λ index → function (fsuc index))

lookupTabulate :
  ∀ {Scalar n} (function : Fin n → Scalar) index →
  lookupVec (tabulateVec function) index ≡ function index
lookupTabulate {n = zero} function ()
lookupTabulate {n = suc n} function fzero = refl
lookupTabulate {n = suc n} function (fsuc index) =
  lookupTabulate (λ inner → function (fsuc inner)) index

tabulateLookup :
  ∀ {Scalar n} (vector : Vec Scalar n) →
  tabulateVec (lookupVec vector) ≡ vector
tabulateLookup vnil = refl
tabulateLookup (value v∷ values) =
  cong (value v∷_) (tabulateLookup values)

record PointedScalar (Scalar : Set) : Set₁ where
  field
    zeroScalar oneScalar : Scalar

open PointedScalar public

delta : ∀ {Scalar n} →
  PointedScalar Scalar → Fin n → Fin n → Scalar
delta pointed left right with finDecidableEquality left right
... | yes equality = oneScalar pointed
... | no inequality = zeroScalar pointed

standardBasisVector : ∀ {Scalar n} →
  PointedScalar Scalar → Fin n → Vec Scalar n
standardBasisVector pointed index =
  tabulateVec (delta pointed index)

standardCoordinate : ∀ {Scalar n} →
  Vec Scalar n → Fin n → Scalar
standardCoordinate = lookupVec

standardReconstruct : ∀ {Scalar n} →
  (Fin n → Scalar) → Vec Scalar n
standardReconstruct = tabulateVec

standardCoordinateOfBasis :
  ∀ {Scalar n} (pointed : PointedScalar Scalar) left right →
  standardCoordinate (standardBasisVector pointed left) right
  ≡ delta pointed left right
standardCoordinateOfBasis pointed left right =
  lookupTabulate (delta pointed left) right

standardReconstructionExact :
  ∀ {Scalar n} (vector : Vec Scalar n) →
  standardReconstruct (standardCoordinate vector) ≡ vector
standardReconstructionExact = tabulateLookup

standardCoordinatesReconstructExact :
  ∀ {Scalar n} (coordinates : Fin n → Scalar) index →
  standardCoordinate (standardReconstruct coordinates) index
  ≡ coordinates index
standardCoordinatesReconstructExact = lookupTabulate

Biorthogonal : ∀ {Scalar n} →
  PointedScalar Scalar → (Fin n → Vec Scalar n) → Set
Biorthogonal pointed family =
  ∀ left right →
    standardCoordinate (family left) right
    ≡ delta pointed left right

standardBasisBiorthogonal :
  ∀ {Scalar n} (pointed : PointedScalar Scalar) →
  Biorthogonal pointed (standardBasisVector pointed)
standardBasisBiorthogonal = standardCoordinateOfBasis

canonicalFiniteTangentBasis :
  ∀ {Scalar n} → PointedScalar Scalar →
  Matrix.FiniteTangentBasis
    (Fin n) (Vec Scalar n) Scalar
canonicalFiniteTangentBasis {n = n} pointed = record
  { Matrix.FiniteTangentBasis.indices = allFin n
  ; Matrix.FiniteTangentBasis.basisVector = standardBasisVector pointed
  ; Matrix.FiniteTangentBasis.coordinates = standardCoordinate
  ; Matrix.FiniteTangentBasis.linearCombination =
      λ selected coefficients → standardReconstruct coefficients
  ; Matrix.FiniteTangentBasis.BasisIndexComplete =
      λ index → index ∈ allFin n
  ; Matrix.FiniteTangentBasis.basisIndexComplete = allFinComplete
  ; Matrix.FiniteTangentBasis.basisComplete =
      λ vector → sym (standardReconstructionExact vector)
  ; Matrix.FiniteTangentBasis.LinearlyIndependent =
      Biorthogonal pointed
  ; Matrix.FiniteTangentBasis.basisIndependent =
      standardBasisBiorthogonal pointed
  }

bondAt : ∀ {A : Set} (values : List A) →
  Fin (Support.listLength values) → A
bondAt [] ()
bondAt (value ∷ values) fzero = value
bondAt (value ∷ values) (fsuc index) = bondAt values index

bondAtBelongs :
  ∀ {A : Set} (values : List A)
    (index : Fin (Support.listLength values)) →
  bondAt values index ∈ values
bondAtBelongs [] ()
bondAtBelongs (value ∷ values) fzero = here
bondAtBelongs (value ∷ values) (fsuc index) =
  there (bondAtBelongs values index)

offTreeDimension :
  ∀ {n} → Periodic.PeriodicTree n → Nat
offTreeDimension tree =
  Support.listLength (Tree.offTreePositiveBonds tree)

OffTreePosition :
  ∀ {n} → Periodic.PeriodicTree n → Set
OffTreePosition tree = Fin (offTreeDimension tree)

offTreeBondAt :
  ∀ {n} (tree : Periodic.PeriodicTree n) →
  OffTreePosition tree → PositiveBond (suc n)
offTreeBondAt tree = bondAt (Tree.offTreePositiveBonds tree)

offTreeBondAtIsOffTree :
  ∀ {n} (tree : Periodic.PeriodicTree n)
    (index : OffTreePosition tree) →
  Tree.OffTreeBond tree (offTreeBondAt tree index)
offTreeBondAtIsOffTree tree index =
  Tree.offTreePositiveBondsSound tree (offTreeBondAt tree index)
    (bondAtBelongs (Tree.offTreePositiveBonds tree) index)

canonicalPeriodicTreeGaugeBasis :
  ∀ {n Scalar} (pointed : PointedScalar Scalar)
    (tree : Periodic.PeriodicTree n) →
  Matrix.FiniteTangentBasis
    (OffTreePosition tree)
    (Vec Scalar (offTreeDimension tree)) Scalar
canonicalPeriodicTreeGaugeBasis pointed tree =
  canonicalFiniteTangentBasis pointed

finiteCoordinateTupleRoundTripLevel : ProofLevel
finiteCoordinateTupleRoundTripLevel = machineChecked

finiteStandardBasisBiorthogonalityLevel : ProofLevel
finiteStandardBasisBiorthogonalityLevel = machineChecked

periodicOffTreePositionToBondLevel : ProofLevel
periodicOffTreePositionToBondLevel = machineChecked

periodicOffTreeCanonicalBasisLevel : ProofLevel
periodicOffTreeCanonicalBasisLevel = machineChecked

physicalFreeCoordinatesToFluctuationFibreInputsLevel : ProofLevel
physicalFreeCoordinatesToFluctuationFibreInputsLevel = conditional
