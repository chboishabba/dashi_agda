module DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeSU2FreeBasisExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Dec; yes; no; _∈_; here; there; PositiveBond)

import DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeCoordinatesExact as Tree
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeCanonicalFreeBasisExact as Free
import DASHI.Physics.YangMills.BalabanClayGate4FiniteCoordinateMatrixEquivalenceExact as Coordinate
import DASHI.Physics.YangMills.BalabanClayGate4FiniteTangentMatrixRepresentationExact as Matrix
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic

------------------------------------------------------------------------
-- Canonical off-tree × colour basis for an SU(2) tangent fibre.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press; open-access
-- reissue (2022). DOI: 10.1017/9781009290395.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- SU(2) has three Lie-algebra coordinates.  If the exact off-tree list has m
-- entries, the free tree-gauge tangent carrier is represented here by m rows
-- of three scalar coordinates.  Its canonical basis is indexed by
--
--   OffTreePosition × Fin 3,
--
-- has exactly 3m entries, reconstructs every coordinate tuple, and is
-- biorthogonal to coordinate extraction.  The remaining physical statement is
-- only the analytic identification of this free carrier with Bałaban's chosen
-- background-field tangent slice.
------------------------------------------------------------------------

three : Nat
three = suc (suc (suc zero))

infixr 20 _+ᴺ_

_+ᴺ_ : Nat → Nat → Nat
zero +ᴺ right = right
suc left +ᴺ right = suc (left +ᴺ right)

infixr 25 _*ᴺ_

_*ᴺ_ : Nat → Nat → Nat
zero *ᴺ right = zero
suc left *ᴺ right = right +ᴺ (left *ᴺ right)

record IndexPair (Left Right : Set) : Set where
  constructor indexPair
  field
    leftIndex : Left
    rightIndex : Right

open IndexPair public

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

infixr 15 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ right = right
(value ∷ left) ++ right = value ∷ (left ++ right)

cartesian :
  ∀ {Left Right : Set} →
  List Left → List Right → List (IndexPair Left Right)
cartesian [] rights = []
cartesian (left ∷ lefts) rights =
  mapList (indexPair left) rights ++ cartesian lefts rights

mapMembership :
  ∀ {A B : Set} (function : A → B)
    {value : A} {values : List A} →
  value ∈ values → function value ∈ mapList function values
mapMembership function here = here
mapMembership function (there membership) =
  there (mapMembership function membership)

appendMembershipLeft :
  ∀ {A : Set} {value : A} {left right : List A} →
  value ∈ left → value ∈ (left ++ right)
appendMembershipLeft here = here
appendMembershipLeft (there membership) =
  there (appendMembershipLeft membership)

appendMembershipRight :
  ∀ {A : Set} {value : A} {left right : List A} →
  value ∈ right → value ∈ (left ++ right)
appendMembershipRight {left = []} membership = membership
appendMembershipRight {left = _ ∷ left} membership =
  there (appendMembershipRight {left = left} membership)

cartesianMembership :
  ∀ {Left Right : Set}
    {left : Left} {right : Right}
    {lefts : List Left} {rights : List Right} →
  left ∈ lefts → right ∈ rights →
  indexPair left right ∈ cartesian lefts rights
cartesianMembership {lefts = []} () rightMembership
cartesianMembership {left = left} {right = right}
    {lefts = left ∷ lefts} here rightMembership =
  appendMembershipLeft
    (mapMembership (indexPair left) rightMembership)
cartesianMembership {left = left} {right = right}
    {lefts = other ∷ lefts} (there leftMembership) rightMembership =
  appendMembershipRight
    (cartesianMembership leftMembership rightMembership)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

mapLength :
  ∀ {A B : Set} (function : A → B) values →
  listLength (mapList function values) ≡ listLength values
mapLength function [] = refl
mapLength function (value ∷ values) =
  cong suc (mapLength function values)

appendLength :
  ∀ {A : Set} (left right : List A) →
  listLength (left ++ right)
  ≡ listLength left +ᴺ listLength right
appendLength [] right = refl
appendLength (value ∷ left) right =
  cong suc (appendLength left right)

cartesianLength :
  ∀ {Left Right : Set}
    (lefts : List Left) (rights : List Right) →
  listLength (cartesian lefts rights)
  ≡ listLength lefts *ᴺ listLength rights
cartesianLength [] rights = refl
cartesianLength (left ∷ lefts) rights =
  trans
    (appendLength (mapList (indexPair left) rights)
      (cartesian lefts rights))
    (trans
      (cong
        (λ length → length +ᴺ listLength (cartesian lefts rights))
        (mapLength (indexPair left) rights))
      (cong (listLength rights +ᴺ_)
        (cartesianLength lefts rights)))

allFinLength : ∀ n → listLength (Free.allFin n) ≡ n
allFinLength zero = refl
allFinLength (suc n) =
  cong suc (trans (mapLength Free.fsuc (Free.allFin n)) (allFinLength n))

SU2Colour : Set
SU2Colour = Free.Fin three

OffTreeColourIndex :
  ∀ {n} → Periodic.PeriodicTree n → Set
OffTreeColourIndex tree =
  IndexPair (Free.OffTreePosition tree) SU2Colour

offTreeColourIndices :
  ∀ {n} (tree : Periodic.PeriodicTree n) →
  List (OffTreeColourIndex tree)
offTreeColourIndices tree =
  cartesian
    (Free.allFin (Free.offTreeDimension tree))
    (Free.allFin three)

offTreeColourIndicesComplete :
  ∀ {n} (tree : Periodic.PeriodicTree n)
    (index : OffTreeColourIndex tree) →
  index ∈ offTreeColourIndices tree
offTreeColourIndicesComplete tree (indexPair bond colour) =
  cartesianMembership
    (Free.allFinComplete bond)
    (Free.allFinComplete colour)

offTreeColourDimension :
  ∀ {n} → Periodic.PeriodicTree n → Nat
offTreeColourDimension tree =
  Free.offTreeDimension tree *ᴺ three

offTreeColourIndexCountExact :
  ∀ {n} (tree : Periodic.PeriodicTree n) →
  listLength (offTreeColourIndices tree)
  ≡ offTreeColourDimension tree
offTreeColourIndexCountExact tree =
  trans
    (cartesianLength
      (Free.allFin (Free.offTreeDimension tree))
      (Free.allFin three))
    (trans
      (cong
        (λ leftLength → leftLength *ᴺ listLength (Free.allFin three))
        (allFinLength (Free.offTreeDimension tree)))
      (cong (Free.offTreeDimension tree *ᴺ_)
        (allFinLength three)))

SU2CoordinateTuple : Set → Nat → Set
SU2CoordinateTuple Scalar bondCount =
  Free.Vec (Free.Vec Scalar three) bondCount

lookupSU2Coordinate :
  ∀ {Scalar bondCount} →
  SU2CoordinateTuple Scalar bondCount →
  IndexPair (Free.Fin bondCount) SU2Colour → Scalar
lookupSU2Coordinate tuple (indexPair bond colour) =
  Free.lookupVec (Free.lookupVec tuple bond) colour

tabulateSU2Coordinates :
  ∀ {Scalar bondCount} →
  (IndexPair (Free.Fin bondCount) SU2Colour → Scalar) →
  SU2CoordinateTuple Scalar bondCount
tabulateSU2Coordinates coefficients =
  Free.tabulateVec
    (λ bond → Free.tabulateVec
      (λ colour → coefficients (indexPair bond colour)))

lookupTabulateSU2 :
  ∀ {Scalar bondCount}
    (coefficients : IndexPair (Free.Fin bondCount) SU2Colour → Scalar)
    index →
  lookupSU2Coordinate (tabulateSU2Coordinates coefficients) index
  ≡ coefficients index
lookupTabulateSU2 coefficients (indexPair bond colour) =
  trans
    (cong (λ row → Free.lookupVec row colour)
      (Free.lookupTabulate
        (λ selectedBond → Free.tabulateVec
          (λ selectedColour →
            coefficients (indexPair selectedBond selectedColour)))
        bond))
    (Free.lookupTabulate
      (λ selectedColour → coefficients (indexPair bond selectedColour))
      colour)

tabulateLookupSU2 :
  ∀ {Scalar bondCount}
    (tuple : SU2CoordinateTuple Scalar bondCount) →
  tabulateSU2Coordinates (lookupSU2Coordinate tuple) ≡ tuple
tabulateLookupSU2 tuple =
  Coordinate.vecExt (λ bond →
    trans
      (Free.lookupTabulate
        (λ selectedBond → Free.tabulateVec
          (λ colour →
            lookupSU2Coordinate tuple (indexPair selectedBond colour)))
        bond)
      (Free.tabulateLookup (Free.lookupVec tuple bond)))

pairDelta :
  ∀ {Scalar bondCount} →
  Free.PointedScalar Scalar →
  IndexPair (Free.Fin bondCount) SU2Colour →
  IndexPair (Free.Fin bondCount) SU2Colour → Scalar
pairDelta pointed (indexPair leftBond leftColour)
    (indexPair rightBond rightColour)
  with Free.finDecidableEquality leftBond rightBond
     | Free.finDecidableEquality leftColour rightColour
... | yes bondEquality | yes colourEquality =
  Free.oneScalar pointed
... | no bondInequality | colourDecision =
  Free.zeroScalar pointed
... | yes bondEquality | no colourInequality =
  Free.zeroScalar pointed

su2BasisVector :
  ∀ {Scalar bondCount} →
  Free.PointedScalar Scalar →
  IndexPair (Free.Fin bondCount) SU2Colour →
  SU2CoordinateTuple Scalar bondCount
su2BasisVector pointed index =
  tabulateSU2Coordinates (pairDelta pointed index)

su2CoordinateOfBasis :
  ∀ {Scalar bondCount}
    (pointed : Free.PointedScalar Scalar)
    left right →
  lookupSU2Coordinate (su2BasisVector pointed left) right
  ≡ pairDelta pointed left right
su2CoordinateOfBasis pointed left right =
  lookupTabulateSU2 (pairDelta pointed left) right

SU2Biorthogonal :
  ∀ {Scalar bondCount} →
  Free.PointedScalar Scalar →
  (IndexPair (Free.Fin bondCount) SU2Colour →
    SU2CoordinateTuple Scalar bondCount) → Set
SU2Biorthogonal pointed family =
  ∀ left right →
    lookupSU2Coordinate (family left) right
    ≡ pairDelta pointed left right

su2BasisBiorthogonal :
  ∀ {Scalar bondCount}
    (pointed : Free.PointedScalar Scalar) →
  SU2Biorthogonal pointed (su2BasisVector pointed)
su2BasisBiorthogonal = su2CoordinateOfBasis

canonicalPeriodicTreeGaugeSU2Basis :
  ∀ {n Scalar}
    (pointed : Free.PointedScalar Scalar)
    (tree : Periodic.PeriodicTree n) →
  Matrix.FiniteTangentBasis
    (OffTreeColourIndex tree)
    (SU2CoordinateTuple Scalar (Free.offTreeDimension tree))
    Scalar
canonicalPeriodicTreeGaugeSU2Basis pointed tree = record
  { Matrix.FiniteTangentBasis.indices = offTreeColourIndices tree
  ; Matrix.FiniteTangentBasis.basisVector = su2BasisVector pointed
  ; Matrix.FiniteTangentBasis.coordinates = lookupSU2Coordinate
  ; Matrix.FiniteTangentBasis.linearCombination =
      λ selected coefficients → tabulateSU2Coordinates coefficients
  ; Matrix.FiniteTangentBasis.BasisIndexComplete =
      λ index → index ∈ offTreeColourIndices tree
  ; Matrix.FiniteTangentBasis.basisIndexComplete =
      offTreeColourIndicesComplete tree
  ; Matrix.FiniteTangentBasis.basisComplete =
      λ tuple → sym (tabulateLookupSU2 tuple)
  ; Matrix.FiniteTangentBasis.LinearlyIndependent =
      SU2Biorthogonal pointed
  ; Matrix.FiniteTangentBasis.basisIndependent =
      su2BasisBiorthogonal pointed
  }

offTreeColourBond :
  ∀ {n} (tree : Periodic.PeriodicTree n) →
  OffTreeColourIndex tree → PositiveBond (suc n)
offTreeColourBond tree index =
  Free.offTreeBondAt tree (leftIndex index)

offTreeColourBondIsOffTree :
  ∀ {n} (tree : Periodic.PeriodicTree n)
    (index : OffTreeColourIndex tree) →
  Tree.OffTreeBond tree (offTreeColourBond tree index)
offTreeColourBondIsOffTree tree index =
  Free.offTreeBondAtIsOffTree tree (leftIndex index)

periodicTreeGaugeSU2BasisIndexCountLevel : ProofLevel
periodicTreeGaugeSU2BasisIndexCountLevel = machineChecked

periodicTreeGaugeSU2TupleRoundTripLevel : ProofLevel
periodicTreeGaugeSU2TupleRoundTripLevel = machineChecked

periodicTreeGaugeSU2BasisBiorthogonalityLevel : ProofLevel
periodicTreeGaugeSU2BasisBiorthogonalityLevel = machineChecked

periodicTreeGaugeSU2BasisCarrierLevel : ProofLevel
periodicTreeGaugeSU2BasisCarrierLevel = machineChecked

periodicTreeGaugeSU2BasisSupportLevel : ProofLevel
periodicTreeGaugeSU2BasisSupportLevel = machineChecked

physicalSU2CoordinateTupleToLieFieldInputsLevel : ProofLevel
physicalSU2CoordinateTupleToLieFieldInputsLevel = conditional
