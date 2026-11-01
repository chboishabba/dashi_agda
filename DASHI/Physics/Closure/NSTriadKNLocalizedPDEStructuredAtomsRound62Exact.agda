module DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 62 CONTRIBUTION
--
-- Strengthen the common D/F source.  A localized PDE producer should not emit
-- an undifferentiated list and then independently reconstruct kernel and
-- boundary ledgers.  Emit ONE list of structured atoms:
--
--   * physical interior atom with its existing compatible owner proof,
--   * tail atom,
--   * duplicate kernel atom,
--   * exact cancelling kernel PAIR,
--   * independent kernel atom,
--   * lower/upper boundary atom with its vanishing-reason classification.
--
-- HH ownership is deliberately NOT guessed: a physical HH atom must carry the
-- existing proof selecting HH-good or HH-bad.  Thus this layer preserves the
-- duplicate-free owner semantics of the signed constituent tree exactly.
--
-- A cancellation pair stores l+r=0.  Recursive folding proves the TOTAL
-- cancellation contribution is zero, constructs the mature Round55
-- LiteralKernelResidualSplit, and extracts the boundary-atom list from the
-- same source.  No global cancellation theorem is resupplied.
--
-- What remains genuinely analytic after this file is:
--   (D1/F1) emit this ONE structured list from the literal localized NS identity;
--   (D2) prove the independent kernel total is zero or bound it quantitatively;
--   (F2) prove the classified boundary atom limits vanish.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNSignedConstituentTreeRound28Exact as Signed
import DASHI.Physics.Closure.NSTriadKNBoundaryVanishingClassificationRound29Exact as Boundary
import DASHI.Physics.Closure.NSTriadKNKernelLiteralResidualRound55Exact as Kernel
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEConstituentPartitionRound62Exact as Partition

------------------------------------------------------------------------
-- One source-level atom language.
------------------------------------------------------------------------

data LocalizedPDEAtom : Set where
  physicalAtom :
    (cell : Support.FiveSourceCell) →
    (selected : Tax.TaxOwner) →
    Signed.CompatibleOwner (Signed.physicalSource cell) selected →
    ℚ → LocalizedPDEAtom
  tailAtom : ℚ → LocalizedPDEAtom
  duplicateKernelAtom : ℚ → LocalizedPDEAtom
  cancellingKernelPair :
    (left right : ℚ) → left + right ≡ 0ℚ → LocalizedPDEAtom
  independentKernelAtom : ℚ → LocalizedPDEAtom
  lowerBoundaryAtom : Boundary.BoundaryVanishingReason → ℚ → LocalizedPDEAtom
  upperBoundaryAtom : Boundary.BoundaryVanishingReason → ℚ → LocalizedPDEAtom

kernelConstituent : ℚ → Signed.SignedConstituent
kernelConstituent value =
  Signed.signed-constituent
    Signed.kernelSource Tax.kernel refl value

lowerBoundaryConstituent : ℚ → Signed.SignedConstituent
lowerBoundaryConstituent value =
  Signed.signed-constituent
    (Signed.boundarySource Signed.lowerCut) Tax.boundary refl value

upperBoundaryConstituent : ℚ → Signed.SignedConstituent
upperBoundaryConstituent value =
  Signed.signed-constituent
    (Signed.boundarySource Signed.upperCut) Tax.boundary refl value

flattenAtom : LocalizedPDEAtom → List Signed.SignedConstituent
flattenAtom (physicalAtom cell selected compatible value) =
  Signed.signed-constituent
    (Signed.physicalSource cell) selected compatible value ∷ []
flattenAtom (tailAtom value) =
  Signed.signed-constituent Signed.tailSource Tax.tail refl value ∷ []
flattenAtom (duplicateKernelAtom value) = kernelConstituent value ∷ []
flattenAtom (cancellingKernelPair left right cancellation) =
  kernelConstituent left ∷ kernelConstituent right ∷ []
flattenAtom (independentKernelAtom value) = kernelConstituent value ∷ []
flattenAtom (lowerBoundaryAtom reason value) =
  lowerBoundaryConstituent value ∷ []
flattenAtom (upperBoundaryAtom reason value) =
  upperBoundaryConstituent value ∷ []

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (x ∷ xs) right = x ∷ append xs right

flattenAtoms : List LocalizedPDEAtom → List Signed.SignedConstituent
flattenAtoms [] = []
flattenAtoms (atom ∷ rest) = append (flattenAtom atom) (flattenAtoms rest)

------------------------------------------------------------------------
-- Kernel fold.  Exact cancellation is structural because each cancel pair is
-- one atom carrying l+r=0.
------------------------------------------------------------------------

duplicateKernelTotal : List LocalizedPDEAtom → ℚ
duplicateKernelTotal [] = 0ℚ
duplicateKernelTotal (duplicateKernelAtom value ∷ rest) =
  value + duplicateKernelTotal rest
duplicateKernelTotal (atom ∷ rest) = duplicateKernelTotal rest

cancelLeftTotal : List LocalizedPDEAtom → ℚ
cancelLeftTotal [] = 0ℚ
cancelLeftTotal (cancellingKernelPair left right proof ∷ rest) =
  left + cancelLeftTotal rest
cancelLeftTotal (atom ∷ rest) = cancelLeftTotal rest

cancelRightTotal : List LocalizedPDEAtom → ℚ
cancelRightTotal [] = 0ℚ
cancelRightTotal (cancellingKernelPair left right proof ∷ rest) =
  right + cancelRightTotal rest
cancelRightTotal (atom ∷ rest) = cancelRightTotal rest

independentKernelTotal : List LocalizedPDEAtom → ℚ
independentKernelTotal [] = 0ℚ
independentKernelTotal (independentKernelAtom value ∷ rest) =
  value + independentKernelTotal rest
independentKernelTotal (atom ∷ rest) = independentKernelTotal rest

cancelTotalsExact :
  (atoms : List LocalizedPDEAtom) →
  cancelLeftTotal atoms + cancelRightTotal atoms ≡ 0ℚ
cancelTotalsExact [] = refl
cancelTotalsExact (cancellingKernelPair left right local ∷ rest) =
  trans
    (solve
      ( left ∷ right
      ∷ cancelLeftTotal rest ∷ cancelRightTotal rest ∷ []))
    (trans
      (cong₂ _+_ local (cancelTotalsExact rest))
      (solve []))
cancelTotalsExact (physicalAtom cell selected compatible value ∷ rest) =
  cancelTotalsExact rest
cancelTotalsExact (tailAtom value ∷ rest) = cancelTotalsExact rest
cancelTotalsExact (duplicateKernelAtom value ∷ rest) = cancelTotalsExact rest
cancelTotalsExact (independentKernelAtom value ∷ rest) = cancelTotalsExact rest
cancelTotalsExact (lowerBoundaryAtom reason value ∷ rest) = cancelTotalsExact rest
cancelTotalsExact (upperBoundaryAtom reason value ∷ rest) = cancelTotalsExact rest

kernelResidualSplit :
  List LocalizedPDEAtom → Kernel.LiteralKernelResidualSplit
kernelResidualSplit atoms = record
  { duplicateOwned = duplicateKernelTotal atoms
  ; cancelLeft = cancelLeftTotal atoms
  ; cancelRight = cancelRightTotal atoms
  ; independent = independentKernelTotal atoms
  ; cancellation = cancelTotalsExact atoms
  }

------------------------------------------------------------------------
-- Boundary extraction from the same atom list.
------------------------------------------------------------------------

boundaryAtoms : List LocalizedPDEAtom → List Boundary.BoundaryAtom
boundaryAtoms [] = []
boundaryAtoms (lowerBoundaryAtom reason value ∷ rest) =
  Boundary.boundary-atom value reason ∷ boundaryAtoms rest
boundaryAtoms (upperBoundaryAtom reason value ∷ rest) =
  Boundary.boundary-atom value reason ∷ boundaryAtoms rest
boundaryAtoms (atom ∷ rest) = boundaryAtoms rest

lowerBoundarySignedTotal : List LocalizedPDEAtom → ℚ
lowerBoundarySignedTotal [] = 0ℚ
lowerBoundarySignedTotal (lowerBoundaryAtom reason value ∷ rest) =
  value + lowerBoundarySignedTotal rest
lowerBoundarySignedTotal (atom ∷ rest) = lowerBoundarySignedTotal rest

upperBoundarySignedTotal : List LocalizedPDEAtom → ℚ
upperBoundarySignedTotal [] = 0ℚ
upperBoundarySignedTotal (upperBoundaryAtom reason value ∷ rest) =
  value + upperBoundarySignedTotal rest
upperBoundarySignedTotal (atom ∷ rest) = upperBoundarySignedTotal rest

------------------------------------------------------------------------
-- Same-object agreement with the Round62 raw constituent partition.
------------------------------------------------------------------------

kernelFlattenMeaning :
  (atoms : List LocalizedPDEAtom) →
  Partition.kernelTotal (flattenAtoms atoms)
  ≡ duplicateKernelTotal atoms
    + (cancelLeftTotal atoms + cancelRightTotal atoms)
    + independentKernelTotal atoms
kernelFlattenMeaning [] = solve []
kernelFlattenMeaning (physicalAtom cell selected compatible value ∷ rest) =
  trans
    (cong (0ℚ +_) (kernelFlattenMeaning rest))
    (solve
      ( duplicateKernelTotal rest
      ∷ cancelLeftTotal rest ∷ cancelRightTotal rest
      ∷ independentKernelTotal rest ∷ []))
kernelFlattenMeaning (tailAtom value ∷ rest) =
  trans
    (cong (0ℚ +_) (kernelFlattenMeaning rest))
    (solve
      ( duplicateKernelTotal rest
      ∷ cancelLeftTotal rest ∷ cancelRightTotal rest
      ∷ independentKernelTotal rest ∷ []))
kernelFlattenMeaning (duplicateKernelAtom value ∷ rest) =
  trans
    (cong (value +_) (kernelFlattenMeaning rest))
    (solve
      ( value ∷ duplicateKernelTotal rest
      ∷ cancelLeftTotal rest ∷ cancelRightTotal rest
      ∷ independentKernelTotal rest ∷ []))
kernelFlattenMeaning (cancellingKernelPair left right local ∷ rest) =
  trans
    (cong (left + (right +_)) (kernelFlattenMeaning rest))
    (solve
      ( left ∷ right ∷ duplicateKernelTotal rest
      ∷ cancelLeftTotal rest ∷ cancelRightTotal rest
      ∷ independentKernelTotal rest ∷ []))
kernelFlattenMeaning (independentKernelAtom value ∷ rest) =
  trans
    (cong (value +_) (kernelFlattenMeaning rest))
    (solve
      ( value ∷ duplicateKernelTotal rest
      ∷ cancelLeftTotal rest ∷ cancelRightTotal rest
      ∷ independentKernelTotal rest ∷ []))
kernelFlattenMeaning (lowerBoundaryAtom reason value ∷ rest) =
  trans
    (cong (0ℚ +_) (kernelFlattenMeaning rest))
    (solve
      ( duplicateKernelTotal rest
      ∷ cancelLeftTotal rest ∷ cancelRightTotal rest
      ∷ independentKernelTotal rest ∷ []))
kernelFlattenMeaning (upperBoundaryAtom reason value ∷ rest) =
  trans
    (cong (0ℚ +_) (kernelFlattenMeaning rest))
    (solve
      ( duplicateKernelTotal rest
      ∷ cancelLeftTotal rest ∷ cancelRightTotal rest
      ∷ independentKernelTotal rest ∷ []))

kernelAfterStructuralCancellation :
  (atoms : List LocalizedPDEAtom) →
  Partition.kernelTotal (flattenAtoms atoms)
  ≡ duplicateKernelTotal atoms + independentKernelTotal atoms
kernelAfterStructuralCancellation atoms =
  trans
    (kernelFlattenMeaning atoms)
    (trans
      (cong
        (λ cancelled →
          duplicateKernelTotal atoms + cancelled
            + independentKernelTotal atoms)
        (cancelTotalsExact atoms))
      (solve
        (duplicateKernelTotal atoms ∷ independentKernelTotal atoms ∷ [])))

structuredAtomsDeriveKernelResidualAndBoundaryLedger : Bool
structuredAtomsDeriveKernelResidualAndBoundaryLedger = true

structuredCancellationNeedsNoGlobalPremise : Bool
structuredCancellationNeedsNoGlobalPremise = true

structuredAtomsDeriveKernelResidualAndBoundaryLedgerIsTrue :
  structuredAtomsDeriveKernelResidualAndBoundaryLedger ≡ true
structuredAtomsDeriveKernelResidualAndBoundaryLedgerIsTrue = refl

structuredCancellationNeedsNoGlobalPremiseIsTrue :
  structuredCancellationNeedsNoGlobalPremise ≡ true
structuredCancellationNeedsNoGlobalPremiseIsTrue = refl
