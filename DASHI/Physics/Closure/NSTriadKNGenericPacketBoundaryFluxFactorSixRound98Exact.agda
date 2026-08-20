module DASHI.Physics.Closure.NSTriadKNGenericPacketBoundaryFluxFactorSixRound98Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- ROUND98/99 / GENERIC-CARRIER PACKET-FLUX NORMALIZATION
--
-- Round38/39 and the rational Round98 audit show that the three-leg,
-- ordered-pair packet bookkeeping counts each raw projected incidence six
-- times.  The compact-Gamma lane is generic over `RealField`, whose interface
-- intentionally does not postulate inverse laws, so the source-native theorem
-- is division-free:
--
--   selected three-leg boundary transfer
--       = sixFold (literal selected projected pairing).
--
-- Round99 repairs the first generic draft without adding any algebraic axiom:
-- listwise three-leg splitting is proved recursively, the four/six-term
-- reorders are proved from the existing commutative-ring solver, and the
-- zero-output Hermitian case is proved explicitly.  The rational specialization
-- may then divide by six; the generic theorem does not manufacture 1/6.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Agda.Builtin.Nat using (Nat)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3EnergyCancellation as Energy
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as Round39

selectComplex : ∀ {r} {F : C3.RealField r} → Bool → C3.Complex F → C3.Complex F
selectComplex {F = F} true value = value
selectComplex {F = F} false value = C3.complexZero F

foldComplex : ∀ {r} {F : C3.RealField r} →
  (Physical.PhysicalTriadIncidence → C3.Complex F) →
  List Physical.PhysicalTriadIncidence → C3.Complex F
foldComplex {F = F} value [] = C3.complexZero F
foldComplex value (tau ∷ rest) = C3.complexAdd (value tau) (foldComplex value rest)

foldComplexMap : ∀ {r} {F : C3.RealField r}
  (value : Physical.PhysicalTriadIncidence → C3.Complex F)
  (reindex : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence)
  (items : List Physical.PhysicalTriadIncidence) →
  foldComplex value (map reindex items)
  ≡ foldComplex (λ tau → value (reindex tau)) items
foldComplexMap value reindex [] = refl
foldComplexMap value reindex (tau ∷ rest) =
  cong (C3.complexAdd (value (reindex tau))) (foldComplexMap value reindex rest)

swapAdd : ∀ {r} {F : C3.RealField r} (a b tail : C3.Complex F) →
  C3.complexAdd a (C3.complexAdd b tail)
  ≡ C3.complexAdd b (C3.complexAdd a tail)
swapAdd a b tail =
  trans
    (sym (Algebra.complexAddAssociative a b tail))
    (trans
      (cong (λ head → C3.complexAdd head tail)
        (Algebra.complexAddCommutative a b))
      (Algebra.complexAddAssociative b a tail))

foldComplexPermutationInvariant : ∀ {r} {F : C3.RealField r}
  (value : Physical.PhysicalTriadIncidence → C3.Complex F) →
  ∀ {left right} → left Perm.↭ right →
  foldComplex value left ≡ foldComplex value right
foldComplexPermutationInvariant value Perm.refl = refl
foldComplexPermutationInvariant value (Perm.prep x permutation) =
  cong (C3.complexAdd (value x)) (foldComplexPermutationInvariant value permutation)
foldComplexPermutationInvariant value (Perm.swap {ys = ys} x y permutation) =
  trans
    (cong
      (λ tail → C3.complexAdd (value x) (C3.complexAdd (value y) tail))
      (foldComplexPermutationInvariant value permutation))
    (swapAdd (value x) (value y) (foldComplex value ys))
foldComplexPermutationInvariant value (Perm.trans first second) =
  trans (foldComplexPermutationInvariant value first)
        (foldComplexPermutationInvariant value second)

complexInterchange : ∀ {r} {F : C3.RealField r}
  (a b c d : C3.Complex F) →
  C3.complexAdd (C3.complexAdd a b) (C3.complexAdd c d)
  ≡ C3.complexAdd (C3.complexAdd a c) (C3.complexAdd b d)
complexInterchange a b c d =
  trans
    (Algebra.complexAddAssociative a b (C3.complexAdd c d))
    (trans
      (cong (C3.complexAdd a) (sym (Algebra.complexAddAssociative b c d)))
      (trans
        (cong (C3.complexAdd a)
          (cong (λ middle → C3.complexAdd middle d)
            (Algebra.complexAddCommutative b c)))
        (trans
          (cong (C3.complexAdd a) (Algebra.complexAddAssociative c b d))
          (sym (Algebra.complexAddAssociative a c (C3.complexAdd b d))))))

complexPacketReorder : ∀ {r} {F : C3.RealField r}
  (a b c ar br cr : C3.Complex F) →
  C3.complexAdd
    (C3.complexAdd (C3.complexAdd a b) c)
    (C3.complexAdd (C3.complexAdd ar br) cr)
  ≡ C3.complexAdd
      (C3.complexAdd (C3.complexAdd a ar) (C3.complexAdd b br))
      (C3.complexAdd c cr)
complexPacketReorder {F = F}
    (C3.complex a ai) (C3.complex b bi) (C3.complex c ci)
    (C3.complex ar ari) (C3.complex br bri) (C3.complex cr cri) =
  Algebra.complexExt
    (P.R.solve 6
      (λ a b c ar br cr →
        (((a P.R.⊕ b) P.R.⊕ c) P.R.⊕ ((ar P.R.⊕ br) P.R.⊕ cr))
        P.R.⊜ (((a P.R.⊕ ar) P.R.⊕ (b P.R.⊕ br)) P.R.⊕ (c P.R.⊕ cr)))
      refl a b c ar br cr)
    (P.R.solve 6
      (λ a b c ar br cr →
        (((a P.R.⊕ b) P.R.⊕ c) P.R.⊕ ((ar P.R.⊕ br) P.R.⊕ cr))
        P.R.⊜ (((a P.R.⊕ ar) P.R.⊕ (b P.R.⊕ br)) P.R.⊕ (c P.R.⊕ cr)))
      refl ai bi ci ari bri cri)
  where module P = Algebra.Polynomial F

sixFold : ∀ {r} {F : C3.RealField r} → C3.Complex F → C3.Complex F
sixFold value =
  C3.complexAdd
    (C3.complexAdd
      (C3.complexAdd value value)
      (C3.complexAdd value value))
    (C3.complexAdd value value)

orderedPower : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) → C3.ModeInverseSquare F E →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) → C3.Complex F
orderedPower E I tau velocity = Audit.orderedSignedTransferAt E I tau velocity

orderedPairPower : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) → C3.ModeInverseSquare F E →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) → C3.Complex F
orderedPairPower E I tau velocity = Audit.orderedPairSignedTransferAt E I tau velocity

selectedOrderedPower : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) → (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) → (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex F
selectedOrderedPower E I selected velocity tau =
  selectComplex (selected (Physical.k tau)) (orderedPower E I tau velocity)

selectedPairPower : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) → (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) → (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex F
selectedPairPower E I selected velocity tau =
  selectComplex (selected (Physical.k tau)) (orderedPairPower E I tau velocity)

selectedOrderedFold selectedPairFold : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) → (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) → (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → C3.Complex F
selectedOrderedFold E I selected velocity = foldComplex (selectedOrderedPower E I selected velocity)
selectedPairFold E I selected velocity = foldComplex (selectedPairPower E I selected velocity)

selectAdd : ∀ {r} {F : C3.RealField r} b (x y : C3.Complex F) →
  selectComplex b (C3.complexAdd x y)
  ≡ C3.complexAdd (selectComplex b x) (selectComplex b y)
selectAdd true x y = refl
selectAdd {F = F} false x y = sym (Algebra.complexAddZeroLeft (C3.complexZero F))

selectedPairPointwise : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F)
  (tau : Physical.PhysicalTriadIncidence) →
  selectedPairPower E I selected velocity tau
  ≡ C3.complexAdd
      (selectedOrderedPower E I selected velocity tau)
      (selectedOrderedPower E I selected velocity (Symmetry.swapTriad tau))
selectedPairPointwise E I selected velocity tau =
  trans
    (cong (selectComplex (selected (Physical.k tau)))
      (Energy.orderedPairCoefficientIsOrderedSum E I tau velocity))
    (selectAdd (selected (Physical.k tau))
      (orderedPower E I tau velocity)
      (orderedPower E I (Symmetry.swapTriad tau) velocity))

selectedPairFoldSplit : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F)
  (items : List Physical.PhysicalTriadIncidence) →
  selectedPairFold E I selected velocity items
  ≡ C3.complexAdd
      (selectedOrderedFold E I selected velocity items)
      (foldComplex
        (λ tau → selectedOrderedPower E I selected velocity (Symmetry.swapTriad tau)) items)
selectedPairFoldSplit {F = F} E I selected velocity [] =
  sym (Algebra.complexAddZeroLeft (C3.complexZero F))
selectedPairFoldSplit E I selected velocity (tau ∷ rest) =
  trans
    (cong (C3.complexAdd (selectedPairPower E I selected velocity tau))
      (selectedPairFoldSplit E I selected velocity rest))
    (trans
      (cong
        (λ head → C3.complexAdd head
          (C3.complexAdd
            (selectedOrderedFold E I selected velocity rest)
            (foldComplex
              (λ t → selectedOrderedPower E I selected velocity (Symmetry.swapTriad t)) rest)))
        (selectedPairPointwise E I selected velocity tau))
      (complexInterchange
        (selectedOrderedPower E I selected velocity tau)
        (selectedOrderedPower E I selected velocity (Symmetry.swapTriad tau))
        (selectedOrderedFold E I selected velocity rest)
        (foldComplex
          (λ t → selectedOrderedPower E I selected velocity (Symmetry.swapTriad t)) rest)))

selectedPairFoldIsDoubleOrdered : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F) (cutoff : Nat) →
  selectedPairFold E I selected velocity (Physical.physicalTriadEnumeration cutoff)
  ≡ C3.complexAdd
      (selectedOrderedFold E I selected velocity (Physical.physicalTriadEnumeration cutoff))
      (selectedOrderedFold E I selected velocity (Physical.physicalTriadEnumeration cutoff))
selectedPairFoldIsDoubleOrdered E I selected velocity cutoff =
  trans
    (selectedPairFoldSplit E I selected velocity (Physical.physicalTriadEnumeration cutoff))
    (cong
      (C3.complexAdd
        (selectedOrderedFold E I selected velocity (Physical.physicalTriadEnumeration cutoff)))
      (trans
        (sym (foldComplexMap
          (selectedOrderedPower E I selected velocity)
          Symmetry.swapTriad (Physical.physicalTriadEnumeration cutoff)))
        (foldComplexPermutationInvariant
          (selectedOrderedPower E I selected velocity)
          (Round38.swapTriadEnumerationPermutation cutoff))))

pSelectedPairFold qSelectedPairFold : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) → (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → C3.Complex F
pSelectedPairFold E I selected velocity =
  foldComplex (λ tau → selectComplex (selected (Physical.p tau))
    (orderedPairPower E I (Orbit.pEnergyLeg tau) velocity))
qSelectedPairFold E I selected velocity =
  foldComplex (λ tau → selectComplex (selected (Physical.q tau))
    (orderedPairPower E I (Orbit.qEnergyLeg tau) velocity))

pSelectedPairInvariant : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F) (cutoff : Nat) →
  pSelectedPairFold E I selected velocity (Physical.physicalTriadEnumeration cutoff)
  ≡ selectedPairFold E I selected velocity (Physical.physicalTriadEnumeration cutoff)
pSelectedPairInvariant E I selected velocity cutoff =
  trans
    (sym (foldComplexMap (selectedPairPower E I selected velocity)
      Orbit.pEnergyLeg (Physical.physicalTriadEnumeration cutoff)))
    (foldComplexPermutationInvariant (selectedPairPower E I selected velocity)
      (Round38.pEnergyLegEnumerationPermutation cutoff))

qSelectedPairInvariant : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F) (cutoff : Nat) →
  qSelectedPairFold E I selected velocity (Physical.physicalTriadEnumeration cutoff)
  ≡ selectedPairFold E I selected velocity (Physical.physicalTriadEnumeration cutoff)
qSelectedPairInvariant E I selected velocity cutoff =
  trans
    (sym (foldComplexMap (selectedPairPower E I selected velocity)
      Orbit.qEnergyLeg (Physical.physicalTriadEnumeration cutoff)))
    (foldComplexPermutationInvariant (selectedPairPower E I selected velocity)
      (Round38.qEnergyLegEnumerationPermutation cutoff))

packetTriadTransfer : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) → (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex F
packetTriadTransfer E I selected velocity tau =
  C3.complexAdd
    (C3.complexAdd
      (selectComplex (selected (Physical.k tau)) (orderedPairPower E I tau velocity))
      (selectComplex (selected (Physical.p tau))
        (orderedPairPower E I (Orbit.pEnergyLeg tau) velocity)))
    (selectComplex (selected (Physical.q tau))
      (orderedPairPower E I (Orbit.qEnergyLeg tau) velocity))

boundaryTriadTransfer : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) → (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex F
boundaryTriadTransfer {F = F} E I selected velocity tau
  with selected (Physical.k tau) | selected (Physical.p tau) | selected (Physical.q tau)
... | true  | true  | true  = C3.complexZero F
... | false | false | false = C3.complexZero F
... | sk | sp | sq = packetTriadTransfer E I selected velocity tau

allSelectedPacketTransferZero : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity → Audit.DivergenceFreeCondition E velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  selected (Physical.k tau) ≡ true → selected (Physical.p tau) ≡ true →
  selected (Physical.q tau) ≡ true →
  packetTriadTransfer E I selected velocity tau ≡ C3.complexZero F
allSelectedPacketTransferZero E I selected velocity reality divergenceFree tau
    kIn pIn qIn rewrite kIn | pIn | qIn =
  Audit.completeTriadCancellation
    (Energy.exactTriadEnergyCancellation E I tau)
    velocity reality divergenceFree

packetTransferIsBoundaryPointwise : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity → Audit.DivergenceFreeCondition E velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  packetTriadTransfer E I selected velocity tau
  ≡ boundaryTriadTransfer E I selected velocity tau
packetTransferIsBoundaryPointwise E I selected velocity reality divergenceFree tau
  with selected (Physical.k tau) | selected (Physical.p tau) | selected (Physical.q tau)
... | true | true | true =
  allSelectedPacketTransferZero E I selected velocity reality divergenceFree tau refl refl refl
... | false | false | false =
  trans (Algebra.complexAddZeroLeft (C3.complexZero _))
        (Algebra.complexAddZeroLeft (C3.complexZero _))
... | true | true | false = refl
... | true | false | true = refl
... | false | true | true = refl
... | true | false | false = refl
... | false | true | false = refl
... | false | false | true = refl

sumPacketTransfer sumBoundaryTransfer : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) → (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → C3.Complex F
sumPacketTransfer E I selected velocity = foldComplex (packetTriadTransfer E I selected velocity)
sumBoundaryTransfer E I selected velocity = foldComplex (boundaryTriadTransfer E I selected velocity)

finitePacketTransferIsBoundaryFlux : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity → Audit.DivergenceFreeCondition E velocity →
  (items : List Physical.PhysicalTriadIncidence) →
  sumPacketTransfer E I selected velocity items
  ≡ sumBoundaryTransfer E I selected velocity items
finitePacketTransferIsBoundaryFlux E I selected velocity reality divergenceFree [] = refl
finitePacketTransferIsBoundaryFlux E I selected velocity reality divergenceFree (tau ∷ rest) =
  cong₂ C3.complexAdd
    (packetTransferIsBoundaryPointwise E I selected velocity reality divergenceFree tau)
    (finitePacketTransferIsBoundaryFlux E I selected velocity reality divergenceFree rest)

packetTransferSplit : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F)
  (items : List Physical.PhysicalTriadIncidence) →
  sumPacketTransfer E I selected velocity items
  ≡ C3.complexAdd
      (C3.complexAdd
        (selectedPairFold E I selected velocity items)
        (pSelectedPairFold E I selected velocity items))
      (qSelectedPairFold E I selected velocity items)
packetTransferSplit {F = F} E I selected velocity [] =
  sym
    (trans
      (cong (λ first → C3.complexAdd first (C3.complexZero F))
        (Algebra.complexAddZeroLeft (C3.complexZero F)))
      (Algebra.complexAddZeroLeft (C3.complexZero F)))
packetTransferSplit E I selected velocity (tau ∷ rest) =
  let
    a = selectedPairPower E I selected velocity tau
    b = selectComplex (selected (Physical.p tau))
      (orderedPairPower E I (Orbit.pEnergyLeg tau) velocity)
    c = selectComplex (selected (Physical.q tau))
      (orderedPairPower E I (Orbit.qEnergyLeg tau) velocity)
    ar = selectedPairFold E I selected velocity rest
    br = pSelectedPairFold E I selected velocity rest
    cr = qSelectedPairFold E I selected velocity rest
  in
  trans
    (cong (C3.complexAdd (packetTriadTransfer E I selected velocity tau))
      (packetTransferSplit E I selected velocity rest))
    (complexPacketReorder a b c ar br cr)

packetTransferIsSixSelectedOrdered : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (selected : Z3.FourierMode → Bool)
  (velocity : Z3.FourierMode → C3.Complex3 F) (cutoff : Nat) →
  sumPacketTransfer E I selected velocity (Physical.physicalTriadEnumeration cutoff)
  ≡ sixFold
      (selectedOrderedFold E I selected velocity (Physical.physicalTriadEnumeration cutoff))
packetTransferIsSixSelectedOrdered E I selected velocity cutoff =
  let
    enumeration = Physical.physicalTriadEnumeration cutoff
    pairTotal = selectedPairFold E I selected velocity enumeration
    pTotal = pSelectedPairFold E I selected velocity enumeration
    qTotal = qSelectedPairFold E I selected velocity enumeration
    pInv = pSelectedPairInvariant E I selected velocity cutoff
    qInv = qSelectedPairInvariant E I selected velocity cutoff
    pairDouble = selectedPairFoldIsDoubleOrdered E I selected velocity cutoff
  in
  trans
    (packetTransferSplit E I selected velocity enumeration)
    (trans
      (cong₂ C3.complexAdd
        (cong (C3.complexAdd pairTotal) pInv) qInv)
      (cong₂ C3.complexAdd
        (cong₂ C3.complexAdd pairDouble pairDouble) pairDouble))

------------------------------------------------------------------------
-- Generic actual projected pairing, output by output.
------------------------------------------------------------------------

hermitianZeroRight : ∀ {r} {F : C3.RealField r} (test : C3.Complex3 F) →
  C3.hermitianPairing3 test (C3.complex3Zero F) ≡ C3.complexZero F
hermitianZeroRight {F = F} (C3.complex3 tx ty tz) =
  trans
    (cong
      (λ first → C3.complexAdd first
        (C3.complexMultiply (C3.complexConjugate tz) (C3.complexZero F)))
      (cong₂ C3.complexAdd
        (Algebra.complexMultiplyZeroRight (C3.complexConjugate tx))
        (Algebra.complexMultiplyZeroRight (C3.complexConjugate ty))))
    (trans
      (cong
        (λ last → C3.complexAdd
          (C3.complexAdd (C3.complexZero F) (C3.complexZero F)) last)
        (Algebra.complexMultiplyZeroRight (C3.complexConjugate tz)))
      (trans
        (cong (λ first → C3.complexAdd first (C3.complexZero F))
          (Algebra.complexAddZeroLeft (C3.complexZero F)))
        (Algebra.complexAddZeroRight (C3.complexZero F))))

projectedPower : ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex F
projectedPower test value = C3.complexRealPart (C3.hermitianPairing3 test value)

projectedPowerZeroRight : ∀ {r} {F : C3.RealField r} (test : C3.Complex3 F) →
  projectedPower test (C3.complex3Zero F) ≡ C3.complexZero F
projectedPowerZeroRight test = cong C3.complexRealPart (hermitianZeroRight test)

projectedPowerAddRight : ∀ {r} {F : C3.RealField r}
  (test left right : C3.Complex3 F) →
  projectedPower test (C3.complex3Add left right)
  ≡ C3.complexAdd (projectedPower test left) (projectedPower test right)
projectedPowerAddRight test left right =
  trans
    (cong C3.complexRealPart (Algebra.hermitianAddRight test left right))
    (Algebra.complexRealPartAdd
      (C3.hermitianPairing3 test left) (C3.hermitianPairing3 test right))

sumOutputTermPowers : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I → Z3.FourierMode →
  List Physical.PhysicalTriadIncidence → C3.Complex F
sumOutputTermPowers {F = F} system output [] = C3.complexZero F
sumOutputTermPowers system output (tau ∷ rest) =
  C3.complexAdd
    (projectedPower (Equation.velocity system output)
      (Equation.projectedOrderedTerm system tau))
    (sumOutputTermPowers system output rest)

pairingWithVectorSum : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (output : Z3.FourierMode) → (items : List Physical.PhysicalTriadIncidence) →
  projectedPower (Equation.velocity system output)
    (Equation.sumVectors (Equation.mapTriadTerms system items))
  ≡ sumOutputTermPowers system output items
pairingWithVectorSum system output [] = projectedPowerZeroRight (Equation.velocity system output)
pairingWithVectorSum system output (tau ∷ rest) =
  trans
    (projectedPowerAddRight
      (Equation.velocity system output)
      (Equation.projectedOrderedTerm system tau)
      (Equation.sumVectors (Equation.mapTriadTerms system rest)))
    (cong
      (C3.complexAdd
        (projectedPower (Equation.velocity system output)
          (Equation.projectedOrderedTerm system tau)))
      (pairingWithVectorSum system output rest))

outputFiberPowerIsOrdered : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
  (system : Equation.FiniteComplex3GalerkinSystem F E I)
  (output : Z3.FourierMode) (tau : Physical.PhysicalTriadIncidence) →
  Cube._∈_ tau (Equation.concreteTriadsAt system output) →
  projectedPower (Equation.velocity system output)
    (Equation.projectedOrderedTerm system tau)
  ≡ orderedPower E I tau (Equation.velocity system)
outputFiberPowerIsOrdered system output tau member =
  subst
    (λ selectedOutput →
      projectedPower (Equation.velocity system selectedOutput)
        (Equation.projectedOrderedTerm system tau)
      ≡ orderedPower _ _ tau (Equation.velocity system))
    (Equation.concreteTriadsAtOutputAgreement member)
    refl

sumOutputFiberIsOrderedFold : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
  (system : Equation.FiniteComplex3GalerkinSystem F E I)
  (output : Z3.FourierMode) →
  sumOutputTermPowers system output (Equation.concreteTriadsAt system output)
  ≡ foldComplex (λ tau → orderedPower E I tau (Equation.velocity system))
      (Equation.concreteTriadsAt system output)
sumOutputFiberIsOrderedFold {E = E} {I = I} system output =
  go (Equation.concreteTriadsAt system output)
    (λ tau member → outputFiberPowerIsOrdered system output tau member)
  where
  go : (items : List Physical.PhysicalTriadIncidence) →
    (∀ tau → Cube._∈_ tau items →
      projectedPower (Equation.velocity system output)
        (Equation.projectedOrderedTerm system tau)
      ≡ orderedPower E I tau (Equation.velocity system)) →
    sumOutputTermPowers system output items
    ≡ foldComplex (λ tau → orderedPower E I tau (Equation.velocity system)) items
  go [] pointwise = refl
  go (tau ∷ rest) pointwise =
    cong₂ C3.complexAdd
      (pointwise tau (Cube.here refl))
      (go rest (λ chosen member → pointwise chosen (Cube.there member)))

projectedOutputPowerIsOrderedFiber : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
  (system : Equation.FiniteComplex3GalerkinSystem F E I)
  (output : Z3.FourierMode) →
  projectedPower (Equation.velocity system output)
    (Equation.projectedNonlinearity system output)
  ≡ foldComplex (λ tau → orderedPower E I tau (Equation.velocity system))
      (Equation.concreteTriadsAt system output)
projectedOutputPowerIsOrderedFiber system output =
  trans (pairingWithVectorSum system output (Equation.concreteTriadsAt system output))
        (sumOutputFiberIsOrderedFold system output)

selectedProjectedOutputPower : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) → Z3.FourierMode → C3.Complex F
selectedProjectedOutputPower system selected output =
  selectComplex (selected output)
    (projectedPower (Equation.velocity system output)
      (Equation.projectedNonlinearity system output))

sumSelectedProjectedPowers : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) → List Z3.FourierMode → C3.Complex F
sumSelectedProjectedPowers {F = F} system selected [] = C3.complexZero F
sumSelectedProjectedPowers system selected (output ∷ rest) =
  C3.complexAdd (selectedProjectedOutputPower system selected output)
    (sumSelectedProjectedPowers system selected rest)

literalSelectedProjectedPairing : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) → C3.Complex F
literalSelectedProjectedPairing system selected =
  sumSelectedProjectedPowers system selected (Cube.cutoffModes (Equation.cutoff system))

selectedFiberPowerIsSelectedOrderedFold : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
  (system : Equation.FiniteComplex3GalerkinSystem F E I)
  (selected : Z3.FourierMode → Bool) (output : Z3.FourierMode) →
  selectedProjectedOutputPower system selected output
  ≡ selectedOrderedFold E I selected (Equation.velocity system)
      (Equation.concreteTriadsAt system output)
selectedFiberPowerIsSelectedOrderedFold {F = F} {E = E} {I = I} system selected output
  with selected output
... | true =
  trans (projectedOutputPowerIsOrderedFiber system output)
    (sym (goTrue (Equation.concreteTriadsAt system output)
      (λ tau member → Equation.concreteTriadsAtOutputAgreement member)))
  where
  goTrue : (items : List Physical.PhysicalTriadIncidence) →
    (∀ tau → Cube._∈_ tau items → Physical.k tau ≡ output) →
    selectedOrderedFold E I selected (Equation.velocity system) items
    ≡ foldComplex (λ tau → orderedPower E I tau (Equation.velocity system)) items
  goTrue [] pointwise = refl
  goTrue (tau ∷ rest) pointwise
    rewrite pointwise tau (Cube.here refl) =
    cong (C3.complexAdd (orderedPower E I tau (Equation.velocity system)))
      (goTrue rest (λ chosen member → pointwise chosen (Cube.there member)))
... | false =
  sym (goFalse (Equation.concreteTriadsAt system output)
    (λ tau member → Equation.concreteTriadsAtOutputAgreement member))
  where
  goFalse : (items : List Physical.PhysicalTriadIncidence) →
    (∀ tau → Cube._∈_ tau items → Physical.k tau ≡ output) →
    selectedOrderedFold E I selected (Equation.velocity system) items
    ≡ C3.complexZero F
  goFalse [] pointwise = refl
  goFalse (tau ∷ rest) pointwise
    rewrite pointwise tau (Cube.here refl) =
    trans
      (Algebra.complexAddZeroLeft
        (selectedOrderedFold E I selected (Equation.velocity system) rest))
      (goFalse rest (λ chosen member → pointwise chosen (Cube.there member)))

foldComplexAppend : ∀ {r} {F : C3.RealField r}
  (value : Physical.PhysicalTriadIncidence → C3.Complex F) → ∀ left right →
  foldComplex value (Cube._++_ left right)
  ≡ C3.complexAdd (foldComplex value left) (foldComplex value right)
foldComplexAppend {F = F} value [] right =
  sym (Algebra.complexAddZeroLeft (foldComplex value right))
foldComplexAppend value (tau ∷ rest) right =
  trans
    (cong (C3.complexAdd (value tau)) (foldComplexAppend value rest right))
    (sym (Algebra.complexAddAssociative
      (value tau) (foldComplex value rest) (foldComplex value right)))

sumSelectedEqualsConcatFiberFold : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
  (system : Equation.FiniteComplex3GalerkinSystem F E I)
  (selected : Z3.FourierMode → Bool) (outputs : List Z3.FourierMode) →
  sumSelectedProjectedPowers system selected outputs
  ≡ selectedOrderedFold E I selected (Equation.velocity system)
      (Round39.concatOutputFibers (Equation.cutoff system) outputs)
sumSelectedEqualsConcatFiberFold system selected [] = refl
sumSelectedEqualsConcatFiberFold {E = E} {I = I} system selected (output ∷ rest) =
  trans
    (cong₂ C3.complexAdd
      (selectedFiberPowerIsSelectedOrderedFold system selected output)
      (sumSelectedEqualsConcatFiberFold system selected rest))
    (sym (foldComplexAppend
      (selectedOrderedPower E I selected (Equation.velocity system))
      (Equation.concreteTriadsAt system output)
      (Round39.concatOutputFibers (Equation.cutoff system) rest)))

literalSelectedProjectedPairingIsSelectedOrderedFold : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
  (system : Equation.FiniteComplex3GalerkinSystem F E I)
  (selected : Z3.FourierMode → Bool) →
  literalSelectedProjectedPairing system selected
  ≡ selectedOrderedFold E I selected (Equation.velocity system)
      (Physical.physicalTriadEnumeration (Equation.cutoff system))
literalSelectedProjectedPairingIsSelectedOrderedFold {E = E} {I = I} system selected =
  trans
    (sumSelectedEqualsConcatFiberFold system selected
      (Cube.cutoffModes (Equation.cutoff system)))
    (foldComplexPermutationInvariant
      (selectedOrderedPower E I selected (Equation.velocity system))
      (Round39.literalOutputPartitionPermutation (Equation.cutoff system)))

PhysicalPacketBoundaryFluxFactorSixIdentification : ∀ {r} {F : C3.RealField r}
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
  (system : Equation.FiniteComplex3GalerkinSystem F E I)
  (selected : Z3.FourierMode → Bool) →
  Audit.RealityCondition (Equation.velocity system) →
  Audit.DivergenceFreeCondition E (Equation.velocity system) →
  sumBoundaryTransfer E I selected (Equation.velocity system)
    (Physical.physicalTriadEnumeration (Equation.cutoff system))
  ≡ sixFold (literalSelectedProjectedPairing system selected)
PhysicalPacketBoundaryFluxFactorSixIdentification {E = E} {I = I}
    system selected reality divergenceFree =
  trans
    (sym (finitePacketTransferIsBoundaryFlux E I selected
      (Equation.velocity system) reality divergenceFree
      (Physical.physicalTriadEnumeration (Equation.cutoff system))))
    (trans
      (packetTransferIsSixSelectedOrdered E I selected
        (Equation.velocity system) (Equation.cutoff system))
      (cong sixFold
        (sym (literalSelectedProjectedPairingIsSelectedOrderedFold system selected))))

round98GenericRealFieldPacketBoundaryFactorSixClosed : Bool
round98GenericRealFieldPacketBoundaryFactorSixClosed = true

round98GenericRealFieldNeedsInverseSixAxiom : Bool
round98GenericRealFieldNeedsInverseSixAxiom = false

round99GenericFactorSixListSplitRepaired : Bool
round99GenericFactorSixListSplitRepaired = true
