module DASHI.Moonshine.MarkedOldspaceGeometricOggFrontierEverything where

------------------------------------------------------------------------
-- Focused frontier root after the p11/p37/p43 marked-Hecke tranches.
--
-- OLDSPACE / LOCAL-REALIZATION SIDE
--   one common Old3 coordinate module realizes both:
--     * the formal analytic d=1,2,4 Gamma_0(4)-degeneracy span;
--     * the source-native marked principal-level-2 permutation span.
--   The entire analytic span inherits every good-prime level-11 eigencharacter.
--
--   IMPORTANT CORRECTION:
--   common coordinates + common good-prime Hecke character do NOT identify the
--   two local fixed-vector realizations.  The marked side carries a genuine
--   GL_2(F_2)=S3 deck action; the classical degeneracy model is a different
--   local level realization.  P11Level44TwoAdicFixedVectorSeparationExact
--   constructs the finite P^1(F_2) action explicitly and proves the marked
--   deck action is exactly that permutation module, while shared Old3
--   coordinates do not identify the local roles.
--
--   P11Level44HeckeAlignmentNonUniquenessExact strengthens the correction:
--   on this multiplicity space every good-prime T_ell acts by one scalar
--   a_ell, so every scalar-compatible Old3 map is automatically an intertwiner.
--   Identity and the nontrivial three-cycle are two explicit distinct maps
--   intertwining EVERY scalar Hecke action.  Thus no further away-from-2 Hecke
--   probes can canonicalize the local comparison.
--
--   AuxiliaryLevelHeckeEquivariantQuotientNoGoExact weakens an earlier product
--   assumption: all-prime Hecke blindness on a fine fibre requires only a
--   source-native equivariant quotient q T_marked = T_global q plus a
--   nontrivial q-fibre.  A literal Global x Deck product is sufficient but not
--   necessary.  This narrows future same-object work to the commuting quotient
--   square actually consumed by the observer theorem.
--
--   Remaining seam: construct the actual 2-adic local comparison inside the
--   same global automorphic representation (equivalently, the source-native
--   Eichler/Jacquet--Langlands fixed-vector comparison), rather than declaring
--   the K(2)-fixed and K_0(4)-fixed models definitionally equal.
--
-- OGG SELECTOR SIDE
--   The finite quotient geometry has now advanced beyond a count interface.
--   From any ACTUAL supersingular Frobenius normal-form realization we derive:
--
--     * one quotient-node coordinate per nonfixed Frobenius pair;
--     * four oriented Deligne--Rapoport local branches over a quadratic pair;
--     * exactly two Fricke branch-orbits over one quotient-node coordinate;
--     * one rational dual-graph vertex and one loop edge per pair;
--     * arithmetic genus = Frobenius pair count.
--
--   The global selector therefore requires only TWO source-facing equalities:
--
--     actual Fricke special fibre
--       = derived Frobenius-pair nodal model,
--
--     generic Fricke genus
--       = arithmetic genus of that proper-flat special fibre.
--
--   Once supplied, pair defect = g(X0+(p)) follows.  The older table-free
--   pointwise-fixed selector is recovered automatically, and its former
--   independent pairCountSameObject premise disappears because both counts now
--   descend from the SAME finite involution normal form.
--
--   Remaining seam: construct the actual Deligne--Rapoport modular scheme /
--   Fricke quotient same-object theorem and proper-flat genus transport for
--   arbitrary p.  The finite Fricke/class-number Ogg table is not used by this
--   geometric proof interface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)
open import Data.Fin using (Fin)

import DASHI.Moonshine.FormalQSeriesOldformEigencharacterTransportExact as Eig
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Marked
import DASHI.Moonshine.P11MarkedLevel44PermutationOldspaceExact as Perm
import DASHI.Moonshine.P11Level44FormalSameCoordinateComparisonExact as Same
import DASHI.Moonshine.P11Level44SameCoordinateHighestAlphaRegression as SameReg
import DASHI.Moonshine.P11Level44TwoAdicFixedVectorSeparationExact as Local2
import DASHI.Moonshine.P11Level44HeckeAlignmentNonUniquenessExact as AlignNoGo
import DASHI.Moonshine.AuxiliaryLevelHeckeEquivariantQuotientNoGoExact as QuotientNoGo
import DASHI.Moonshine.SupersingularFrobeniusFrickeGenusReductionExact as CountReduce
import DASHI.Moonshine.SupersingularFrobeniusFrickeGenusReductionRegression as CountReg
import DASHI.Moonshine.RationalNodalSpecialFibreGenusExact as Nodal
import DASHI.Moonshine.SupersingularFrickeSpecialFibreSelectorExact as Geometric
import DASHI.Moonshine.FrickeSpecialFibreFrobeniusFixedSelectorExact as FixedSelector
import DASHI.Foundations.FiniteInvolutionPairedOrbitQuotientExact as PairQuot
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DRComb
import DASHI.Moonshine.DeligneRapoportFrickeLocalNodeExact as DRLocal
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as DRSelector
import DASHI.Moonshine.DeligneRapoportFrickeCombinatoricsRegression as DRReg

wholeOldspaceRegression :
  {D : Same.Level44DegeneracyTriple} {ell : Nat} →
  (H : Same.Level44GoodPrimeEigenData D ell) →
  (v : Marked.Old3) →
  (n : Nat) →
  Same.analyticHeckeRealize H v n
  ≡ Eig.scaleSeries (Same.eigenvalue H) (Same.analyticRealize D v) n
wholeOldspaceRegression = Same.wholeOldspaceGoodPrimeEigen

localP1RotationRegression :
  (x : Local2.P1F2) →
  Marked.realizeOld3 (Local2.p1Basis (Local2.rotateP1 x))
  ≡ Perm.deckR5 (Marked.realizeOld3 (Local2.p1Basis x))
localP1RotationRegression = Local2.markedDeckRotationFromP1

localRoleNoCollapseRegression :
  (v : Marked.Old3) →
  Local2.markedLocalPresentation v
  ≡ Local2.analyticDegeneracyPresentation v → Local2.Impossible
localRoleNoCollapseRegression = Local2.sameCoordinatesDoNotIdentifyLocalRealization

allScalarHeckeAlignmentCollisionRegression :
  AlignNoGo.HeckeAlignmentCollision
allScalarHeckeAlignmentCollisionRegression =
  AlignNoGo.allGoodPrimeHeckeAlignmentCollision

rotationIntertwinesArbitraryScalarHeckeRegression :
  (lambda : ℤ) → (v : Marked.Old3) →
  AlignNoGo.mapOld3 AlignNoGo.rotationOld3Map
    (AlignNoGo.scalarHecke lambda v)
  ≡ AlignNoGo.scalarHecke lambda
      (AlignNoGo.mapOld3 AlignNoGo.rotationOld3Map v)
rotationIntertwinesArbitraryScalarHeckeRegression =
  AlignNoGo.rotationHeckeIntertwiner

equivariantQuotientNotProductRequiredRegression :
  QuotientNoGo.productFactorizationRequiredForBlindness
    QuotientNoGo.canonicalEquivariantQuotientNoGoBoundary ≡ false
equivariantQuotientNotProductRequiredRegression = refl

equivariantQuotientAllPrimeBlindnessRegression :
  QuotientNoGo.equivariantQuotientSufficientForAllPrimeBlindness
    QuotientNoGo.canonicalEquivariantQuotientNoGoBoundary ≡ true
equivariantQuotientAllPrimeBlindnessRegression = refl

countReductionRegression :
  (D : CountReduce.SupersingularFrickeCountData) →
  CountReduce.frobeniusPairDefect D ≡ CountReduce.genusX0Plus D
countReductionRegression = CountReduce.frobeniusPairDefectEqualsFrickeGenus

nodalGenusRegression :
  (D : Nodal.NodalDualGraphGenusData) →
  Nodal.arithmeticGenus D ≡ Nodal.nodeCount D
nodalGenusRegression = Nodal.arithmeticGenusEqualsNodeCount

geometricSelectorRegression :
  (R : Geometric.PrimeFrickeSpecialFibreRealization) →
  Geometric.genericFrickeGenus R ≡ Geometric.frobeniusPairDefect R
geometricSelectorRegression = Geometric.frickeGenusEqualsFrobeniusPairDefect

geometricFixedIffGenusZeroRegression :
  (G : FixedSelector.PrimeFrickeFrobeniusGeometry) →
  FixedSelector.GeometricallyFullyFixed G
  ↔ Geometric.genericFrickeGenus
      (FixedSelector.specialFibreRealization G) ≡ 0
geometricFixedIffGenusZeroRegression =
  FixedSelector.frobeniusFullyFixedIffFrickeGenusZero

finiteOggTableNotUsedInGeometricFixedSelectorRegression :
  FixedSelector.finiteOggControlTableUsed
    FixedSelector.canonicalFrickeFrobeniusFixedSelectorBoundary ≡ false
finiteOggTableNotUsedInGeometricFixedSelectorRegression = refl

------------------------------------------------------------------------
-- New Deligne--Rapoport quotient-node regressions.
------------------------------------------------------------------------

p37DerivedNodalGenusRegression :
  Nodal.arithmeticGenus
    (DRComb.canonicalFrickeQuotientDualGraph DRReg.p37DRData) ≡ 1
p37DerivedNodalGenusRegression = DRReg.p37DerivedQuotientArithmeticGenus

p43DerivedNodalGenusRegression :
  Nodal.arithmeticGenus
    (DRComb.canonicalFrickeQuotientDualGraph DRReg.p43DRData) ≡ 1
p43DerivedNodalGenusRegression = DRReg.p43DerivedQuotientArithmeticGenus

localQuadraticPairHasTwoQuotientBranchesRegression :
  (index : Fin 1) →
  DRLocal.quotientBranch (DRLocal.branch0Section index)
  ≡ DRLocal.quotientBranch0
localQuadraticPairHasTwoQuotientBranchesRegression =
  DRLocal.branch0SectionHasType

derivedSelectorRegression :
  (A : DRSelector.PrimeLevelFrickeSpecialFibreAuthority) →
  DRSelector.genericFrickeGenus A
  ≡ DRComb.pairedCount (DRSelector.supersingularFrobenius A)
derivedSelectorRegression = DRSelector.genericFrickeGenusEqualsDeclaredPairDefect

derivedFixedIffGenusZeroRegression :
  (A : DRSelector.PrimeLevelFrickeSpecialFibreAuthority) →
  DRSelector.GeometricallyFullyFixed A
  ↔ DRSelector.genericFrickeGenus A ≡ 0
derivedFixedIffGenusZeroRegression =
  DRSelector.frobeniusFullyFixedIffGenericFrickeGenusZero

duplicatePairAuthorityEliminatedRegression :
  DRSelector.duplicatePairCountAuthorityEliminated
    DRSelector.canonicalPrimeLevelDeligneRapoportFrickeSelectorBoundary ≡ true
duplicatePairAuthorityEliminatedRegression = refl
