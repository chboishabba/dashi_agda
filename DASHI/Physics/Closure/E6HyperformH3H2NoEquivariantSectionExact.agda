module DASHI.Physics.Closure.E6HyperformH3H2NoEquivariantSectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3H2PhaseIncidenceExact as Incidence
import DASHI.Physics.Closure.E6HyperformH3H2OrderParameterGeometryExact as Geometry

h3BaseCount : Nat
h3BaseCount = 120

fibreCount : Nat
fibreCount = 9

selectedH3StabilizerOrder : Nat
selectedH3StabilizerOrder = 432

effectiveFibreActionOrder : Nat
effectiveFibreActionOrder = 72

translationSubgroupOrder : Nat
translationSubgroupOrder = 9

record H3H2AssociatedBundleLocalReceipt : Set where
  constructor h3-h2-associated-bundle-local-receipt
  field
    h3BaseWeylHomogeneous : Bool
    nineIncidentH2FibrePaid : Bool
    incidenceWeylEquivariant : Bool
    decoratedMetricWeylCovariant : Bool
    selectedH3Stabilizer432Paid : Bool
    effectiveFibreAction72Paid : Bool
    regularTranslationNinePaid : Bool
    stabilizerHasFixedFibrePoint : Bool
    weylEquivariantSectionExists : Bool
    sectionChoiceBreaksSymmetry : Bool
    finiteAssociatedBundlePaidLocally : Bool
    physicalSelectionLawPaid : Bool
    boundary : String
open H3H2AssociatedBundleLocalReceipt public

canonicalH3H2AssociatedBundleLocalReceipt : H3H2AssociatedBundleLocalReceipt
canonicalH3H2AssociatedBundleLocalReceipt =
  h3-h2-associated-bundle-local-receipt
    true true true true true true true
    false false true true false
    "The selected-H3 stabilizer acts transitively on its nine incident H2 faces through the regular F3^2 translation subgroup. Therefore no stabilizer-fixed H2 choice exists, so no Weyl-equivariant rule selects one H2 decoration over every H3 patch. The incidence bundle and decorated metrics are covariant; an actual section is extra symmetry-breaking data."

incidenceReceipt : Incidence.H3H2PhaseIncidenceLocalReceipt
incidenceReceipt = Incidence.canonicalH3H2PhaseIncidenceLocalReceipt

geometryReceipt : Geometry.H3H2OrderParameterGeometryLocalReceipt
geometryReceipt = Geometry.canonicalH3H2OrderParameterGeometryLocalReceipt

record H3H2SectionProducer : Set₁ where
  field
    Base : Set
    Fibre : Base → Set
    selected : (x : Base) → Fibre x
    selectionLawReceipt : Set
    dynamicsReceipt : Set
    continuumReceipt : Set
    calibrationReceipt : Set
open H3H2SectionProducer public

data CovariantBundleCreatesCanonicalSection : Set where

covariantBundleDoesNotCreateCanonicalSection :
  CovariantBundleCreatesCanonicalSection → {A : Set} → A
covariantBundleDoesNotCreateCanonicalSection ()
