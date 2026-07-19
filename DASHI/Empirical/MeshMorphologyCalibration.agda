module DASHI.Empirical.MeshMorphologyCalibration where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

-- This module deliberately does not infer anatomy.
-- A system morphology label is licensed only by a human-labelled calibration
-- exemplar and an explicit comparison result over barycentric radial-mass
-- signatures.

data Morphology : Set where
  human ogre : Morphology

data Comparison : Set where
  nearer-human nearer-ogre unresolved : Comparison

data Classification : Set where
  classified-human classified-ogre needs-human : Classification

record BarycentricRadialMassModel
       (Mesh Point Signature : Set) : Set₁ where
  field
    barycentre : Mesh → Point
    radialMassFrom : Mesh → Point → Signature
    distance : Signature → Signature → Nat

  radialMass : Mesh → Signature
  radialMass mesh = radialMassFrom mesh (barycentre mesh)

record HumanCalibration (Mesh : Set) : Set where
  constructor calibration
  field
    humanExemplar : Mesh
    ogreExemplar : Mesh

-- The comparison procedure is outside the trusted semantic core. It may be a
-- numerical nearest-exemplar routine, but its result is explicit input here.
-- In particular, no head/feet/limb heuristic occurs in this classifier.
classify : {Mesh : Set} → HumanCalibration Mesh → Mesh → Comparison → Classification
classify calibration mesh nearer-human = classified-human
classify calibration mesh nearer-ogre = classified-ogre
classify calibration mesh unresolved = needs-human

-- A label is never synthesized outside the two labels supplied by calibration.
data LicensedByCalibration {Mesh : Set}
     (c : HumanCalibration Mesh) : Classification → Set where
  by-human-exemplar : LicensedByCalibration c classified-human
  by-ogre-exemplar : LicensedByCalibration c classified-ogre
  deferred-to-human : LicensedByCalibration c needs-human

classificationLicensed :
  {Mesh : Set} →
  (c : HumanCalibration Mesh) →
  (mesh : Mesh) →
  (comparison : Comparison) →
  LicensedByCalibration c (classify c mesh comparison)
classificationLicensed c mesh nearer-human = by-human-exemplar
classificationLicensed c mesh nearer-ogre = by-ogre-exemplar
classificationLicensed c mesh unresolved = deferred-to-human

-- The unresolved branch is a first-class fail-closed result, not an implicit
-- default to either morphology.
unresolvedNeedsHuman :
  {Mesh : Set} →
  (c : HumanCalibration Mesh) →
  (mesh : Mesh) →
  classify c mesh unresolved ≡ needs-human
unresolvedNeedsHuman c mesh = refl

humanComparisonLabelsHuman :
  {Mesh : Set} →
  (c : HumanCalibration Mesh) →
  (mesh : Mesh) →
  classify c mesh nearer-human ≡ classified-human
humanComparisonLabelsHuman c mesh = refl

ogreComparisonLabelsOgre :
  {Mesh : Set} →
  (c : HumanCalibration Mesh) →
  (mesh : Mesh) →
  classify c mesh nearer-ogre ≡ classified-ogre
ogreComparisonLabelsOgre c mesh = refl
