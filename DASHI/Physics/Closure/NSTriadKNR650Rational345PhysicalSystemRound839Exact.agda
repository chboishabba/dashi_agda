{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345PhysicalSystemRound839Exact where

------------------------------------------------------------------------
-- R839 / ACTUAL PHYSICAL FINITE GALERKIN SYSTEM FOR THE 3-4-5 SNAPSHOT
--
-- R838 constructs the genuine Round71 radius-four canonical reality state and
-- proves transversality on the stored positive representatives.  This owner
-- upgrades that state to Field30.PhysicalFiniteComplex3GalerkinSystem:
--
--   * retained modes are the literal nonzero cutoff-four cube;
--   * triads are the literal exhaustive physical enumeration;
--   * velocity is the Round71 reality lookup of the R838 state;
--   * every retained mode is nonzero (R404);
--   * transversality on the negative sheet is derived by conjugation.
--
-- The geometry E/I remains a parameter.  No projected-nonlinearity numerical
-- evaluation is claimed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact as Orbit
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Fixed
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityLookupExactRound71Exact as Lookup
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNR650Rational345CanonicalStateRound838Exact as State838
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot

F : C3.RealField _
F = Rational.rationalRealField

removeZeroMemberSource :
  ∀ {mode modes} →
  mode Cube.∈ Canonical.removeZero modes →
  mode Cube.∈ modes
removeZeroMemberSource {modes = []} ()
removeZeroMemberSource {mode} {modes = head ∷ tail} member
  with Output.modeEqual head Z3.zeroMode
... | true = Cube.there (removeZeroMemberSource member)
... | false with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest = Cube.there (removeZeroMemberSource rest)

retainedModeCutoffBound :
  ∀ {mode} →
  mode Cube.∈ Canonical.nonzeroCutoffModes 4 →
  Cube.InCutoffCube 4 mode
retainedModeCutoffBound {mode} member =
  Cube.cutoffModeEnumerationSound 4 mode
    (removeZeroMemberSource member)

positiveRealityAtRepresentative :
  (representative : Z3.FourierMode) →
  representative Cube.∈ Orbit.canonicalCutoffOrbitModes 4 →
  Fixed.realityVelocity State838.canonicalSnapshotState
    (Z3.negateMode representative)
  ≡
  C3.complex3Conjugate
    (Fixed.realityVelocity State838.canonicalSnapshotState representative)
positiveRealityAtRepresentative representative member =
  let
    entry =
      Fixed.canonical-mode-value representative
        (Snapshot.velocity345 representative)
    entryMember =
      State838.snapshotEntryMember member
    negative =
      Lookup.realityVelocityNegativeExact
        State838.canonicalSnapshotState entry entryMember
    positive =
      State838.positiveVelocityExact representative member
  in
  trans negative
    (cong C3.complex3Conjugate (sym positive))

negativeRepresentativeTransverse :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (representative : Z3.FourierMode) →
  (member : representative Cube.∈ Orbit.canonicalCutoffOrbitModes 4) →
  C3.bilinearDot3
    (C3.modeVector E (Z3.negateMode representative))
    (Fixed.realityVelocity State838.canonicalSnapshotState
      (Z3.negateMode representative))
  ≡ C3.complexZero F
negativeRepresentativeTransverse E I representative member =
  let
    positiveTransverse =
      State838.canonicalSnapshotPositiveTransverse E I
        representative member

    conjugateTransverse =
      Phase.canonicalConjugatePreservesTransverse E
        representative
        (Fixed.realityVelocity State838.canonicalSnapshotState representative)
        positiveTransverse

    reality =
      positiveRealityAtRepresentative representative member
  in
  trans
    (cong
      (C3.bilinearDot3
        (C3.modeVector E (Z3.negateMode representative)))
      reality)
    conjugateTransverse

retainedVelocityTransverse :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (mode : Z3.FourierMode) →
  mode Cube.∈ Canonical.nonzeroCutoffModes 4 →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (Fixed.realityVelocity State838.canonicalSnapshotState mode)
  ≡ C3.complexZero F
retainedVelocityTransverse E I mode member =
  let
    nonzero = R404.nonzeroCutoffMemberNonzero member
    represented =
      Orbit.canonicalCutoffRepresentsEveryNonzeroOrbit
        (retainedModeCutoffBound member) nonzero
    representative = Orbit.representative represented
    representativeMember =
      Orbit.representativeInCanonicalCutoff represented
  in
  choose representative representativeMember
    (Orbit.representativeIsKOrNegK represented)
  where
  choose :
    (representative : Z3.FourierMode) →
    representative Cube.∈ Orbit.canonicalCutoffOrbitModes 4 →
    (representative ≡ mode) ⊎
      (representative ≡ Z3.negateMode mode) →
    C3.bilinearDot3
      (C3.modeVector E mode)
      (Fixed.realityVelocity State838.canonicalSnapshotState mode)
    ≡ C3.complexZero F
  choose representative representativeMember (inj₁ representativeIsMode) =
    subst
      (λ selected →
        C3.bilinearDot3
          (C3.modeVector E selected)
          (Fixed.realityVelocity State838.canonicalSnapshotState selected)
        ≡ C3.complexZero F)
      representativeIsMode
      (State838.canonicalSnapshotPositiveTransverse E I
        representative representativeMember)
  choose representative representativeMember (inj₂ representativeIsNegMode) =
    let
      negateRepresentativeIsMode :
        Z3.negateMode representative ≡ mode
      negateRepresentativeIsMode =
        trans
          (cong Z3.negateMode representativeIsNegMode)
          (Symmetry.negateModeInvolutive mode)
    in
    subst
      (λ selected →
        C3.bilinearDot3
          (C3.modeVector E selected)
          (Fixed.realityVelocity State838.canonicalSnapshotState selected)
        ≡ C3.complexZero F)
      negateRepresentativeIsMode
      (negativeRepresentativeTransverse E I
        representative representativeMember)

physicalSnapshotSystem :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Field30.PhysicalFiniteComplex3GalerkinSystem F
physicalSnapshotSystem E I = record
  { Field30.physicalEmbedding = E
  ; Field30.physicalInverseSquare = I
  ; Field30.finiteSystem =
      Fixed.fixedAuditSystem (State838.geometry345 E I)
        State838.canonicalSnapshotState
  ; Field30.viscosity = 1
  ; Field30.retainedModeNonzero =
      R404.fixedAuditRetainedModeNonzero
        (State838.geometry345 E I)
        State838.canonicalSnapshotState
  ; Field30.retainedVelocityTransverse =
      retainedVelocityTransverse E I
  }

physicalSnapshotCutoffIsFour :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Audit.cutoff (Field30.finiteSystem (physicalSnapshotSystem E I)) ≡ 4
physicalSnapshotCutoffIsFour E I = refl

physicalSnapshotModesAreLiteralNonzeroCutoff :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Audit.modes (Field30.finiteSystem (physicalSnapshotSystem E I))
  ≡ Canonical.nonzeroCutoffModes 4
physicalSnapshotModesAreLiteralNonzeroCutoff E I = refl

round839ActualPhysicalFiniteSystemConstructed : Bool
round839ActualPhysicalFiniteSystemConstructed = true

round839RetainedNonzeroSupportClosed : Bool
round839RetainedNonzeroSupportClosed = true

round839RetainedTransversalityClosed : Bool
round839RetainedTransversalityClosed = true

round839ProjectedNonlinearityRowsEvaluated : Bool
round839ProjectedNonlinearityRowsEvaluated = false

round839ClayPromotion : Bool
round839ClayPromotion = false

round839ActualPhysicalFiniteSystemConstructedIsTrue :
  round839ActualPhysicalFiniteSystemConstructed ≡ true
round839ActualPhysicalFiniteSystemConstructedIsTrue = refl
