{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact where

------------------------------------------------------------------------
-- R841 / DIRECT INSTANTANEOUS PHYSICAL SYSTEM FOR R829
--
-- R839 is the correct Round71 state for the later real-ODE lane.  R829,
-- however, is an instantaneous finite-state theorem and does not need to pass
-- through the reality lookup.  This owner constructs a Field30 physical system
-- whose velocity is definitionally Snapshot.velocity345.
--
-- Hence the R829 velocity same-object equality is refl on ALL Fourier modes.
-- Retained nonzero support is the literal cutoff-four carrier and
-- transversality is proved from the six explicit active rows.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345CanonicalStateRound838Exact as State838

F : C3.RealField _
F = Rational.rationalRealField

negativeK₁Transverse :
  (E : C3.IntegerEmbedding F) →
  C3.bilinearDot3
    (C3.modeVector E Active.k₁)
    (Snapshot.velocity345 Active.k₁)
  ≡ C3.complexZero F
negativeK₁Transverse E
  rewrite Scale.negativeMagnitudeEmbeddingScale E 2
        | Scale.negativeMagnitudeEmbeddingScale E 3
        | C3.embedZero E =
  Algebra.complexExt
    (solve (Scale.embeddingUnit E ∷ []))
    (solve (Scale.embeddingUnit E ∷ []))

negativeK₂Transverse :
  (E : C3.IntegerEmbedding F) →
  C3.bilinearDot3
    (C3.modeVector E Active.k₂)
    (Snapshot.velocity345 Active.k₂)
  ≡ C3.complexZero F
negativeK₂Transverse E
  rewrite Scale.negativeMagnitudeEmbeddingScale E 2
        | C3.embedZero E =
  Algebra.complexExt
    (solve (Scale.embeddingUnit E ∷ []))
    (solve (Scale.embeddingUnit E ∷ []))

negativeK₄Transverse :
  (E : C3.IntegerEmbedding F) →
  C3.bilinearDot3
    (C3.modeVector E Active.k₄)
    (Snapshot.velocity345 Active.k₄)
  ≡ C3.complexZero F
negativeK₄Transverse E
  rewrite Scale.negativeMagnitudeEmbeddingScale E 3
        | C3.embedZero E =
  Algebra.complexExt
    (solve (Scale.embeddingUnit E ∷ []))
    (solve (Scale.embeddingUnit E ∷ []))

snapshotVelocityTransverse :
  (E : C3.IntegerEmbedding F) →
  (mode : Z3.FourierMode) →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (Snapshot.velocity345 mode)
  ≡ C3.complexZero F
snapshotVelocityTransverse E mode
  with Snapshot.velocityActive mode in active
... | false =
  trans
    (cong (C3.bilinearDot3 (C3.modeVector E mode))
      (Snapshot.velocityInactiveZero mode active))
    (R30.bilinearDot3ZeroRight (C3.modeVector E mode))
... | true with State838.velocityActiveSound mode active
...   | State838.hit₁ same =
      subst
        (λ selected →
          C3.bilinearDot3
            (C3.modeVector E selected)
            (Snapshot.velocity345 selected)
          ≡ C3.complexZero F)
        (sym same)
        (negativeK₁Transverse E)
...   | State838.hit₂ same =
      subst
        (λ selected →
          C3.bilinearDot3
            (C3.modeVector E selected)
            (Snapshot.velocity345 selected)
          ≡ C3.complexZero F)
        (sym same)
        (negativeK₂Transverse E)
...   | State838.hit₄ same =
      subst
        (λ selected →
          C3.bilinearDot3
            (C3.modeVector E selected)
            (Snapshot.velocity345 selected)
          ≡ C3.complexZero F)
        (sym same)
        (negativeK₄Transverse E)
...   | State838.hit₅ same =
      subst
        (λ selected →
          C3.bilinearDot3
            (C3.modeVector E selected)
            (Snapshot.velocity345 selected)
          ≡ C3.complexZero F)
        (sym same)
        (State838.k₅Transverse E)
...   | State838.hit₇ same =
      subst
        (λ selected →
          C3.bilinearDot3
            (C3.modeVector E selected)
            (Snapshot.velocity345 selected)
          ≡ C3.complexZero F)
        (sym same)
        (State838.k₇Transverse E)
...   | State838.hit₈ same =
      subst
        (λ selected →
          C3.bilinearDot3
            (C3.modeVector E selected)
            (Snapshot.velocity345 selected)
          ≡ C3.complexZero F)
        (sym same)
        (State838.k₈Transverse E)

directAuditSystem :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Audit.FiniteComplex3GalerkinSystem F E I
directAuditSystem E I = record
  { Audit.FiniteComplex3GalerkinSystem.cutoff = 4
  ; Audit.FiniteComplex3GalerkinSystem.modes =
      Canonical.nonzeroCutoffModes 4
  ; Audit.FiniteComplex3GalerkinSystem.triads =
      Physical.physicalTriadEnumeration 4
  ; Audit.FiniteComplex3GalerkinSystem.velocity = Snapshot.velocity345
  ; Audit.FiniteComplex3GalerkinSystem.viscosity = 1
  ; Audit.FiniteComplex3GalerkinSystem.modeListed =
      λ mode → mode Cube.∈ Canonical.nonzeroCutoffModes 4
  ; Audit.FiniteComplex3GalerkinSystem.triadListed =
      λ tau → tau Cube.∈ Physical.physicalTriadEnumeration 4
  ; Audit.FiniteComplex3GalerkinSystem.modesAreLiteralCutoff =
      Canonical.nonzeroCutoffModes 4 ≡ Canonical.nonzeroCutoffModes 4
  ; Audit.FiniteComplex3GalerkinSystem.triadsAreLiteralEnumeration = refl
  ; Audit.FiniteComplex3GalerkinSystem.zeroModeExcluded =
      ∀ mode → mode Cube.∈ Canonical.nonzeroCutoffModes 4 →
        Z3.NonZeroMode mode
  ; Audit.FiniteComplex3GalerkinSystem.realityClosed =
      ∀ mode → Snapshot.velocity345 (Z3.negateMode mode)
        ≡ C3.complex3Conjugate (Snapshot.velocity345 mode)
  }

directPhysicalSystem :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Field30.PhysicalFiniteComplex3GalerkinSystem F
directPhysicalSystem E I = record
  { Field30.physicalEmbedding = E
  ; Field30.physicalInverseSquare = I
  ; Field30.finiteSystem = directAuditSystem E I
  ; Field30.viscosity = 1
  ; Field30.retainedModeNonzero =
      R404.fixedAuditRetainedModeNonzero
        (State838.geometry345 E I)
        State838.canonicalSnapshotState
  ; Field30.retainedVelocityTransverse =
      λ mode member → snapshotVelocityTransverse E mode
  }

directVelocitySame :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (mode : Z3.FourierMode) →
  Audit.velocityAt (Field30.finiteSystem (directPhysicalSystem E I)) mode
  ≡ Snapshot.velocity345 mode
directVelocitySame E I mode = refl

round841DirectInstantaneousPhysicalSystemConstructed : Bool
round841DirectInstantaneousPhysicalSystemConstructed = true

round841VelocitySameObjectIsDefinitional : Bool
round841VelocitySameObjectIsDefinitional = true

round841AllModeTransversalityClosed : Bool
round841AllModeTransversalityClosed = true

round841ProjectedNonlinearityRowsEvaluated : Bool
round841ProjectedNonlinearityRowsEvaluated = false

round841RealODECarrierClaimed : Bool
round841RealODECarrierClaimed = false

round841ClayPromotion : Bool
round841ClayPromotion = false

round841VelocitySameObjectIsDefinitionalIsTrue :
  round841VelocitySameObjectIsDefinitional ≡ true
round841VelocitySameObjectIsDefinitionalIsTrue = refl
