module DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact where

------------------------------------------------------------------------
-- GROUP-LEVEL U(1) INSIDE THE EXISTING UNIT-QUATERNION SU(2)
--
-- U(1) is realised as the unit circle in the (q0,q3)-plane of the repository's
-- concrete unit-quaternion SU(2).  Multiplication and inversion are literal
-- complex multiplication/conjugation, and the inclusion is proved to preserve
-- the existing SU(2) operations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import Data.List.Base using ([]; _∷_)
import Tactic.RingSolver as Solver

open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using (GroupStructure)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_; _*R_; -R_; zeroR; oneR; *-identityˡ; -‿involutive )
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2

record U1TorusElement : Set where
  constructor u1-torus
  field
    realPart imagPart : ℝ
    unitCircle :
      (realPart *R realPart) +R (imagPart *R imagPart) ≡ oneR

open U1TorusElement public

u1Ext : ∀ {u v : U1TorusElement} →
  realPart u ≡ realPart v → imagPart u ≡ imagPart v → u ≡ v
u1Ext {u1-torus a b p} {u1-torus .a .b q} refl refl =
  cong (u1-torus a b) (SU2.unitNormProofIrrelevance p q)

axisQuaternion : U1TorusElement → SU2.Quaternion
axisQuaternion u =
  SU2.quat (realPart u) zeroR zeroR (imagPart u)

axisNormSimplifies : ∀ a b →
  SU2.normSquaredQ (SU2.quat a zeroR zeroR b)
  ≡ (a *R a) +R (b *R b)
axisNormSimplifies a b =
  Solver.solve (a ∷ b ∷ []) SU2.realSolverRing

includeU1InSU2 : U1TorusElement → SU2.SU2Quaternion
includeU1InSU2 u =
  SU2.su2q (axisQuaternion u)
    (trans (axisNormSimplifies (realPart u) (imagPart u)) (unitCircle u))

complexNormMultiplicative : ∀ a b c d →
  (((a *R c) +R (-R (b *R d))) *R ((a *R c) +R (-R (b *R d))))
  +R (((a *R d) +R (b *R c)) *R ((a *R d) +R (b *R c)))
  ≡
  ((a *R a) +R (b *R b)) *R ((c *R c) +R (d *R d))
complexNormMultiplicative a b c d =
  Solver.solve (a ∷ b ∷ c ∷ d ∷ []) SU2.realSolverRing

u1Multiply : U1TorusElement → U1TorusElement → U1TorusElement
u1Multiply (u1-torus a b abNorm) (u1-torus c d cdNorm) =
  u1-torus
    ((a *R c) +R (-R (b *R d)))
    ((a *R d) +R (b *R c))
    (trans
      (complexNormMultiplicative a b c d)
      (trans
        (cong₂ _*R_ abNorm cdNorm)
        (*-identityˡ oneR)))

u1Identity : U1TorusElement
u1Identity =
  u1-torus oneR zeroR
    (Solver.solve [] SU2.realSolverRing)

u1Inverse : U1TorusElement → U1TorusElement
u1Inverse (u1-torus a b norm) =
  u1-torus a (-R b)
    (trans (Solver.solve (a ∷ b ∷ []) SU2.realSolverRing) norm)

u1MultiplyAssociative : ∀ a b c →
  u1Multiply (u1Multiply a b) c ≡ u1Multiply a (u1Multiply b c)
u1MultiplyAssociative
  (u1-torus a b _)
  (u1-torus c d _)
  (u1-torus e f _) =
  u1Ext
    (Solver.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) SU2.realSolverRing)
    (Solver.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) SU2.realSolverRing)

u1IdentityLeft : ∀ u → u1Multiply u1Identity u ≡ u
u1IdentityLeft (u1-torus a b _) =
  u1Ext
    (Solver.solve (a ∷ b ∷ []) SU2.realSolverRing)
    (Solver.solve (a ∷ b ∷ []) SU2.realSolverRing)

u1IdentityRight : ∀ u → u1Multiply u u1Identity ≡ u
u1IdentityRight (u1-torus a b _) =
  u1Ext
    (Solver.solve (a ∷ b ∷ []) SU2.realSolverRing)
    (Solver.solve (a ∷ b ∷ []) SU2.realSolverRing)

u1InverseLeft : ∀ u → u1Multiply (u1Inverse u) u ≡ u1Identity
u1InverseLeft (u1-torus a b norm) =
  u1Ext
    (trans (Solver.solve (a ∷ b ∷ []) SU2.realSolverRing) norm)
    (Solver.solve (a ∷ b ∷ []) SU2.realSolverRing)

u1InverseRight : ∀ u → u1Multiply u (u1Inverse u) ≡ u1Identity
u1InverseRight (u1-torus a b norm) =
  u1Ext
    (trans (Solver.solve (a ∷ b ∷ []) SU2.realSolverRing) norm)
    (Solver.solve (a ∷ b ∷ []) SU2.realSolverRing)

u1InverseInvolutive : ∀ u → u1Inverse (u1Inverse u) ≡ u
u1InverseInvolutive (u1-torus a b _) =
  u1Ext refl (-‿involutive b)

u1TorusGroup : GroupStructure
u1TorusGroup = record
  { Carrier = U1TorusElement
  ; unit = u1Identity
  ; multiply = u1Multiply
  ; inverse = u1Inverse
  ; multiplyAssoc = u1MultiplyAssociative
  ; unitLeft = u1IdentityLeft
  ; unitRight = u1IdentityRight
  ; inverseLeft = u1InverseLeft
  ; inverseRight = u1InverseRight
  ; inverseInvolutive = u1InverseInvolutive
  }

includePreservesMultiply : ∀ u v →
  includeU1InSU2 (u1Multiply u v)
  ≡ SU2.su2Multiply (includeU1InSU2 u) (includeU1InSU2 v)
includePreservesMultiply
  (u1-torus a b _) (u1-torus c d _) =
  SU2.su2QuaternionExt
    (SU2.quaternionExt
      (Solver.solve (a ∷ b ∷ c ∷ d ∷ []) SU2.realSolverRing)
      (Solver.solve (a ∷ b ∷ c ∷ d ∷ []) SU2.realSolverRing)
      (Solver.solve (a ∷ b ∷ c ∷ d ∷ []) SU2.realSolverRing)
      (Solver.solve (a ∷ b ∷ c ∷ d ∷ []) SU2.realSolverRing))

includePreservesInverse : ∀ u →
  includeU1InSU2 (u1Inverse u) ≡ SU2.su2Inverse (includeU1InSU2 u)
includePreservesInverse (u1-torus a b _) =
  SU2.su2QuaternionExt
    (SU2.quaternionExt refl refl refl refl)

includePreservesIdentity :
  includeU1InSU2 u1Identity ≡ SU2.su2Identity
includePreservesIdentity =
  SU2.su2QuaternionExt (SU2.quaternionExt refl refl refl refl)

groupLevelU1SubgroupConstructed : Bool
groupLevelU1SubgroupConstructed = true

inclusionPreservesMultiplication : Bool
inclusionPreservesMultiplication = true

inclusionPreservesInversion : Bool
inclusionPreservesInversion = true

u1GroupRestrictionInsideSU2 : Bool
u1GroupRestrictionInsideSU2 = true

standardModelHyperchargeEmbeddingPaid : Bool
standardModelHyperchargeEmbeddingPaid = false

nonAbelianMassGapTransferredToU1 : Bool
nonAbelianMassGapTransferredToU1 = false

record U1SU2GroupTorusBoundary : Set where
  constructor u1-su2-group-torus-boundary
  field
    concreteUnitQuaternionSU2Reused : Bool
    literalU1GroupConstructed : Bool
    multiplicationInclusionTheoremPaid : Bool
    inversionInclusionTheoremPaid : Bool
    smHyperchargeRepresentationAutomaticallyRecovered : Bool
    nonAbelianMassGapAutomaticallyInherited : Bool

canonicalU1SU2GroupTorusBoundary : U1SU2GroupTorusBoundary
canonicalU1SU2GroupTorusBoundary =
  u1-su2-group-torus-boundary true true true true false false
