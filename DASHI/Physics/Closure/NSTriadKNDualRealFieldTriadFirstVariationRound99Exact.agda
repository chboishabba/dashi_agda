module DASHI.Physics.Closure.NSTriadKNDualRealFieldTriadFirstVariationRound99Exact where

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
-- ROUND99 / DIFFERENTIATE THE EXACT CANCELLATION, DO NOT RE-ESTIMATE IT
--
-- The complete triad-energy cancellation is already proved over the abstract
-- repository `RealField`.  Instead of expanding every mixed cubic term again,
-- lift that theorem to the dual-number ring F[eps]/(eps^2), evaluate it on
--
--     u + eps h,
--
-- and project the eps coefficient.  Because `RealField` only asks for the
-- commutative-ring laws (its `inverse` operation carries no inverse axiom), the
-- dual lift is source-native and requires no extra analytic assumption.
--
-- The result is exact first-variation cancellation for every INTERNAL triad:
--
--   dT_k + dT_p + dT_q = 0
--
-- whenever both u and h obey the Fourier reality and divergence-free laws.
-- Thus differentiated packet transfer can only receive a contribution from
-- packet-boundary incidences; internal quartic variation is not an estimate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3EnergyCancellation as Energy

record Dual {r : Level} (F : C3.RealField r) : Set r where
  constructor dual
  field
    primal tangent : C3.Carrier F
open Dual public

dualExt : ∀ {r} {F : C3.RealField r} {a b : Dual F} →
  primal a ≡ primal b → tangent a ≡ tangent b → a ≡ b
dualExt {a = dual ap at} {b = dual .ap .at} refl refl = refl

dualZero : ∀ {r} (F : C3.RealField r) → Dual F
dualZero F = dual (C3.zero F) (C3.zero F)

dualOne : ∀ {r} (F : C3.RealField r) → Dual F
dualOne F = dual (C3.one F) (C3.zero F)

dualAdd : ∀ {r} {F : C3.RealField r} → Dual F → Dual F → Dual F
dualAdd {F = F} (dual a da) (dual b db) =
  dual (C3.add F a b) (C3.add F da db)

dualNegate : ∀ {r} {F : C3.RealField r} → Dual F → Dual F
dualNegate {F = F} (dual a da) =
  dual (C3.negate F a) (C3.negate F da)

dualMultiply : ∀ {r} {F : C3.RealField r} → Dual F → Dual F → Dual F
dualMultiply {F = F} (dual a da) (dual b db) =
  dual
    (C3.multiply F a b)
    (C3.add F (C3.multiply F a db) (C3.multiply F da b))

dualInverse : ∀ {r} {F : C3.RealField r} → Dual F → Dual F
dualInverse {F = F} (dual a da) = dual (C3.inverse F a) (C3.zero F)

dualRealField : ∀ {r} (F : C3.RealField r) → C3.RealField r
dualRealField F = record
  { Carrier = Dual F
  ; zero = dualZero F
  ; one = dualOne F
  ; add = dualAdd
  ; multiply = dualMultiply
  ; negate = dualNegate
  ; inverse = dualInverse
  ; addAssociative = λ (dual a da) (dual b db) (dual c dc) →
      dualExt (C3.addAssociative F a b c) (C3.addAssociative F da db dc)
  ; addCommutative = λ (dual a da) (dual b db) →
      dualExt (C3.addCommutative F a b) (C3.addCommutative F da db)
  ; addZeroLeft = λ (dual a da) →
      dualExt (C3.addZeroLeft F a) (C3.addZeroLeft F da)
  ; addInverseLeft = λ (dual a da) →
      dualExt (C3.addInverseLeft F a) (C3.addInverseLeft F da)
  ; multiplyAssociative = multiplyAssoc
  ; multiplyCommutative = multiplyComm
  ; multiplyOneLeft = multiplyOne
  ; distributeLeft = distribute
  ; negateInvolutive = λ (dual a da) →
      dualExt (C3.negateInvolutive F a) (C3.negateInvolutive F da)
  ; negateZero = dualExt (C3.negateZero F) (C3.negateZero F)
  }
  where
  module P = Algebra.Polynomial F

  multiplyAssoc : ∀ x y z →
    dualMultiply (dualMultiply x y) z ≡ dualMultiply x (dualMultiply y z)
  multiplyAssoc (dual a da) (dual b db) (dual c dc) =
    dualExt
      (C3.multiplyAssociative F a b c)
      (P.R.solve 6
        (λ a da b db c dc →
          (((a P.R.⊗ b) P.R.⊗ dc)
            P.R.⊕ (((a P.R.⊗ db) P.R.⊕ (da P.R.⊗ b)) P.R.⊗ c))
          P.R.⊜
          ((a P.R.⊗ ((b P.R.⊗ dc) P.R.⊕ (db P.R.⊗ c)))
            P.R.⊕ (da P.R.⊗ (b P.R.⊗ c))))
        refl a da b db c dc)

  multiplyComm : ∀ x y → dualMultiply x y ≡ dualMultiply y x
  multiplyComm (dual a da) (dual b db) =
    dualExt
      (C3.multiplyCommutative F a b)
      (P.R.solve 4
        (λ a da b db →
          ((a P.R.⊗ db) P.R.⊕ (da P.R.⊗ b))
          P.R.⊜ ((b P.R.⊗ da) P.R.⊕ (db P.R.⊗ a)))
        refl a da b db)

  multiplyOne : ∀ x → dualMultiply (dualOne F) x ≡ x
  multiplyOne (dual a da) =
    dualExt
      (C3.multiplyOneLeft F a)
      (P.R.solve 2
        (λ a da →
          ((P.R.K (C3.one F) P.R.⊗ da)
            P.R.⊕ (P.R.K (C3.zero F) P.R.⊗ a)) P.R.⊜ da)
        refl a da)

  distribute : ∀ x y z →
    dualMultiply x (dualAdd y z)
    ≡ dualAdd (dualMultiply x y) (dualMultiply x z)
  distribute (dual a da) (dual b db) (dual c dc) =
    dualExt
      (C3.distributeLeft F a b c)
      (P.R.solve 6
        (λ a da b db c dc →
          ((a P.R.⊗ (db P.R.⊕ dc))
            P.R.⊕ (da P.R.⊗ (b P.R.⊕ c)))
          P.R.⊜
          (((a P.R.⊗ db) P.R.⊕ (da P.R.⊗ b))
            P.R.⊕ ((a P.R.⊗ dc) P.R.⊕ (da P.R.⊗ c))))
        refl a da b db c dc)

constantDual : ∀ {r} {F : C3.RealField r} → C3.Carrier F → Dual F
constantDual {F = F} a = dual a (C3.zero F)

dualIntegerEmbedding : ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → C3.IntegerEmbedding (dualRealField F)
dualIntegerEmbedding {F = F} E = record
  { embedInteger = λ z → constantDual (C3.embedInteger E z)
  ; embedZero = dualExt (C3.embedZero E) refl
  ; embedAdd = λ a b →
      dualExt (C3.embedAdd E a b) (sym (C3.addZeroLeft F (C3.zero F)))
  ; embedNegate = λ a →
      dualExt (C3.embedNegate E a) (sym (C3.negateZero F))
  }

dualModeInverseSquare : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) →
  C3.ModeInverseSquare F E →
  C3.ModeInverseSquare (dualRealField F) (dualIntegerEmbedding E)
dualModeInverseSquare {F = F} E I = record
  { inverseNormSquared = λ k → constantDual (C3.inverseNormSquared I k)
  ; normSquared = λ k → constantDual (C3.normSquared I k)
  ; normSquaredMeaning = normMeaning
  ; inverseLaw = inverseMeaning
  }
  where
  module P = Algebra.Polynomial F

  normMeaning : ∀ k →
    constantDual (C3.normSquared I k)
    ≡
    C3.add (dualRealField F)
      (C3.add (dualRealField F)
        (C3.multiply (dualRealField F)
          (C3.embedInteger (dualIntegerEmbedding E) (Z3.kx k))
          (C3.embedInteger (dualIntegerEmbedding E) (Z3.kx k)))
        (C3.multiply (dualRealField F)
          (C3.embedInteger (dualIntegerEmbedding E) (Z3.ky k))
          (C3.embedInteger (dualIntegerEmbedding E) (Z3.ky k))))
      (C3.multiply (dualRealField F)
        (C3.embedInteger (dualIntegerEmbedding E) (Z3.kz k))
        (C3.embedInteger (dualIntegerEmbedding E) (Z3.kz k)))
  normMeaning k =
    dualExt
      (C3.normSquaredMeaning I k)
      (P.R.solve 3
        (λ x y z →
          P.R.K (C3.zero F)
          P.R.⊜
          ((((x P.R.⊗ P.R.K (C3.zero F))
              P.R.⊕ (P.R.K (C3.zero F) P.R.⊗ x))
            P.R.⊕ ((y P.R.⊗ P.R.K (C3.zero F))
              P.R.⊕ (P.R.K (C3.zero F) P.R.⊗ y)))
            P.R.⊕ ((z P.R.⊗ P.R.K (C3.zero F))
              P.R.⊕ (P.R.K (C3.zero F) P.R.⊗ z))))
        refl
        (C3.embedInteger E (Z3.kx k))
        (C3.embedInteger E (Z3.ky k))
        (C3.embedInteger E (Z3.kz k)))

  inverseMeaning : ∀ k → Z3.NonZeroMode k →
    C3.multiply (dualRealField F)
      (constantDual (C3.inverseNormSquared I k))
      (constantDual (C3.normSquared I k))
    ≡ C3.one (dualRealField F)
  inverseMeaning k nz =
    dualExt
      (C3.inverseLaw I k nz)
      (P.R.solve 2
        (λ a b →
          ((a P.R.⊗ P.R.K (C3.zero F))
            P.R.⊕ (P.R.K (C3.zero F) P.R.⊗ b))
          P.R.⊜ P.R.K (C3.zero F))
        refl (C3.inverseNormSquared I k) (C3.normSquared I k))

liftComplex : ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex (dualRealField F)
liftComplex (C3.complex ar ai) (C3.complex dr di) =
  C3.complex (dual ar dr) (dual ai di)

liftComplex3 : ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 (dualRealField F)
liftComplex3 (C3.complex3 ax ay az) (C3.complex3 dx dy dz) =
  C3.complex3 (liftComplex ax dx) (liftComplex ay dy) (liftComplex az dz)

complexTangent : ∀ {r} {F : C3.RealField r} →
  C3.Complex (dualRealField F) → C3.Complex F
complexTangent (C3.complex (dual ar dr) (dual ai di)) = C3.complex dr di

complex3Tangent : ∀ {r} {F : C3.RealField r} →
  C3.Complex3 (dualRealField F) → C3.Complex3 F
complex3Tangent (C3.complex3 x y z) =
  C3.complex3 (complexTangent x) (complexTangent y) (complexTangent z)

liftConjugate : ∀ {r} {F : C3.RealField r} (u h : C3.Complex F) →
  C3.complexConjugate (liftComplex u h)
  ≡ liftComplex (C3.complexConjugate u) (C3.complexConjugate h)
liftConjugate {F = F} (C3.complex ur ui) (C3.complex hr hi)
  rewrite C3.negateZero F = refl

liftComplex3Conjugate : ∀ {r} {F : C3.RealField r}
  (u h : C3.Complex3 F) →
  C3.complex3Conjugate (liftComplex3 u h)
  ≡ liftComplex3 (C3.complex3Conjugate u) (C3.complex3Conjugate h)
liftComplex3Conjugate (C3.complex3 ux uy uz) (C3.complex3 hx hy hz)
  rewrite liftConjugate ux hx | liftConjugate uy hy | liftConjugate uz hz = refl

liftedReality : ∀ {r} {F : C3.RealField r}
  (u h : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition u → Audit.RealityCondition h →
  Audit.RealityCondition (λ k → liftComplex3 (u k) (h k))
liftedReality u h uReality hReality k
  rewrite uReality k | hReality k =
  sym (liftComplex3Conjugate (u k) (h k))

liftBilinearDotWithConstantMode : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (u h : C3.Complex3 F) (k : Z3.FourierMode) →
  C3.bilinearDot3
    (liftComplex3 u h)
    (C3.modeVector (dualIntegerEmbedding E) k)
  ≡ liftComplex
      (C3.bilinearDot3 u (C3.modeVector E k))
      (C3.bilinearDot3 h (C3.modeVector E k))
liftBilinearDotWithConstantMode {F = F} E
    (C3.complex3 (C3.complex ux uxi) (C3.complex uy uyi) (C3.complex uz uzi))
    (C3.complex3 (C3.complex hx hxi) (C3.complex hy hyi) (C3.complex hz hzi))
    (Z3.mode kx ky kz) =
  refl

liftedDivergenceFree : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F)
  (u h : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E u →
  Audit.DivergenceFreeCondition E h →
  Audit.DivergenceFreeCondition (dualIntegerEmbedding E)
    (λ k → liftComplex3 (u k) (h k))
liftedDivergenceFree {F = F} E u h uDiv hDiv k =
  trans
    (liftBilinearDotWithConstantMode E (u k) (h k) k)
    (cong₂ liftComplex (uDiv k) (hDiv k))

orderedPairFirstVariation : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
orderedPairFirstVariation E I tau u h =
  complexTangent
    (Audit.orderedPairSignedTransferAt
      (dualIntegerEmbedding E) (dualModeInverseSquare E I) tau
      (λ k → liftComplex3 (u k) (h k)))

internalTriadFirstVariationCancellation : ∀ {r} {F : C3.RealField r}
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (tau : Physical.PhysicalTriadIncidence)
  (u h : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition u → Audit.RealityCondition h →
  Audit.DivergenceFreeCondition E u → Audit.DivergenceFreeCondition E h →
  C3.complexAdd
    (C3.complexAdd
      (orderedPairFirstVariation E I tau u h)
      (orderedPairFirstVariation E I (Orbit.pEnergyLeg tau) u h))
    (orderedPairFirstVariation E I (Orbit.qEnergyLeg tau) u h)
  ≡ C3.complexZero F
internalTriadFirstVariationCancellation {F = F} E I tau u h
    uReality hReality uDiv hDiv =
  cong complexTangent
    (Audit.completeTriadCancellation
      (Energy.exactTriadEnergyCancellation
        (dualIntegerEmbedding E) (dualModeInverseSquare E I) tau)
      (λ k → liftComplex3 (u k) (h k))
      (liftedReality u h uReality hReality)
      (liftedDivergenceFree E u h uDiv hDiv))

round99DualRealFieldLiftConstructed : Bool
round99DualRealFieldLiftConstructed = true

round99InternalTriadFirstVariationCancelsExactly : Bool
round99InternalTriadFirstVariationCancelsExactly = true

round99DifferentiatedPacketTransferIsBoundaryOnly : Bool
round99DifferentiatedPacketTransferIsBoundaryOnly = true
