module DASHI.Physics.YangMills.BalabanSU2SecondJetSUNInstanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieGroupDerived using
  (conjugate; rightInverseAction)
open import DASHI.Physics.YangMills.SUNWilsonClassFunction
open import DASHI.Physics.YangMills.SUNWilsonAction using (WilsonScalarOperations)
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact

------------------------------------------------------------------------
-- Exact group of unit SU(2) second jets.
------------------------------------------------------------------------

twoR : ℚ
twoR = 1ℚ + 1ℚ

unitDefect : SU2SecondJet → ℚ
unitDefect path =
  twoR * realSecond path + normSqV (imaginaryFirst path)

inverseJet : SU2SecondJet → SU2SecondJet
inverseJet (jet second first) = jet second (negV first)

jetExt : ∀ {left right : SU2SecondJet} →
  realSecond left ≡ realSecond right →
  imaginaryFirst left ≡ imaginaryFirst right →
  left ≡ right
jetExt {jet leftSecond leftFirst} {jet .leftSecond .leftFirst} refl refl = refl

open import Data.List.Base using (_∷_; [])

jetMultiplyAssociativeScalar : ∀ ar ax ay az br bx by bz cr cx cy cz →
  ((ar + br + (- (ax * bx + (ay * by + az * bz)))) + cr + (- ((ax + bx) * cx + ((ay + by) * cy + (az + bz) * cz)))) ≡
  (ar + (br + cr + (- (bx * cx + (by * cy + bz * cz)))) + (- (ax * (bx + cx) + (ay * (by + cy) + az * (bz + cz)))))
jetMultiplyAssociativeScalar ar ax ay az br bx by bz cr cx cy cz =
  ℚRing.solve (ar ∷ ax ∷ ay ∷ az ∷ br ∷ bx ∷ by ∷ bz ∷ cr ∷ cx ∷ cy ∷ cz ∷ [])

jetMultiplyCommutativeScalar : ∀ ar ax ay az br bx by bz →
  (ar + br + (- (ax * bx + (ay * by + az * bz)))) ≡
  (br + ar + (- (bx * ax + (by * ay + bz * az))))
jetMultiplyCommutativeScalar ar ax ay az br bx by bz =
  ℚRing.solve (ar ∷ ax ∷ ay ∷ az ∷ br ∷ bx ∷ by ∷ bz ∷ [])

assocQ : ∀ a b c → (a + b) + c ≡ a + (b + c)
assocQ = ℚRing.solve-∀

commQ : ∀ a b → a + b ≡ b + a
commQ = ℚRing.solve-∀

jetMultiplyAssociative : ∀ first second third →
  (first *j second) *j third ≡ first *j (second *j third)
jetMultiplyAssociative
  (jet ar (lie3 ax ay az))
  (jet br (lie3 bx by bz))
  (jet cr (lie3 cx cy cz)) =
  jetExt
    (jetMultiplyAssociativeScalar ar ax ay az br bx by bz cr cx cy cz)
    (lie3Ext
      (assocQ ax bx cx)
      (assocQ ay by cy)
      (assocQ az bz cz))

jetMultiplyCommutative : ∀ first second → first *j second ≡ second *j first
jetMultiplyCommutative
  (jet ar (lie3 ax ay az))
  (jet br (lie3 bx by bz)) =
  jetExt
    (jetMultiplyCommutativeScalar ar ax ay az br bx by bz)
    (lie3Ext
      (commQ ax bx)
      (commQ ay by)
      (commQ az bz))

zeroAddL : ∀ x → 0ℚ + x ≡ x
zeroAddL = ℚRing.solve-∀

zeroAddR : ∀ x → x + 0ℚ ≡ x
zeroAddR = ℚRing.solve-∀

negInvol : ∀ x → - (- x) ≡ x
negInvol = ℚRing.solve-∀

invL : ∀ x → - x + x ≡ 0ℚ
invL = ℚRing.solve-∀

invR : ∀ x → x + - x ≡ 0ℚ
invR = ℚRing.solve-∀

jetIdentityLeftRealScalar : ∀ r vx vy vz →
  0ℚ + r + (- (0ℚ * vx + (0ℚ * vy + 0ℚ * vz))) ≡ r
jetIdentityLeftRealScalar r vx vy vz =
  ℚRing.solve (r ∷ vx ∷ vy ∷ vz ∷ [])

jetIdentityRightRealScalar : ∀ r vx vy vz →
  r + 0ℚ + (- (vx * 0ℚ + (vy * 0ℚ + vz * 0ℚ))) ≡ r
jetIdentityRightRealScalar r vx vy vz =
  ℚRing.solve (r ∷ vx ∷ vy ∷ vz ∷ [])

unitDefectMultiplyScalar : ∀ ar ax ay az br bx by bz →
  ((1ℚ + 1ℚ) * (ar + br + (- (ax * bx + (ay * by + az * bz)))) + ((ax + bx) * (ax + bx) + ((ay + by) * (ay + by) + (az + bz) * (az + bz)))) ≡
  (((1ℚ + 1ℚ) * ar + (ax * ax + (ay * ay + az * az))) + ((1ℚ + 1ℚ) * br + (bx * bx + (by * by + bz * bz))))
unitDefectMultiplyScalar ar ax ay az br bx by bz =
  ℚRing.solve (ar ∷ ax ∷ ay ∷ az ∷ br ∷ bx ∷ by ∷ bz ∷ [])

unitDefectInverseScalar : ∀ r vx vy vz →
  ((1ℚ + 1ℚ) * r + ((- vx) * (- vx) + ((- vy) * (- vy) + (- vz) * (- vz)))) ≡
  ((1ℚ + 1ℚ) * r + (vx * vx + (vy * vy + vz * vz)))
unitDefectInverseScalar r vx vy vz =
  ℚRing.solve (r ∷ vx ∷ vy ∷ vz ∷ [])

expDefectZeroScalar : ∀ vx vy vz →
  ((1ℚ + 1ℚ) * (- (half * (vx * vx + (vy * vy + vz * vz)))) + (vx * vx + (vy * vy + vz * vz))) ≡ 0ℚ
expDefectZeroScalar vx vy vz =
  ℚRing.solve (vx ∷ vy ∷ vz ∷ [])

inverseLeftRealScalar : ∀ r vx vy vz →
  (r + r + (- ((- vx) * vx + ((- vy) * vy + (- vz) * vz)))) ≡
  ((1ℚ + 1ℚ) * r + (vx * vx + (vy * vy + vz * vz)))
inverseLeftRealScalar r vx vy vz =
  ℚRing.solve (r ∷ vx ∷ vy ∷ vz ∷ [])

inverseRightRealScalar : ∀ r vx vy vz →
  (r + r + (- (vx * (- vx) + (vy * (- vy) + vz * (- vz))))) ≡
  ((1ℚ + 1ℚ) * r + (vx * vx + (vy * vy + vz * vz)))
inverseRightRealScalar r vx vy vz =
  ℚRing.solve (r ∷ vx ∷ vy ∷ vz ∷ [])

jetIdentityLeft : ∀ path → identityJet *j path ≡ path
jetIdentityLeft (jet r (lie3 vx vy vz)) =
  jetExt
    (jetIdentityLeftRealScalar r vx vy vz)
    (lie3Ext (zeroAddL vx) (zeroAddL vy) (zeroAddL vz))

jetIdentityRight : ∀ path → path *j identityJet ≡ path
jetIdentityRight (jet r (lie3 vx vy vz)) =
  jetExt
    (jetIdentityRightRealScalar r vx vy vz)
    (lie3Ext (zeroAddR vx) (zeroAddR vy) (zeroAddR vz))

inverseJetInvolutive : ∀ path → inverseJet (inverseJet path) ≡ path
inverseJetInvolutive (jet r (lie3 vx vy vz)) =
  jetExt refl
    (lie3Ext (negInvol vx) (negInvol vy) (negInvol vz))

unitDefectIdentity : unitDefect identityJet ≡ 0ℚ
unitDefectIdentity = refl

unitDefectMultiply : ∀ first second →
  unitDefect (first *j second) ≡ unitDefect first + unitDefect second
unitDefectMultiply
  (jet ar (lie3 ax ay az))
  (jet br (lie3 bx by bz)) =
  unitDefectMultiplyScalar ar ax ay az br bx by bz

unitDefectInverse : ∀ path → unitDefect (inverseJet path) ≡ unitDefect path
unitDefectInverse (jet r (lie3 vx vy vz)) =
  unitDefectInverseScalar r vx vy vz

exponentialJetDefectZero : ∀ value → unitDefect (exponentialJet value) ≡ 0ℚ
exponentialJetDefectZero (lie3 vx vy vz) =
  expDefectZeroScalar vx vy vz

jetInverseLeftFromDefect : ∀ path → unitDefect path ≡ 0ℚ →
  inverseJet path *j path ≡ identityJet
jetInverseLeftFromDefect (jet r (lie3 vx vy vz)) defectZero =
  jetExt
    (trans (inverseLeftRealScalar r vx vy vz) defectZero)
    (lie3Ext (invL vx) (invL vy) (invL vz))

jetInverseRightFromDefect : ∀ path → unitDefect path ≡ 0ℚ →
  path *j inverseJet path ≡ identityJet
jetInverseRightFromDefect (jet r (lie3 vx vy vz)) defectZero =
  jetExt
    (trans (inverseRightRealScalar r vx vy vz) defectZero)
    (lie3Ext (invR vx) (invR vy) (invR vz))

open import DASHI.Physics.YangMills.SUNMatrixCarrier

jetMatrixOperations : ComplexMatrixOperations SU2SecondJet ℚ
jetMatrixOperations = record
  { identityM = identityJet
  ; multiplyM = _*j_
  ; daggerM = inverseJet
  ; determinantM = unitDefect
  ; oneC = 0ℚ
  }

jetSpecialFromDefect : ∀ path → unitDefect path ≡ 0ℚ →
  IsSpecialUnitary jetMatrixOperations path
jetSpecialFromDefect path defectZero = record
  { unitaryLeft = jetInverseLeftFromDefect path defectZero
  ; unitaryRight = jetInverseRightFromDefect path defectZero
  ; specialDeterminant = record { determinantOne = defectZero }
  }

twoN : Nat
twoN = suc (suc Nat.zero)

jetSUNTheory : CertifiedSUNMatrixTheory twoN SU2SecondJet ℚ
jetSUNTheory = record
  { operations = jetMatrixOperations
  ; multiplyAssociative = jetMultiplyAssociative
  ; identityLeft = jetIdentityLeft
  ; identityRight = jetIdentityRight
  ; daggerInvolutive = inverseJetInvolutive
  ; identitySpecial = jetSpecialFromDefect identityJet unitDefectIdentity
  ; multiplySpecial = λ {A} {B} specialA specialB →
      let defectAB = trans
            (unitDefectMultiply A B)
            (trans
              (cong₂ _+_
                (IsUnitDeterminant.determinantOne (IsSpecialUnitary.specialDeterminant specialA))
                (IsUnitDeterminant.determinantOne (IsSpecialUnitary.specialDeterminant specialB)))
              (ℚRing.solve-∀))
      in jetSpecialFromDefect (A *j B) defectAB
  ; daggerSpecial = λ {A} specialA →
      jetSpecialFromDefect (inverseJet A)
        (trans (unitDefectInverse A) (IsUnitDeterminant.determinantOne (IsSpecialUnitary.specialDeterminant specialA)))
  }

JetSUN : Set
JetSUN = SUNMatrixElement jetSUNTheory

jetSUNGroup : Group JetSUN
jetSUNGroup = sunMatrixGroup jetSUNTheory

sunExponentialJet : Lie3 → JetSUN
sunExponentialJet value =
  sunMatrix (exponentialJet value)
    (jetSpecialFromDefect (exponentialJet value)
      (exponentialJetDefectZero value))

sunInverseExponentialJet : Lie3 → JetSUN
sunInverseExponentialJet value = sunExponentialJet (negV value)

sunJetMultiplyCommutative : ∀ first second →
  multiply jetSUNGroup first second ≡ multiply jetSUNGroup second first
sunJetMultiplyCommutative first second =
  sunMatrixExt (jetMultiplyCommutative (matrix first) (matrix second))

sunJetConjugateTrivial : ∀ frame value →
  conjugate jetSUNGroup frame value ≡ value
sunJetConjugateTrivial frame value =
  trans
    (cong (λ product → multiply jetSUNGroup product (inverse jetSUNGroup frame))
      (sunJetMultiplyCommutative frame value))
    (rightInverseAction jetSUNGroup frame value)

------------------------------------------------------------------------
-- Scalar second jets and the normalized-real-trace authority.
------------------------------------------------------------------------

record ScalarSecondJet : Set where
  constructor scalarJet
  field
    scalarConstant scalarSecond : ℚ

open ScalarSecondJet public

zeroScalarJet oneScalarJet : ScalarSecondJet
zeroScalarJet = scalarJet 0ℚ 0ℚ
oneScalarJet = scalarJet 1ℚ 0ℚ

addScalarJet subtractScalarJet : ScalarSecondJet → ScalarSecondJet → ScalarSecondJet
addScalarJet (scalarJet ac aq) (scalarJet bc bq) =
  scalarJet (ac + bc) (aq + bq)
subtractScalarJet (scalarJet ac aq) (scalarJet bc bq) =
  scalarJet (ac + (- bc)) (aq + (- bq))

scalarSecondJetOperations : WilsonScalarOperations ScalarSecondJet
scalarSecondJetOperations = record
  { zeroS = zeroScalarJet
  ; oneS = oneScalarJet
  ; addS = addScalarJet
  ; subtractS = subtractScalarJet
  }

normalizedRealTraceSecondJet : JetSUN → ScalarSecondJet
normalizedRealTraceSecondJet element =
  scalarJet 1ℚ (realSecond (matrix element))

jetSUNTraceAuthority :
  SUNWilsonTraceAuthority jetSUNTheory scalarSecondJetOperations
jetSUNTraceAuthority = record
  { normalizedRealTrace = normalizedRealTraceSecondJet
  ; normalizedRealTraceConjugationInvariant = λ frame value →
      cong normalizedRealTraceSecondJet
        (sunJetConjugateTrivial frame value)
  }

scalarSecondDerivative : ScalarSecondJet → ℚ
scalarSecondDerivative path = twoR * scalarSecond path

scalarSecondDerivativeZero : scalarSecondDerivative zeroScalarJet ≡ 0ℚ
scalarSecondDerivativeZero = ℚRing.solve-∀

scalarSecondDerivativeAdd : ∀ left right →
  scalarSecondDerivative (addScalarJet left right)
  ≡ scalarSecondDerivative left + scalarSecondDerivative right
scalarSecondDerivativeAdd (scalarJet lc lq) (scalarJet rc rq) =
  ℚRing.solve-∀

su2SecondJetSUNTheoryLevel : ProofLevel
su2SecondJetSUNTheoryLevel = machineChecked

su2SecondJetTraceAuthorityLevel : ProofLevel
su2SecondJetTraceAuthorityLevel = machineChecked
