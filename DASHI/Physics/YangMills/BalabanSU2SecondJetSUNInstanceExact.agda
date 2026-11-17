module DASHI.Physics.YangMills.BalabanSU2SecondJetSUNInstanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.CompactLieGroupCore using (Group; multiply; inverse)
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

assocQ : ∀ a b c → (a + b) + c ≡ a + (b + c)
assocQ = ℚRing.solve-∀

commQ : ∀ a b → a + b ≡ b + a
commQ = ℚRing.solve-∀

twoScaleAddRaw : ∀ lq rq → twoR * (lq + rq) ≡ twoR * lq + twoR * rq
twoScaleAddRaw = ℚRing.solve-∀

pairSum2 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
pairSum2 = ℚRing.solve-∀

pairSum3 : ∀ x1 y1 z1 x2 y2 z2 →
  (x1 + (y1 + z1)) + (x2 + (y2 + z2)) ≡ (x1 + x2) + ((y1 + y2) + (z1 + z2))
pairSum3 x1 y1 z1 x2 y2 z2 =
  trans
    (pairSum2 x1 (y1 + z1) x2 (y2 + z2))
    (cong (λ r → (x1 + x2) + r) (pairSum2 y1 z1 y2 z2))

dotAssoc1D : ∀ a b c → a * b + (a + b) * c ≡ b * c + a * (b + c)
dotAssoc1D = ℚRing.solve-∀

dotAssocV : ∀ (a b c : Lie3) →
  (a ·v b) + ((a +v b) ·v c) ≡ (b ·v c) + (a ·v (b +v c))
dotAssocV (lie3 ax ay az) (lie3 bx by bz) (lie3 cx cy cz) =
  trans
    (pairSum3 (ax * bx) (ay * by) (az * bz) ((ax + bx) * cx) ((ay + by) * cy) ((az + bz) * cz))
    (trans
      (cong₂ _+_
        (dotAssoc1D ax bx cx)
        (cong₂ _+_ (dotAssoc1D ay by cy) (dotAssoc1D az bz cz)))
      (sym (pairSum3 (bx * cx) (by * cy) (bz * cz) (ax * (bx + cx)) (ay * (by + cy)) (az * (bz + cz)))))

realAssocStepL : ∀ ar br cr u v →
  ((ar + br + (- u)) + cr + (- v)) ≡ (ar + br + cr) + (- (u + v))
realAssocStepL = ℚRing.solve-∀

realAssocStepR : ∀ ar br cr w t →
  (ar + br + cr) + (- (w + t)) ≡ (ar + (br + cr + (- w)) + (- t))
realAssocStepR = ℚRing.solve-∀

dotComm1D : ∀ a b → a * b ≡ b * a
dotComm1D = ℚRing.solve-∀

dotCommV : ∀ (a b : Lie3) → (a ·v b) ≡ (b ·v a)
dotCommV (lie3 ax ay az) (lie3 bx by bz) =
  cong₂ _+_ (dotComm1D ax bx) (cong₂ _+_ (dotComm1D ay by) (dotComm1D az bz))

realCommStep : ∀ ar br d → ar + br + (- d) ≡ br + ar + (- d)
realCommStep = ℚRing.solve-∀

jetMultiplyAssociative : ∀ first second third →
  (first *j second) *j third ≡ first *j (second *j third)
jetMultiplyAssociative
  (jet ar (lie3 ax ay az))
  (jet br (lie3 bx by bz))
  (jet cr (lie3 cx cy cz)) =
  let
    a = lie3 ax ay az
    b = lie3 bx by bz
    c = lie3 cx cy cz
  in
  jetExt
    (trans
      (realAssocStepL ar br cr (a ·v b) ((a +v b) ·v c))
      (trans
        (cong (λ d → (ar + br + cr) + (- d)) (dotAssocV a b c))
        (realAssocStepR ar br cr (b ·v c) (a ·v (b +v c)))))
    (lie3Ext
      (assocQ ax bx cx)
      (assocQ ay by cy)
      (assocQ az bz cz))

jetMultiplyCommutative : ∀ first second → first *j second ≡ second *j first
jetMultiplyCommutative
  (jet ar (lie3 ax ay az))
  (jet br (lie3 bx by bz)) =
  let
    a = lie3 ax ay az
    b = lie3 bx by bz
  in
  jetExt
    (trans
      (realCommStep ar br (a ·v b))
      (cong (λ d → br + ar + (- d)) (dotCommV a b)))
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
jetIdentityLeftRealScalar = ℚRing.solve-∀

jetIdentityRightRealScalar : ∀ r vx vy vz →
  r + 0ℚ + (- (vx * 0ℚ + (vy * 0ℚ + vz * 0ℚ))) ≡ r
jetIdentityRightRealScalar = ℚRing.solve-∀

normSqAdd1D : ∀ a b → (a + b) * (a + b) ≡ (a * a + b * b) + twoR * (a * b)
normSqAdd1D = ℚRing.solve-∀

normSqAddV : ∀ (a b : Lie3) →
  normSqV (a +v b) ≡ (normSqV a + normSqV b) + twoR * (a ·v b)
normSqAddV (lie3 ax ay az) (lie3 bx by bz) =
  trans
    (cong₂ _+_ (normSqAdd1D ax bx)
      (trans
        (cong₂ _+_ (normSqAdd1D ay by) (normSqAdd1D az bz))
        (trans
          (pairSum2 (ay * ay + by * by) (twoR * (ay * by)) (az * az + bz * bz) (twoR * (az * bz)))
          (cong₂ _+_
            (pairSum2 (ay * ay) (by * by) (az * az) (bz * bz))
            (sym (twoScaleAddRaw (ay * by) (az * bz)))))))
    (trans
      (pairSum2 (ax * ax + bx * bx) (twoR * (ax * bx))
        ((ay * ay + az * az) + (by * by + bz * bz))
        (twoR * (ay * by + az * bz)))
      (cong₂ _+_
        (pairSum2 (ax * ax) (bx * bx) (ay * ay + az * az) (by * by + bz * bz))
        (sym (twoScaleAddRaw (ax * bx) (ay * by + az * bz)))))

unitDefectFromNormSqAdd : ∀ ar br na nb d →
  twoR * (ar + br + (- d)) + ((na + nb) + twoR * d)
  ≡ (twoR * ar + na) + (twoR * br + nb)
unitDefectFromNormSqAdd = ℚRing.solve-∀

unitDefectInverseScalar : ∀ r vx vy vz →
  ((1ℚ + 1ℚ) * r + ((- vx) * (- vx) + ((- vy) * (- vy) + (- vz) * (- vz)))) ≡
  ((1ℚ + 1ℚ) * r + (vx * vx + (vy * vy + vz * vz)))
unitDefectInverseScalar = ℚRing.solve-∀

expDefectZeroScalar : ∀ vx vy vz →
  ((1ℚ + 1ℚ) * (- (half * (vx * vx + (vy * vy + vz * vz)))) + (vx * vx + (vy * vy + vz * vz))) ≡ 0ℚ
expDefectZeroScalar = ℚRing.solve-∀

inverseLeftRealScalar : ∀ r vx vy vz →
  (r + r + (- ((- vx) * vx + ((- vy) * vy + (- vz) * vz)))) ≡
  ((1ℚ + 1ℚ) * r + (vx * vx + (vy * vy + vz * vz)))
inverseLeftRealScalar = ℚRing.solve-∀

inverseRightRealScalar : ∀ r vx vy vz →
  (r + r + (- (vx * (- vx) + (vy * (- vy) + vz * (- vz))))) ≡
  ((1ℚ + 1ℚ) * r + (vx * vx + (vy * vy + vz * vz)))
inverseRightRealScalar = ℚRing.solve-∀

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
  (jet ar a)
  (jet br b) =
  trans
    (cong (λ n → twoR * (ar + br + (- (a ·v b))) + n) (normSqAddV a b))
    (unitDefectFromNormSqAdd ar br (normSqV a) (normSqV b) (a ·v b))

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
  ; determinant = unitDefect
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
twoN = suc (suc zero)

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
            (cong₂ _+_
              (IsUnitDeterminant.determinantOne (IsSpecialUnitary.specialDeterminant specialA))
              (IsUnitDeterminant.determinantOne (IsSpecialUnitary.specialDeterminant specialB)))
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

inverseExponentialJetDefectZero : ∀ value →
  unitDefect (inverseExponentialJet value) ≡ 0ℚ
inverseExponentialJetDefectZero (lie3 vx vy vz) =
  trans
    (unitDefectInverseScalar (- (half * (vx * vx + (vy * vy + vz * vz)))) vx vy vz)
    (expDefectZeroScalar vx vy vz)

sunInverseExponentialJet : Lie3 → JetSUN
sunInverseExponentialJet value =
  sunMatrix (inverseExponentialJet value)
    (jetSpecialFromDefect (inverseExponentialJet value)
      (inverseExponentialJetDefectZero value))

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
  SUNWilsonTraceAuthority {Scalar = ScalarSecondJet} jetSUNTheory
jetSUNTraceAuthority = record
  { normalizedRealTrace = normalizedRealTraceSecondJet
  ; traceConjugationInvariant = λ frame value →
      cong normalizedRealTraceSecondJet
        (sunJetConjugateTrivial frame value)
  }

scalarSecondDerivative : ScalarSecondJet → ℚ
scalarSecondDerivative path = twoR * scalarSecond path

scalarSecondDerivativeZero : scalarSecondDerivative zeroScalarJet ≡ 0ℚ
scalarSecondDerivativeZero = refl

scalarSecondDerivativeAdd : ∀ left right →
  scalarSecondDerivative (addScalarJet left right)
  ≡ scalarSecondDerivative left + scalarSecondDerivative right
scalarSecondDerivativeAdd (scalarJet lc lq) (scalarJet rc rq) =
  twoScaleAddRaw lq rq

su2SecondJetSUNTheoryLevel : ProofLevel
su2SecondJetSUNTheoryLevel = machineChecked

su2SecondJetTraceAuthorityLevel : ProofLevel
su2SecondJetTraceAuthorityLevel = machineChecked
