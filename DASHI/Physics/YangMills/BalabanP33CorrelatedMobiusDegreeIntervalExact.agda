module DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeIntervalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota, "On the Foundations of Combinatorial Theory I. Theory of
-- Möbius Functions", Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964),
-- 340--368. DOI: 10.1007/BF00531932.
--
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories", Commun. Math.
-- Phys. 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Commun. Math. Phys. 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Marc Daumas, David Lester and César Muñoz, "Verified Real Number
-- Calculations: A Library for Interval Arithmetic", IEEE Trans. Computers 58
-- (2009), 226--237. DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- DASHI CONTRIBUTION
--
-- Consume the exact 4 + 16 Möbius-degree decomposition from Round57 and prove
-- interval transport at the SAME grouped level.  This replaces separate
-- majorisation of 15 raw atoms and 15x15 Green atoms by four raw upper bounds
-- and sixteen joint Green lower bounds.  The remaining physical work is to
-- obtain those 20 bounds from the same selected-background variables,
-- preferably by one affine/Taylor model.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree

------------------------------------------------------------------------
-- Finite-sum monotonicity, proved here rather than assumed from a helper API.
------------------------------------------------------------------------

sumPointwiseUpper : ∀ {A : Set}
  (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  Sums.sumRational values left ≤ Sums.sumRational values right
sumPointwiseUpper [] left right pointwise = ℚP.≤-refl
sumPointwiseUpper (value ∷ values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumPointwiseUpper values left right pointwise)

sumPointwiseLower : ∀ {A : Set}
  (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  Sums.sumRational values left ≤ Sums.sumRational values right
sumPointwiseLower = sumPointwiseUpper

------------------------------------------------------------------------
-- Twenty joint degree envelopes.
------------------------------------------------------------------------

record DegreeRawUpper
    (family : Ownership.CorrelatedResidualFamily)
    (degree : Degree.MobiusDegree) : Set where
  constructor rawUpper
  field
    upper : ℚ
    sound : Degree.rawDegreeBlock family degree ≤ upper
open DegreeRawUpper public

record DegreeGreenLower
    (family : Ownership.CorrelatedResidualFamily)
    (left right : Degree.MobiusDegree) : Set where
  constructor greenLower
  field
    lower : ℚ
    sound : lower ≤ Degree.greenDegreeBlock family left right
open DegreeGreenLower public

record JointDegreeEnvelope
    (family : Ownership.CorrelatedResidualFamily) : Set where
  field
    raw1 : DegreeRawUpper family Degree.degree1
    raw2 : DegreeRawUpper family Degree.degree2
    raw3 : DegreeRawUpper family Degree.degree3
    raw4 : DegreeRawUpper family Degree.degree4

    green11 : DegreeGreenLower family Degree.degree1 Degree.degree1
    green12 : DegreeGreenLower family Degree.degree1 Degree.degree2
    green13 : DegreeGreenLower family Degree.degree1 Degree.degree3
    green14 : DegreeGreenLower family Degree.degree1 Degree.degree4
    green21 : DegreeGreenLower family Degree.degree2 Degree.degree1
    green22 : DegreeGreenLower family Degree.degree2 Degree.degree2
    green23 : DegreeGreenLower family Degree.degree2 Degree.degree3
    green24 : DegreeGreenLower family Degree.degree2 Degree.degree4
    green31 : DegreeGreenLower family Degree.degree3 Degree.degree1
    green32 : DegreeGreenLower family Degree.degree3 Degree.degree2
    green33 : DegreeGreenLower family Degree.degree3 Degree.degree3
    green34 : DegreeGreenLower family Degree.degree3 Degree.degree4
    green41 : DegreeGreenLower family Degree.degree4 Degree.degree1
    green42 : DegreeGreenLower family Degree.degree4 Degree.degree2
    green43 : DegreeGreenLower family Degree.degree4 Degree.degree3
    green44 : DegreeGreenLower family Degree.degree4 Degree.degree4
open JointDegreeEnvelope public

chooseRaw : ∀ {family} → JointDegreeEnvelope family →
  (degree : Degree.MobiusDegree) → DegreeRawUpper family degree
chooseRaw envelope Degree.degree1 = raw1 envelope
chooseRaw envelope Degree.degree2 = raw2 envelope
chooseRaw envelope Degree.degree3 = raw3 envelope
chooseRaw envelope Degree.degree4 = raw4 envelope

chooseGreen : ∀ {family} → JointDegreeEnvelope family →
  (left right : Degree.MobiusDegree) → DegreeGreenLower family left right
chooseGreen envelope Degree.degree1 Degree.degree1 = green11 envelope
chooseGreen envelope Degree.degree1 Degree.degree2 = green12 envelope
chooseGreen envelope Degree.degree1 Degree.degree3 = green13 envelope
chooseGreen envelope Degree.degree1 Degree.degree4 = green14 envelope
chooseGreen envelope Degree.degree2 Degree.degree1 = green21 envelope
chooseGreen envelope Degree.degree2 Degree.degree2 = green22 envelope
chooseGreen envelope Degree.degree2 Degree.degree3 = green23 envelope
chooseGreen envelope Degree.degree2 Degree.degree4 = green24 envelope
chooseGreen envelope Degree.degree3 Degree.degree1 = green31 envelope
chooseGreen envelope Degree.degree3 Degree.degree2 = green32 envelope
chooseGreen envelope Degree.degree3 Degree.degree3 = green33 envelope
chooseGreen envelope Degree.degree3 Degree.degree4 = green34 envelope
chooseGreen envelope Degree.degree4 Degree.degree1 = green41 envelope
chooseGreen envelope Degree.degree4 Degree.degree2 = green42 envelope
chooseGreen envelope Degree.degree4 Degree.degree3 = green43 envelope
chooseGreen envelope Degree.degree4 Degree.degree4 = green44 envelope

rawUpperValue : ∀ {family} → JointDegreeEnvelope family →
  Degree.MobiusDegree → ℚ
rawUpperValue envelope degree = upper (chooseRaw envelope degree)

greenLowerValue : ∀ {family} → JointDegreeEnvelope family →
  Degree.MobiusDegree → Degree.MobiusDegree → ℚ
greenLowerValue envelope left right = lower (chooseGreen envelope left right)

rawUpperTotal : ∀ {family} → JointDegreeEnvelope family → ℚ
rawUpperTotal envelope =
  Sums.sumRational Degree.allDegrees (rawUpperValue envelope)

greenLowerRow : ∀ {family} → JointDegreeEnvelope family →
  Degree.MobiusDegree → ℚ
greenLowerRow envelope left =
  Sums.sumRational Degree.allDegrees (greenLowerValue envelope left)

greenLowerTotal : ∀ {family} → JointDegreeEnvelope family → ℚ
greenLowerTotal envelope =
  Sums.sumRational Degree.allDegrees (greenLowerRow envelope)

rawDegreeTotalUpper : ∀ {family}
  (envelope : JointDegreeEnvelope family) →
  Degree.rawDegreeTotal family ≤ rawUpperTotal envelope
rawDegreeTotalUpper envelope =
  sumPointwiseUpper
    Degree.allDegrees
    (Degree.rawDegreeBlock _)
    (rawUpperValue envelope)
    (λ degree → sound (chooseRaw envelope degree))

greenRowLower : ∀ {family}
  (envelope : JointDegreeEnvelope family)
  (left : Degree.MobiusDegree) →
  greenLowerRow envelope left ≤ Degree.greenDegreeRow family left
greenRowLower envelope left =
  sumPointwiseLower
    Degree.allDegrees
    (greenLowerValue envelope left)
    (Degree.greenDegreeBlock _ left)
    (λ right → sound (chooseGreen envelope left right))

greenDegreeTotalLower : ∀ {family}
  (envelope : JointDegreeEnvelope family) →
  greenLowerTotal envelope ≤ Degree.greenDegreeTotal family
greenDegreeTotalLower envelope =
  sumPointwiseLower
    Degree.allDegrees
    (greenLowerRow envelope)
    (Degree.greenDegreeRow _)
    (greenRowLower envelope)

correlatedResidualJointDegreeUpper : ∀ {family}
  (envelope : JointDegreeEnvelope family) →
  Ownership.correlatedResidualTotal family
  ≤ rawUpperTotal envelope - greenLowerTotal envelope
correlatedResidualJointDegreeUpper {family} envelope =
  let
    rawBound = rawDegreeTotalUpper envelope
    greenBound = greenDegreeTotalLower envelope
    differenceBound :
      Degree.rawDegreeTotal family - Degree.greenDegreeTotal family
      ≤ rawUpperTotal envelope - greenLowerTotal envelope
    differenceBound =
      ℚP.+-mono-≤ rawBound (ℚP.neg-mono-≤ greenBound)
  in
  subst
    (λ actual → actual ≤ rawUpperTotal envelope - greenLowerTotal envelope)
    (sym (Degree.correlatedResidualIsJointDegreeExpression family))
    differenceBound

mobiusDegreeJointIntervalTransportLevel : ProofLevel
mobiusDegreeJointIntervalTransportLevel = machineChecked

-- Physical/numerical leaf: construct the 20 grouped bounds from the SAME
-- selected-background variables and verify the final tiny endpoint ratio.
selectedRegionDegreeEnvelopeProducerLevel : ProofLevel
selectedRegionDegreeEnvelopeProducerLevel = conditional
