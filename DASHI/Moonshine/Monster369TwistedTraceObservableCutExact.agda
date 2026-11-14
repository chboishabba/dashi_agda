module DASHI.Moonshine.Monster369TwistedTraceObservableCutExact where

-- SOURCE CREDIT:
-- Lin--Shao, Duality Defect of the Monster CFT, arXiv:1911.00042:
--   T_2A = q^-1 + 4372 q + ...; T_2B = q^-1 + 276 q + ... .
-- FLM/Borcherds: J = q^-1 + 196884 q + ... .
-- ATLAS of finite groups: Monster 27A and 27B, both power to 3B.
-- Carnahan, Generalized Moonshine IV, completed generalized
-- moonshine (twisted/twining modular covariance and root of unity phases).
-- Their established CFT mathematics is NOT an AdS3 gravity dual.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos; []; _∷_)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Moonshine.JCoefficientCharacterBridge as Character
import DASHI.Moonshine.JInvariant369BraidModularTernaryTowerExact as Braid
import DASHI.Moonshine.TwistedModuleModularity as Twisted

-- Reuse the actual preexisting first character coefficient theorem.
firstMonsterCoefficient :
  196884 ≡ 1 + 196883
firstMonsterCoefficient = Character.firstCoefficientArithmetic

weightTwoUntwisted : Nat
weightTwoUntwisted = 196884

weightTwoTwoATwined : Nat
weightTwoTwoATwined = 4372

weightTwoTwoBTwined : Nat
weightTwoTwoBTwined = 276

twoAPlusTwoAminus : Nat
twoAPlusTwoAminus = 100628
twoAMinus : Nat
twoAMinus = 96256

twoBPlusTwoBminus : Nat
twoBPlusTwoBminus = 98580
twoBMinus : Nat
twoBMinus = 98304

twoASectorSum :
  twoAPlusTwoAminus + twoAMinus ≡ weightTwoUntwisted
twoASectorSum = refl

twoAChargeTrace :
  twoAPlusTwoAminus ≡ twoAMinus + weightTwoTwoATwined
twoAChargeTrace = refl

twoBSectorSum :
  twoBPlusTwoBminus + twoBMinus ≡ weightTwoUntwisted
twoBSectorSum = refl

twoBChargeTrace :
  twoBPlusTwoBminus ≡ twoBMinus + weightTwoTwoBTwined
twoBChargeTrace = refl

differentPhysicalMoonshineTwiningCoefficients :
  weightTwoTwoATwined ≡ weightTwoTwoBTwined → ⊥
differentPhysicalMoonshineTwiningCoefficients ()

-- Exact literal 27-cusp coordinates of one order-27 Monster twist
-- and the braid transport M=(T^-1 U)^3. These are only power labels
-- for an ACTUAL order-27 Monster element supplied from ATLAS:
-- (g,1) -> (g^13,g^-8)=(g^13,g^19).
one27 : Q.Residue3Pow 3
one27 = pos ∷ zer ∷ zer ∷ []

zero27 : Q.Residue3Pow 3
zero27 = Arithmetic.zeroResidue 3

thirteen27 : Q.Residue3Pow 3
thirteen27 = pos ∷ pos ∷ pos ∷ []

minusEight27 : Q.Residue3Pow 3
minusEight27 = pos ∷ zer ∷ neg ∷ []

initial27 : Braid.ModularVectorAt 3
initial27 = Braid.modular-vector one27 zero27

transported27 : Braid.ModularVectorAt 3
transported27 = Braid.braidWord initial27

transportedIs13AndMinus8 :
  transported27 ≡ Braid.modular-vector thirteen27 minusEight27
transportedIs13AndMinus8 = refl

transportedTwistPairIsNotOriginal :
  transported27 ≡ initial27 → ⊥
transportedTwistPairIsNotOriginal ()

-- A real twisted VOA signal is additional data; no code/grade/matrix
-- coincidence supplies it. A producer must supply source-certified
-- traces on precisely these order-27 Monster twisted sectors and
-- prove the marked-boundary normalized observables distinguish them.
record ConcreteMonster27TraceDiscriminator
    (Trace : Set)
    (CertifiedMonsterTrace :
      Braid.ModularVectorAt 3 → Trace → Set) : Set₁ where
  field
    trace : Braid.ModularVectorAt 3 → Trace
    certified : (p : Braid.ModularVectorAt 3) →
      CertifiedMonsterTrace p (trace p)
    braidSeparatesTrace :
      trace transported27 ≡ trace initial27 → ⊥

-- The repository's existing TwistedModuleModularity and ConwayNorton
-- owners must supply CertifiedMonsterTrace with the actual V^natural
-- twisted sector, commuting group element, modular multiplier and
-- conformal grading. A bare sector-label witness is insufficient.
-- The physical AdS3 dual additionally requires a bulk defect observable.
