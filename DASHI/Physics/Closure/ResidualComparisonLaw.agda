module DASHI.Physics.Closure.ResidualComparisonLaw where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Properties as NatP using (_≤?_)
open import Relation.Nullary.Decidable.Core using (yes; no)

------------------------------------------------------------------------
-- Universal residual comparison vocabulary.
--
-- This surface names the fail-closed outcomes shared by empirical residual
-- comparison lanes.  It deliberately keeps the numeric classifier finite and
-- Nat-shaped: providers may bind richer integer/rational payloads outside
-- this module, then enter through an Agda-friendly scaled sigma magnitude.

data UniversalResidualComparisonOutcome : Set where
  acceptedResidualCandidate :
    UniversalResidualComparisonOutcome
  borderlineCandidate :
    UniversalResidualComparisonOutcome
  rejectedResidualCandidate :
    UniversalResidualComparisonOutcome
  insufficientAuthority :
    UniversalResidualComparisonOutcome
  theoryUncertaintyDominates :
    UniversalResidualComparisonOutcome
  freezeMissing :
    UniversalResidualComparisonOutcome
  dataMissing :
    UniversalResidualComparisonOutcome

canonicalUniversalResidualComparisonOutcomes :
  List UniversalResidualComparisonOutcome
canonicalUniversalResidualComparisonOutcomes =
  acceptedResidualCandidate
  ∷ borderlineCandidate
  ∷ rejectedResidualCandidate
  ∷ insufficientAuthority
  ∷ theoryUncertaintyDominates
  ∷ freezeMissing
  ∷ dataMissing
  ∷ []

data SigmaBand : Set where
  sigmaAtMostTwo :
    SigmaBand
  sigmaAtMostThree :
    SigmaBand
  sigmaAboveThree :
    SigmaBand

canonicalSigmaBands :
  List SigmaBand
canonicalSigmaBands =
  sigmaAtMostTwo
  ∷ sigmaAtMostThree
  ∷ sigmaAboveThree
  ∷ []

one two three ten twenty thirty : Nat
one =
  suc zero
two =
  suc one
three =
  suc two
ten =
  suc (suc (suc (suc (suc (suc (suc (suc (suc one))))))))
twenty =
  ten + ten
thirty =
  twenty + ten

classifyIntegerSigmaBand :
  Nat →
  SigmaBand
classifyIntegerSigmaBand sigma with sigma NatP.≤? two
... | yes _ =
  sigmaAtMostTwo
... | no _ with sigma NatP.≤? three
...   | yes _ =
  sigmaAtMostThree
...   | no _ =
  sigmaAboveThree

sigmaBandOutcome :
  SigmaBand →
  UniversalResidualComparisonOutcome
sigmaBandOutcome sigmaAtMostTwo =
  acceptedResidualCandidate
sigmaBandOutcome sigmaAtMostThree =
  borderlineCandidate
sigmaBandOutcome sigmaAboveThree =
  rejectedResidualCandidate

classifyIntegerSigmaOutcome :
  Nat →
  UniversalResidualComparisonOutcome
classifyIntegerSigmaOutcome sigma =
  sigmaBandOutcome (classifyIntegerSigmaBand sigma)

record ScaledSigmaMagnitude : Set where
  constructor mkScaledSigmaMagnitude
  field
    numerator :
      Nat

    denominator :
      Nat

open ScaledSigmaMagnitude public

data CanonicalSigmaScale : Set where
  integerSigmaScale :
    CanonicalSigmaScale
  tenthSigmaScale :
    CanonicalSigmaScale

scaleDenominator :
  CanonicalSigmaScale →
  Nat
scaleDenominator integerSigmaScale =
  suc zero
scaleDenominator tenthSigmaScale =
  ten

integerSigmaMagnitude :
  Nat →
  ScaledSigmaMagnitude
integerSigmaMagnitude sigma =
  mkScaledSigmaMagnitude sigma (scaleDenominator integerSigmaScale)

tenthSigmaMagnitude :
  Nat →
  ScaledSigmaMagnitude
tenthSigmaMagnitude sigmaTenths =
  mkScaledSigmaMagnitude sigmaTenths (scaleDenominator tenthSigmaScale)

classifyTenthSigmaBand :
  Nat →
  SigmaBand
classifyTenthSigmaBand sigmaTenths with sigmaTenths NatP.≤? twenty
... | yes _ =
  sigmaAtMostTwo
... | no _ with sigmaTenths NatP.≤? thirty
...   | yes _ =
  sigmaAtMostThree
...   | no _ =
  sigmaAboveThree

classifyTenthSigmaOutcome :
  Nat →
  UniversalResidualComparisonOutcome
classifyTenthSigmaOutcome sigmaTenths =
  sigmaBandOutcome (classifyTenthSigmaBand sigmaTenths)

data ResidualAuthorityState : Set where
  authorityPresent :
    ResidualAuthorityState
  authorityMissing :
    ResidualAuthorityState

data ResidualFreezeState : Set where
  freezePresent :
    ResidualFreezeState
  freezeAbsent :
    ResidualFreezeState

data ResidualDataState : Set where
  dataPresent :
    ResidualDataState
  dataAbsent :
    ResidualDataState

data ResidualTheoryUncertaintyState : Set where
  theoryUncertaintyControlled :
    ResidualTheoryUncertaintyState
  theoryUncertaintyDominant :
    ResidualTheoryUncertaintyState

classifyResidualCandidate :
  ResidualAuthorityState →
  ResidualFreezeState →
  ResidualDataState →
  ResidualTheoryUncertaintyState →
  SigmaBand →
  UniversalResidualComparisonOutcome
classifyResidualCandidate authorityMissing _ _ _ _ =
  insufficientAuthority
classifyResidualCandidate authorityPresent freezeAbsent _ _ _ =
  freezeMissing
classifyResidualCandidate authorityPresent freezePresent dataAbsent _ _ =
  dataMissing
classifyResidualCandidate
  authorityPresent
  freezePresent
  dataPresent
  theoryUncertaintyDominant
  _ =
  theoryUncertaintyDominates
classifyResidualCandidate
  authorityPresent
  freezePresent
  dataPresent
  theoryUncertaintyControlled
  band =
  sigmaBandOutcome band

classifyIntegerResidualCandidate :
  ResidualAuthorityState →
  ResidualFreezeState →
  ResidualDataState →
  ResidualTheoryUncertaintyState →
  Nat →
  UniversalResidualComparisonOutcome
classifyIntegerResidualCandidate authority freeze dataState theory sigma =
  classifyResidualCandidate
    authority
    freeze
    dataState
    theory
    (classifyIntegerSigmaBand sigma)

authorityMissingPrecedesDataMissing :
  (freeze : ResidualFreezeState) →
  (dataState : ResidualDataState) →
  (theory : ResidualTheoryUncertaintyState) →
  (band : SigmaBand) →
  classifyResidualCandidate authorityMissing freeze dataState theory band
  ≡
  insufficientAuthority
authorityMissingPrecedesDataMissing _ _ _ _ =
  refl

freezeMissingPrecedesDataMissing :
  (dataState : ResidualDataState) →
  (theory : ResidualTheoryUncertaintyState) →
  (band : SigmaBand) →
  classifyResidualCandidate authorityPresent freezeAbsent dataState theory band
  ≡
  freezeMissing
freezeMissingPrecedesDataMissing _ _ _ =
  refl

dataMissingPrecedesTheoryDominance :
  (theory : ResidualTheoryUncertaintyState) →
  (band : SigmaBand) →
  classifyResidualCandidate authorityPresent freezePresent dataAbsent theory band
  ≡
  dataMissing
dataMissingPrecedesTheoryDominance _ _ =
  refl

integerSigmaTwoAccepted :
  classifyIntegerSigmaOutcome (suc (suc zero))
  ≡
  acceptedResidualCandidate
integerSigmaTwoAccepted =
  refl

integerSigmaThreeBorderline :
  classifyIntegerSigmaOutcome (suc (suc (suc zero)))
  ≡
  borderlineCandidate
integerSigmaThreeBorderline =
  refl

integerSigmaFourRejected :
  classifyIntegerSigmaOutcome (suc (suc (suc (suc zero))))
  ≡
  rejectedResidualCandidate
integerSigmaFourRejected =
  refl

canonicalUniversalResidualComparisonBoundary :
  List String
canonicalUniversalResidualComparisonBoundary =
  "Authority missing has precedence over freeze, data, theory, and sigma-band outcomes"
  ∷ "Freeze missing has precedence after authority is present"
  ∷ "Data missing has precedence after authority and freeze are present"
  ∷ "Theory uncertainty dominance has precedence before sigma-band acceptance"
  ∷ "Sigma bands classify <=2 as accepted, <=3 as borderline, and >3 as rejected"
  ∷ []
