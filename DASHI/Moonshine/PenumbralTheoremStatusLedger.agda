module DASHI.Moonshine.PenumbralTheoremStatusLedger where

-- Status ledger for the principal penumbral statements.  Established theorems
-- carry inhabitants.  Conditional statements carry their hypotheses and
-- implication.  Conjectures carry only a formulation and provenance witness.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (⊤; tt)

data ClaimStatus : Set where
  established : ClaimStatus
  conditional : ClaimStatus
  conjectural : ClaimStatus

record EstablishedClaim : Setω where
  field
    Statement : Set
    proof : Statement
    SourceAuthority : Set
    sourceAuthority : SourceAuthority

record ConditionalClaim : Setω where
  field
    Hypothesis : Set
    Conclusion : Set
    derivation : Hypothesis → Conclusion
    SourceAuthority : Set
    sourceAuthority : SourceAuthority

record ConjecturalClaim : Setω where
  field
    Statement : Set
    SourceAuthority : Set
    sourceAuthority : SourceAuthority
    NoGeneralProofClaim : Set
    noGeneralProofClaim : NoGeneralProofClaim

record PenumbralFamilyExistenceTheorems : Setω where
  field
    LambdencyDatum : Set
    Admissible : LambdencyDatum → Set
    DiscriminantMinusThree : LambdencyDatum → Set
    DiscriminantMinusFour : LambdencyDatum → Set
    VirtualGradedModuleExists : LambdencyDatum → Set

    minusThreeExistence :
      (lambda : LambdencyDatum) →
      Admissible lambda →
      DiscriminantMinusThree lambda →
      VirtualGradedModuleExists lambda

    minusFourExistence :
      (lambda : LambdencyDatum) →
      Admissible lambda →
      DiscriminantMinusFour lambda →
      VirtualGradedModuleExists lambda

record PenumbralConstructionTheorems : Setω where
  field
    RationalHalfWeightModule : Set
    WeightZeroModule : Set
    PositiveIndex : RationalHalfWeightModule → Set
    WeaklyHolomorphic : RationalHalfWeightModule → Set
    SQOf : RationalHalfWeightModule → WeightZeroModule → Set

    constructSQ :
      (module : RationalHalfWeightModule) →
      PositiveIndex module →
      WeaklyHolomorphic module →
      WeightZeroModule

    sqCorrect :
      (module : RationalHalfWeightModule) →
      (positive : PositiveIndex module) →
      (weak : WeaklyHolomorphic module) →
      SQOf module (constructSQ module positive weak)

record ThompsonAvatarTheorems : Setω where
  field
    ClassicalHalfWeight GeneralizedWeightZero : Set
    PenumbralHalfWeight PenumbralWeightZero : Set

    BorcherdsFromClassical :
      ClassicalHalfWeight → GeneralizedWeightZero → Set
    BorcherdsFromPenumbral :
      PenumbralHalfWeight → PenumbralWeightZero → Set
    SingularModuliFromGeneralized :
      GeneralizedWeightZero → PenumbralHalfWeight → Set
    SingularModuliFromPenumbral :
      PenumbralWeightZero → ClassicalHalfWeight → Set

    classicalHalf : ClassicalHalfWeight
    generalizedZero : GeneralizedWeightZero
    penumbralHalf : PenumbralHalfWeight
    penumbralZero : PenumbralWeightZero

    classicalBorcherds :
      BorcherdsFromClassical classicalHalf generalizedZero
    penumbralBorcherds :
      BorcherdsFromPenumbral penumbralHalf penumbralZero
    generalizedSingularModuli :
      SingularModuliFromGeneralized generalizedZero penumbralHalf
    penumbralSingularModuli :
      SingularModuliFromPenumbral penumbralZero classicalHalf

record PenumbralStatusLedger : Setω where
  field
    familyExistence : PenumbralFamilyExistenceTheorems
    sqConstruction : PenumbralConstructionTheorems
    thompsonAvatars : ThompsonAvatarTheorems
    discriminantFieldProperty : ConjecturalClaim

    familyExistenceStatus : ClaimStatus
    sqConstructionStatus : ClaimStatus
    thompsonAvatarStatus : ClaimStatus
    discriminantFieldStatus : ClaimStatus

    familyExistenceIsEstablished :
      familyExistenceStatus ≡ established
    sqConstructionIsEstablished :
      sqConstructionStatus ≡ established
    thompsonAvatarsAreEstablished :
      thompsonAvatarStatus ≡ established
    discriminantFieldIsConjectural :
      discriminantFieldStatus ≡ conjectural

record PenumbralStatusBoundary : Set where
  field
    establishedClaimsCarryProofs : ⊤
    conditionalClaimsCarryHypotheses : ⊤
    conjecturalClaimsCarryNoGeneralProof : ⊤
    minusThreeAndMinusFourExistenceTrackedSeparately : ⊤
    discriminantFieldPropertyNotPromoted : ⊤

penumbralStatusBoundary : PenumbralStatusBoundary
penumbralStatusBoundary = record
  { establishedClaimsCarryProofs = tt
  ; conditionalClaimsCarryHypotheses = tt
  ; conjecturalClaimsCarryNoGeneralProof = tt
  ; minusThreeAndMinusFourExistenceTrackedSeparately = tt
  ; discriminantFieldPropertyNotPromoted = tt
  }
