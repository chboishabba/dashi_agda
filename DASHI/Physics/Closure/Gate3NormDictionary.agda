module DASHI.Physics.Closure.Gate3NormDictionary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; _+_; _*_; _^_; _∸_; _≤ᵇ_)

open import MonsterOntos using
  ( SSP
  ; toNat
  ; p2
  ; p3
  ; p5
  ; p7
  ; p11
  ; p13
  ; p17
  ; p19
  ; p23
  ; p29
  ; p31
  ; p41
  ; p47
  ; p59
  ; p71
  )
import Ontology.GodelLattice as GL
import Ontology.Hecke.Scan as HScan
import DASHI.Physics.Closure.MultiPrimePAdicCarrierCoordinate as MP

------------------------------------------------------------------------
-- Gate 3 norm dictionary.
--
-- This module gives the concrete finite carrier dictionary needed by the
-- Gate 3 adelic Sobolev proof obligation.  It deliberately records p-adic
-- quantities as rational numerator/denominator data, because p^{-v} and
-- p^{-2v} are not natural numbers.  No adelic Plancherel theorem, Sobolev
-- inequality, physical theorem, or Clay promotion is proved here.

data Gate3NormDictionaryStatus : Set where
  normDictionaryComputable_analyticInequalityStillExternal :
    Gate3NormDictionaryStatus

data BoundedModelLimit71Status : Set where
  finiteBoundedModelLimit71InequalitySurface_only :
    BoundedModelLimit71Status

data BoundedModelFiniteSetStatus : Set where
  compactFiniteSSPSet_limit71 :
    BoundedModelFiniteSetStatus

record PositiveRationalCode : Set where
  constructor frac
  field
    numerator :
      ℕ

    denominator :
      ℕ

open PositiveRationalCode public

one : ℕ
one = 1

two : ℕ
two = 2

fifteen : ℕ
fifteen = 15

limit71 :
  ℕ
limit71 = toNat p71

finiteSSP :
  List SSP
finiteSSP =
  p2
  ∷ p3
  ∷ p5
  ∷ p7
  ∷ p11
  ∷ p13
  ∷ p17
  ∷ p19
  ∷ p23
  ∷ p29
  ∷ p31
  ∷ p41
  ∷ p47
  ∷ p59
  ∷ p71
  ∷ []

lookupExponent :
  SSP →
  GL.FactorVec →
  GL.Exponent
lookupExponent p2  (GL.v15 e2  _   _   _   _   _   _   _   _   _   _   _   _   _   _  ) = e2
lookupExponent p3  (GL.v15 _   e3  _   _   _   _   _   _   _   _   _   _   _   _   _  ) = e3
lookupExponent p5  (GL.v15 _   _   e5  _   _   _   _   _   _   _   _   _   _   _   _  ) = e5
lookupExponent p7  (GL.v15 _   _   _   e7  _   _   _   _   _   _   _   _   _   _   _  ) = e7
lookupExponent p11 (GL.v15 _   _   _   _   e11 _   _   _   _   _   _   _   _   _   _  ) = e11
lookupExponent p13 (GL.v15 _   _   _   _   _   e13 _   _   _   _   _   _   _   _   _  ) = e13
lookupExponent p17 (GL.v15 _   _   _   _   _   _   e17 _   _   _   _   _   _   _   _  ) = e17
lookupExponent p19 (GL.v15 _   _   _   _   _   _   _   e19 _   _   _   _   _   _   _  ) = e19
lookupExponent p23 (GL.v15 _   _   _   _   _   _   _   _   e23 _   _   _   _   _   _  ) = e23
lookupExponent p29 (GL.v15 _   _   _   _   _   _   _   _   _   e29 _   _   _   _   _  ) = e29
lookupExponent p31 (GL.v15 _   _   _   _   _   _   _   _   _   _   e31 _   _   _   _  ) = e31
lookupExponent p41 (GL.v15 _   _   _   _   _   _   _   _   _   _   _   e41 _   _   _  ) = e41
lookupExponent p47 (GL.v15 _   _   _   _   _   _   _   _   _   _   _   _   e47 _   _  ) = e47
lookupExponent p59 (GL.v15 _   _   _   _   _   _   _   _   _   _   _   _   _   e59 _  ) = e59
lookupExponent p71 (GL.v15 _   _   _   _   _   _   _   _   _   _   _   _   _   _   e71) = e71

pAdicCarrierNorm :
  SSP →
  GL.FactorVec →
  PositiveRationalCode
pAdicCarrierNorm p v =
  frac one ((toNat p) ^ (two * lookupExponent p v))

pAdicCarrierNormDenominator :
  SSP →
  GL.FactorVec →
  ℕ
pAdicCarrierNormDenominator p v =
  denominator (pAdicCarrierNorm p v)

heckeEigenvalue :
  SSP →
  GL.FactorVec →
  PositiveRationalCode
heckeEigenvalue p v =
  let
    pv = (toNat p) ^ lookupExponent p v
  in
  frac ((pv * pv) + one) pv

heckeEigenvalueNumerator :
  SSP →
  GL.FactorVec →
  ℕ
heckeEigenvalueNumerator p v =
  numerator (heckeEigenvalue p v)

heckeWaveNorm :
  SSP →
  GL.FactorVec →
  PositiveRationalCode
heckeWaveNorm p v =
  let
    λp = heckeEigenvalue p v
  in
  frac
    (numerator λp * numerator λp)
    (denominator λp * denominator λp)

boundedDepthAtPrime :
  SSP →
  GL.FactorVec →
  ℕ →
  Bool
boundedDepthAtPrime p v cutoff =
  lookupExponent p v ≤ᵇ cutoff

_&&_ :
  Bool →
  Bool →
  Bool
true && b = b
false && _ = false

infixr 6 _&&_

boundedFactorVecLimit71 :
  GL.FactorVec →
  ℕ →
  Bool
boundedFactorVecLimit71 v cutoff =
  boundedDepthAtPrime p2 v cutoff
  && boundedDepthAtPrime p3 v cutoff
  && boundedDepthAtPrime p5 v cutoff
  && boundedDepthAtPrime p7 v cutoff
  && boundedDepthAtPrime p11 v cutoff
  && boundedDepthAtPrime p13 v cutoff
  && boundedDepthAtPrime p17 v cutoff
  && boundedDepthAtPrime p19 v cutoff
  && boundedDepthAtPrime p23 v cutoff
  && boundedDepthAtPrime p29 v cutoff
  && boundedDepthAtPrime p31 v cutoff
  && boundedDepthAtPrime p41 v cutoff
  && boundedDepthAtPrime p47 v cutoff
  && boundedDepthAtPrime p59 v cutoff
  && boundedDepthAtPrime p71 v cutoff

finiteSSPExponentSum :
  GL.FactorVec →
  ℕ
finiteSSPExponentSum v =
  lookupExponent p2 v
  + lookupExponent p3 v
  + lookupExponent p5 v
  + lookupExponent p7 v
  + lookupExponent p11 v
  + lookupExponent p13 v
  + lookupExponent p17 v
  + lookupExponent p19 v
  + lookupExponent p23 v
  + lookupExponent p29 v
  + lookupExponent p31 v
  + lookupExponent p41 v
  + lookupExponent p47 v
  + lookupExponent p59 v
  + lookupExponent p71 v

finiteSSPExponentSumLimit71Bound :
  ℕ →
  ℕ
finiteSSPExponentSumLimit71Bound cutoff =
  fifteen * cutoff

finiteSSPPrimePowerSum :
  GL.FactorVec →
  ℕ
finiteSSPPrimePowerSum v =
  ((toNat p2) ^ lookupExponent p2 v)
  + ((toNat p3) ^ lookupExponent p3 v)
  + ((toNat p5) ^ lookupExponent p5 v)
  + ((toNat p7) ^ lookupExponent p7 v)
  + ((toNat p11) ^ lookupExponent p11 v)
  + ((toNat p13) ^ lookupExponent p13 v)
  + ((toNat p17) ^ lookupExponent p17 v)
  + ((toNat p19) ^ lookupExponent p19 v)
  + ((toNat p23) ^ lookupExponent p23 v)
  + ((toNat p29) ^ lookupExponent p29 v)
  + ((toNat p31) ^ lookupExponent p31 v)
  + ((toNat p41) ^ lookupExponent p41 v)
  + ((toNat p47) ^ lookupExponent p47 v)
  + ((toNat p59) ^ lookupExponent p59 v)
  + ((toNat p71) ^ lookupExponent p71 v)

finiteSSPPrimePowerSumLimit71Bound :
  ℕ →
  ℕ
finiteSSPPrimePowerSumLimit71Bound cutoff =
  fifteen * (limit71 ^ cutoff)

finiteSSPPrimePowerProduct :
  GL.FactorVec →
  ℕ
finiteSSPPrimePowerProduct v =
  ((toNat p2) ^ lookupExponent p2 v)
  * ((toNat p3) ^ lookupExponent p3 v)
  * ((toNat p5) ^ lookupExponent p5 v)
  * ((toNat p7) ^ lookupExponent p7 v)
  * ((toNat p11) ^ lookupExponent p11 v)
  * ((toNat p13) ^ lookupExponent p13 v)
  * ((toNat p17) ^ lookupExponent p17 v)
  * ((toNat p19) ^ lookupExponent p19 v)
  * ((toNat p23) ^ lookupExponent p23 v)
  * ((toNat p29) ^ lookupExponent p29 v)
  * ((toNat p31) ^ lookupExponent p31 v)
  * ((toNat p41) ^ lookupExponent p41 v)
  * ((toNat p47) ^ lookupExponent p47 v)
  * ((toNat p59) ^ lookupExponent p59 v)
  * ((toNat p71) ^ lookupExponent p71 v)

finiteSSPPrimePowerProductLimit71Bound :
  ℕ →
  ℕ
finiteSSPPrimePowerProductLimit71Bound cutoff =
  (limit71 ^ cutoff) ^ fifteen

boundedModelLimit71InequalitySurface :
  GL.FactorVec →
  ℕ →
  Bool
boundedModelLimit71InequalitySurface v cutoff =
  boundedFactorVecLimit71 v cutoff
  && (finiteSSPExponentSum v ≤ᵇ finiteSSPExponentSumLimit71Bound cutoff)
  && (finiteSSPPrimePowerSum v ≤ᵇ finiteSSPPrimePowerSumLimit71Bound cutoff)
  && (finiteSSPPrimePowerProduct v ≤ᵇ finiteSSPPrimePowerProductLimit71Bound cutoff)

canonicalLimit71ReachableFactorVec :
  GL.FactorVec
canonicalLimit71ReachableFactorVec =
  MP.canonicalVec15PAdicCarrierExponentSkeleton

canonicalLimit71ReachableCutoff :
  ℕ
canonicalLimit71ReachableCutoff =
  0

canonicalLimit71InequalityReachable :
  boundedModelLimit71InequalitySurface
    canonicalLimit71ReachableFactorVec
    canonicalLimit71ReachableCutoff
  ≡ true
canonicalLimit71InequalityReachable =
  refl

sigBit :
  SSP →
  HScan.Sig15 →
  Bool
sigBit p2  σ = HScan.Sig15.b2 σ
sigBit p3  σ = HScan.Sig15.b3 σ
sigBit p5  σ = HScan.Sig15.b5 σ
sigBit p7  σ = HScan.Sig15.b7 σ
sigBit p11 σ = HScan.Sig15.b11 σ
sigBit p13 σ = HScan.Sig15.b13 σ
sigBit p17 σ = HScan.Sig15.b17 σ
sigBit p19 σ = HScan.Sig15.b19 σ
sigBit p23 σ = HScan.Sig15.b23 σ
sigBit p29 σ = HScan.Sig15.b29 σ
sigBit p31 σ = HScan.Sig15.b31 σ
sigBit p41 σ = HScan.Sig15.b41 σ
sigBit p47 σ = HScan.Sig15.b47 σ
sigBit p59 σ = HScan.Sig15.b59 σ
sigBit p71 σ = HScan.Sig15.b71 σ

sigAdmissibleAtPrime :
  HScan.Sig15 →
  GL.FactorVec →
  SSP →
  ℕ →
  Bool
sigAdmissibleAtPrime σ v p cutoff =
  sigBit p σ && boundedDepthAtPrime p v cutoff

sigAdmissibility :
  HScan.Sig15 →
  GL.FactorVec →
  ℕ →
  Bool
sigAdmissibility σ v cutoff =
  sigAdmissibleAtPrime σ v p2 cutoff
  && sigAdmissibleAtPrime σ v p3 cutoff
  && sigAdmissibleAtPrime σ v p5 cutoff
  && sigAdmissibleAtPrime σ v p7 cutoff
  && sigAdmissibleAtPrime σ v p11 cutoff
  && sigAdmissibleAtPrime σ v p13 cutoff
  && sigAdmissibleAtPrime σ v p17 cutoff
  && sigAdmissibleAtPrime σ v p19 cutoff
  && sigAdmissibleAtPrime σ v p23 cutoff
  && sigAdmissibleAtPrime σ v p29 cutoff
  && sigAdmissibleAtPrime σ v p31 cutoff
  && sigAdmissibleAtPrime σ v p41 cutoff
  && sigAdmissibleAtPrime σ v p47 cutoff
  && sigAdmissibleAtPrime σ v p59 cutoff
  && sigAdmissibleAtPrime σ v p71 cutoff

partialZetaDenominator :
  ℕ
partialZetaDenominator =
  ((toNat p2  ^ two) ∸ one) * ((toNat p3  ^ two) ∸ one) * ((toNat p5  ^ two) ∸ one) *
  ((toNat p7  ^ two) ∸ one) * ((toNat p11 ^ two) ∸ one) * ((toNat p13 ^ two) ∸ one) *
  ((toNat p17 ^ two) ∸ one) * ((toNat p19 ^ two) ∸ one) * ((toNat p23 ^ two) ∸ one) *
  ((toNat p29 ^ two) ∸ one) * ((toNat p31 ^ two) ∸ one) * ((toNat p41 ^ two) ∸ one) *
  ((toNat p47 ^ two) ∸ one) * ((toNat p59 ^ two) ∸ one) * ((toNat p71 ^ two) ∸ one)

partialZetaNumerator :
  ℕ
partialZetaNumerator =
  (toNat p2  ^ two) * (toNat p3  ^ two) * (toNat p5  ^ two) *
  (toNat p7  ^ two) * (toNat p11 ^ two) * (toNat p13 ^ two) *
  (toNat p17 ^ two) * (toNat p19 ^ two) * (toNat p23 ^ two) *
  (toNat p29 ^ two) * (toNat p31 ^ two) * (toNat p41 ^ two) *
  (toNat p47 ^ two) * (toNat p59 ^ two) * (toNat p71 ^ two)

adelicConstant :
  PositiveRationalCode
adelicConstant =
  frac partialZetaNumerator partialZetaDenominator

data Gate3NormDictionaryNonClaim : Set where
  noAnalyticAdeleRingPromotion :
    Gate3NormDictionaryNonClaim
  noSchwartzBruhatTestFunctionSpace :
    Gate3NormDictionaryNonClaim
  noAdelicPlancherelProof :
    Gate3NormDictionaryNonClaim
  noFullAdelicPlancherelTheorem :
    Gate3NormDictionaryNonClaim
  noSobolevBridgeInequalityProof :
    Gate3NormDictionaryNonClaim
  noClayPromotion :
    Gate3NormDictionaryNonClaim
  noPhysicsPromotion :
    Gate3NormDictionaryNonClaim

canonicalGate3NormDictionaryNonClaims :
  List Gate3NormDictionaryNonClaim
canonicalGate3NormDictionaryNonClaims =
  noAnalyticAdeleRingPromotion
  ∷ noSchwartzBruhatTestFunctionSpace
  ∷ noAdelicPlancherelProof
  ∷ noFullAdelicPlancherelTheorem
  ∷ noSobolevBridgeInequalityProof
  ∷ noClayPromotion
  ∷ noPhysicsPromotion
  ∷ []

dictionaryReading :
  String
dictionaryReading =
  "Concrete Gate 3 norm dictionary: FactorVec valuations give p-adic norm codes, Hecke eigenvalue codes, Sig15 plus depth admissibility, and the finite SSP partial Euler-product constant."

boundedModelLimit71Reading :
  String
boundedModelLimit71Reading =
  "Finite BoundedModel limit71 surface: the zero-exponent FactorVec reaches the finite inequality checker at cutoff 0; bounded FactorVec exponents over the compact 15-SSP set give finite SSP sum/product bounds only, with no Schwartz-Bruhat, adelic Sobolev, or full adelic Plancherel promotion."

record Gate3NormDictionaryReceipt : Set where
  field
    status :
      Gate3NormDictionaryStatus

    statusIsComputable :
      status
      ≡ normDictionaryComputable_analyticInequalityStillExternal

    sampleCarrier :
      GL.FactorVec

    sampleCarrierIsCanonical :
      sampleCarrier ≡ MP.canonicalVec15PAdicCarrierExponentSkeleton

    normAtPrime :
      SSP →
      GL.FactorVec →
      PositiveRationalCode

    normAtPrimeIsPadicCarrierNorm :
      normAtPrime ≡ pAdicCarrierNorm

    eigenvalueAtPrime :
      SSP →
      GL.FactorVec →
      PositiveRationalCode

    eigenvalueAtPrimeIsHeckeEigenvalue :
      eigenvalueAtPrime ≡ heckeEigenvalue

    waveNormAtPrime :
      SSP →
      GL.FactorVec →
      PositiveRationalCode

    waveNormAtPrimeIsHeckeWaveNorm :
      waveNormAtPrime ≡ heckeWaveNorm

    admissibleSig15Depth :
      HScan.Sig15 →
      GL.FactorVec →
      ℕ →
      Bool

    admissibleSig15DepthIsCanonical :
      admissibleSig15Depth ≡ sigAdmissibility

    adelicConstantCode :
      PositiveRationalCode

    adelicConstantCodeIsPartialEulerProduct :
      adelicConstantCode ≡ adelicConstant

    nonClaims :
      List Gate3NormDictionaryNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalGate3NormDictionaryNonClaims

    reading :
      String

    readingIsCanonical :
      reading ≡ dictionaryReading

    boundedModelStatus :
      BoundedModelLimit71Status

    boundedModelStatusIsLimit71Surface :
      boundedModelStatus
      ≡ finiteBoundedModelLimit71InequalitySurface_only

    compactFiniteSetStatus :
      BoundedModelFiniteSetStatus

    compactFiniteSetStatusIsLimit71 :
      compactFiniteSetStatus ≡ compactFiniteSSPSet_limit71

    finitePrimeSet :
      List SSP

    finitePrimeSetIsCanonical :
      finitePrimeSet ≡ finiteSSP

    exponentBoundSurface :
      GL.FactorVec →
      ℕ →
      Bool

    exponentBoundSurfaceIsLimit71 :
      exponentBoundSurface ≡ boundedFactorVecLimit71

    finiteSSPSum :
      GL.FactorVec →
      ℕ

    finiteSSPSumIsCanonical :
      finiteSSPSum ≡ finiteSSPPrimePowerSum

    finiteSSPSumBound :
      ℕ →
      ℕ

    finiteSSPSumBoundIsLimit71 :
      finiteSSPSumBound ≡ finiteSSPPrimePowerSumLimit71Bound

    finiteSSPProduct :
      GL.FactorVec →
      ℕ

    finiteSSPProductIsCanonical :
      finiteSSPProduct ≡ finiteSSPPrimePowerProduct

    finiteSSPProductBound :
      ℕ →
      ℕ

    finiteSSPProductBoundIsLimit71 :
      finiteSSPProductBound ≡ finiteSSPPrimePowerProductLimit71Bound

    limit71InequalitySurface :
      GL.FactorVec →
      ℕ →
      Bool

    limit71InequalitySurfaceIsCanonical :
      limit71InequalitySurface ≡ boundedModelLimit71InequalitySurface

    limit71ReachableFactorVec :
      GL.FactorVec

    limit71ReachableFactorVecIsCanonical :
      limit71ReachableFactorVec ≡ canonicalLimit71ReachableFactorVec

    limit71ReachableCutoff :
      ℕ

    limit71ReachableCutoffIsCanonical :
      limit71ReachableCutoff ≡ canonicalLimit71ReachableCutoff

    limit71InequalityReachable :
      limit71InequalitySurface
        limit71ReachableFactorVec
        limit71ReachableCutoff
      ≡ true

    boundedModelReading :
      String

    boundedModelReadingIsCanonical :
      boundedModelReading ≡ boundedModelLimit71Reading

    analyticProofPromoted :
      Bool

    analyticProofPromotedIsFalse :
      analyticProofPromoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

data AnalyticPromotionToken : Set where
data ClayPromotionToken : Set where

analyticPromotionImpossibleHere :
  AnalyticPromotionToken →
  ⊥
analyticPromotionImpossibleHere ()

clayPromotionImpossibleHere :
  ClayPromotionToken →
  ⊥
clayPromotionImpossibleHere ()

canonicalGate3NormDictionaryReceipt :
  Gate3NormDictionaryReceipt
canonicalGate3NormDictionaryReceipt =
  record
    { status =
        normDictionaryComputable_analyticInequalityStillExternal
    ; statusIsComputable =
        refl
    ; sampleCarrier =
        MP.canonicalVec15PAdicCarrierExponentSkeleton
    ; sampleCarrierIsCanonical =
        refl
    ; normAtPrime =
        pAdicCarrierNorm
    ; normAtPrimeIsPadicCarrierNorm =
        refl
    ; eigenvalueAtPrime =
        heckeEigenvalue
    ; eigenvalueAtPrimeIsHeckeEigenvalue =
        refl
    ; waveNormAtPrime =
        heckeWaveNorm
    ; waveNormAtPrimeIsHeckeWaveNorm =
        refl
    ; admissibleSig15Depth =
        sigAdmissibility
    ; admissibleSig15DepthIsCanonical =
        refl
    ; adelicConstantCode =
        adelicConstant
    ; adelicConstantCodeIsPartialEulerProduct =
        refl
    ; nonClaims =
        canonicalGate3NormDictionaryNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; reading =
        dictionaryReading
    ; readingIsCanonical =
        refl
    ; boundedModelStatus =
        finiteBoundedModelLimit71InequalitySurface_only
    ; boundedModelStatusIsLimit71Surface =
        refl
    ; compactFiniteSetStatus =
        compactFiniteSSPSet_limit71
    ; compactFiniteSetStatusIsLimit71 =
        refl
    ; finitePrimeSet =
        finiteSSP
    ; finitePrimeSetIsCanonical =
        refl
    ; exponentBoundSurface =
        boundedFactorVecLimit71
    ; exponentBoundSurfaceIsLimit71 =
        refl
    ; finiteSSPSum =
        finiteSSPPrimePowerSum
    ; finiteSSPSumIsCanonical =
        refl
    ; finiteSSPSumBound =
        finiteSSPPrimePowerSumLimit71Bound
    ; finiteSSPSumBoundIsLimit71 =
        refl
    ; finiteSSPProduct =
        finiteSSPPrimePowerProduct
    ; finiteSSPProductIsCanonical =
        refl
    ; finiteSSPProductBound =
        finiteSSPPrimePowerProductLimit71Bound
    ; finiteSSPProductBoundIsLimit71 =
        refl
    ; limit71InequalitySurface =
        boundedModelLimit71InequalitySurface
    ; limit71InequalitySurfaceIsCanonical =
        refl
    ; limit71ReachableFactorVec =
        canonicalLimit71ReachableFactorVec
    ; limit71ReachableFactorVecIsCanonical =
        refl
    ; limit71ReachableCutoff =
        canonicalLimit71ReachableCutoff
    ; limit71ReachableCutoffIsCanonical =
        refl
    ; limit71InequalityReachable =
        canonicalLimit71InequalityReachable
    ; boundedModelReading =
        boundedModelLimit71Reading
    ; boundedModelReadingIsCanonical =
        refl
    ; analyticProofPromoted =
        false
    ; analyticProofPromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    }

canonicalGate3NormDictionaryStatus :
  Gate3NormDictionaryStatus
canonicalGate3NormDictionaryStatus =
  Gate3NormDictionaryReceipt.status canonicalGate3NormDictionaryReceipt

------------------------------------------------------------------------
-- Feshbach-Schur / fibre-gap route boundary.
--
-- A positive spectral gap on a selected carrier fibre is useful input, but
-- it is not a tensor-product Hamiltonian gap.  The route below records the
-- extra hypotheses that must be supplied before any such promotion can even
-- be asked for: Gate 3 density of the selected core in the target Hilbert
-- space, a Feshbach projection decomposition, Schur-complement invertibility
-- on the complement, off-diagonal relative bounds, and domain/core
-- compatibility for the full operator.  This is a dependency receipt only.

data Gate3FeshbachSchurStatus : Set where
  fibreGapEvidenceOnly_fullTensorGapRequiresDensityAndFeshbachSchur :
    Gate3FeshbachSchurStatus

data Gate3FeshbachSchurIngredient : Set where
  selectedCarrierFibreGapEvidence :
    Gate3FeshbachSchurIngredient

  gate3DensityOfCarrierCore :
    Gate3FeshbachSchurIngredient

  feshbachProjectionDecomposition :
    Gate3FeshbachSchurIngredient

  schurComplementInvertibility :
    Gate3FeshbachSchurIngredient

  offDiagonalRelativeBound :
    Gate3FeshbachSchurIngredient

  tensorHamiltonianDomainCompatibility :
    Gate3FeshbachSchurIngredient

canonicalGate3FeshbachSchurIngredients :
  List Gate3FeshbachSchurIngredient
canonicalGate3FeshbachSchurIngredients =
  selectedCarrierFibreGapEvidence
  ∷ gate3DensityOfCarrierCore
  ∷ feshbachProjectionDecomposition
  ∷ schurComplementInvertibility
  ∷ offDiagonalRelativeBound
  ∷ tensorHamiltonianDomainCompatibility
  ∷ []

data FullTensorProductGapPromotion : Set where

fullTensorProductGapPromotionImpossibleHere :
  FullTensorProductGapPromotion →
  ⊥
fullTensorProductGapPromotionImpossibleHere ()

feshbachSchurRouteReading :
  String
feshbachSchurRouteReading =
  "Feshbach-Schur route boundary: a carrier-fibre spectral gap is evidence/ingredient only; a full tensor-product Hamiltonian gap requires Gate 3 density of the carrier core plus Feshbach projection, Schur-complement invertibility, off-diagonal relative bounds, and domain compatibility."

record Gate3FeshbachSchurFiberGapRouteReceipt : Set where
  field
    status :
      Gate3FeshbachSchurStatus

    statusIsEvidenceOnly :
      status
      ≡
      fibreGapEvidenceOnly_fullTensorGapRequiresDensityAndFeshbachSchur

    normDictionaryReceipt :
      Gate3NormDictionaryReceipt

    finiteLimit71SurfaceReachable :
      Gate3NormDictionaryReceipt.limit71InequalitySurface
        normDictionaryReceipt
        (Gate3NormDictionaryReceipt.limit71ReachableFactorVec
          normDictionaryReceipt)
        (Gate3NormDictionaryReceipt.limit71ReachableCutoff
          normDictionaryReceipt)
      ≡
      true

    carrierFibreGapEvidenceAvailable :
      Bool

    carrierFibreGapEvidenceAvailableIsTrue :
      carrierFibreGapEvidenceAvailable ≡ true

    carrierFibreGapOnlyIngredient :
      Bool

    carrierFibreGapOnlyIngredientIsTrue :
      carrierFibreGapOnlyIngredient ≡ true

    gate3DensityOfCarrierCoreProved :
      Bool

    gate3DensityOfCarrierCoreProvedIsTrue :
      gate3DensityOfCarrierCoreProved ≡ true

    feshbachProjectionHypothesisProved :
      Bool

    feshbachProjectionHypothesisProvedIsFalse :
      feshbachProjectionHypothesisProved ≡ false

    schurComplementHypothesisProved :
      Bool

    schurComplementHypothesisProvedIsFalse :
      schurComplementHypothesisProved ≡ false

    offDiagonalRelativeBoundProved :
      Bool

    offDiagonalRelativeBoundProvedIsFalse :
      offDiagonalRelativeBoundProved ≡ false

    tensorHamiltonianDomainCompatibilityProved :
      Bool

    tensorHamiltonianDomainCompatibilityProvedIsFalse :
      tensorHamiltonianDomainCompatibilityProved ≡ false

    fullTensorProductGapPromoted :
      Bool

    fullTensorProductGapPromotedIsFalse :
      fullTensorProductGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    ingredients :
      List Gate3FeshbachSchurIngredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalGate3FeshbachSchurIngredients

    reading :
      String

    readingIsCanonical :
      reading ≡ feshbachSchurRouteReading

    promotionFlags :
      List FullTensorProductGapPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open Gate3FeshbachSchurFiberGapRouteReceipt public

canonicalGate3FeshbachSchurFiberGapRouteReceipt :
  Gate3FeshbachSchurFiberGapRouteReceipt
canonicalGate3FeshbachSchurFiberGapRouteReceipt =
  record
    { status =
        fibreGapEvidenceOnly_fullTensorGapRequiresDensityAndFeshbachSchur
    ; statusIsEvidenceOnly =
        refl
    ; normDictionaryReceipt =
        canonicalGate3NormDictionaryReceipt
    ; finiteLimit71SurfaceReachable =
        canonicalLimit71InequalityReachable
    ; carrierFibreGapEvidenceAvailable =
        true
    ; carrierFibreGapEvidenceAvailableIsTrue =
        refl
    ; carrierFibreGapOnlyIngredient =
        true
    ; carrierFibreGapOnlyIngredientIsTrue =
        refl
    ; gate3DensityOfCarrierCoreProved =
        true
    ; gate3DensityOfCarrierCoreProvedIsTrue =
        refl
    ; feshbachProjectionHypothesisProved =
        false
    ; feshbachProjectionHypothesisProvedIsFalse =
        refl
    ; schurComplementHypothesisProved =
        false
    ; schurComplementHypothesisProvedIsFalse =
        refl
    ; offDiagonalRelativeBoundProved =
        false
    ; offDiagonalRelativeBoundProvedIsFalse =
        refl
    ; tensorHamiltonianDomainCompatibilityProved =
        false
    ; tensorHamiltonianDomainCompatibilityProvedIsFalse =
        refl
    ; fullTensorProductGapPromoted =
        false
    ; fullTensorProductGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; ingredients =
        canonicalGate3FeshbachSchurIngredients
    ; ingredientsAreCanonical =
        refl
    ; reading =
        feshbachSchurRouteReading
    ; readingIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

gate3FeshbachSchurFullTensorGapStillFalse :
  fullTensorProductGapPromoted
    canonicalGate3FeshbachSchurFiberGapRouteReceipt
  ≡
  false
gate3FeshbachSchurFullTensorGapStillFalse =
  refl

------------------------------------------------------------------------
-- Large-field / small-field H_k norm story boundary.
--
-- The concrete p-adic carrier norm, finite BoundedModel limit71 checker,
-- and Contractive bridge surfaces already exist elsewhere in the Gate 3/YM
-- stack.  This receipt only records their intended H_k reading: large-field
-- and small-field norm bookkeeping are candidate story labels over the
-- existing finite carrier dictionary.  It deliberately does not construct an
-- analytic H_k Hilbert scale, prove large/small-field decomposition, or
-- promote a contractive analytic theorem.

data Gate3HkLargeSmallFieldNormStatus : Set where
  hkLargeSmallFieldStoryRecorded_failClosed :
    Gate3HkLargeSmallFieldNormStatus

data Gate3HkLargeSmallFieldNormPiece : Set where
  pAdicCarrierNormCodePresent :
    Gate3HkLargeSmallFieldNormPiece

  boundedModelLimit71SurfacePresent :
    Gate3HkLargeSmallFieldNormPiece

  contractiveBridgeSurfacePresent :
    Gate3HkLargeSmallFieldNormPiece

  largeFieldHkNormStoryLabel :
    Gate3HkLargeSmallFieldNormPiece

  smallFieldHkNormStoryLabel :
    Gate3HkLargeSmallFieldNormPiece

canonicalGate3HkLargeSmallFieldNormPieces :
  List Gate3HkLargeSmallFieldNormPiece
canonicalGate3HkLargeSmallFieldNormPieces =
  pAdicCarrierNormCodePresent
  ∷ boundedModelLimit71SurfacePresent
  ∷ contractiveBridgeSurfacePresent
  ∷ largeFieldHkNormStoryLabel
  ∷ smallFieldHkNormStoryLabel
  ∷ []

hkLargeSmallFieldNormReading :
  String
hkLargeSmallFieldNormReading =
  "Large-field/small-field H_k norm story: p-adic carrier norm codes and finite BoundedModel limit71 bounds are available as finite Gate 3 bookkeeping, while Contractive links remain bridge-shape evidence only."

data HkAnalyticPromotionToken : Set where

hkAnalyticPromotionImpossibleHere :
  HkAnalyticPromotionToken →
  ⊥
hkAnalyticPromotionImpossibleHere ()

record Gate3HkLargeSmallFieldNormStoryReceipt : Set where
  field
    status :
      Gate3HkLargeSmallFieldNormStatus

    statusIsFailClosed :
      status ≡ hkLargeSmallFieldStoryRecorded_failClosed

    normDictionaryReceipt :
      Gate3NormDictionaryReceipt

    pAdicCarrierNormAlreadyPresent :
      Gate3NormDictionaryReceipt.normAtPrime normDictionaryReceipt
      ≡
      pAdicCarrierNorm

    boundedModelLimit71AlreadyPresent :
      Gate3NormDictionaryReceipt.limit71InequalitySurface normDictionaryReceipt
      ≡
      boundedModelLimit71InequalitySurface

    finiteLimit71SurfaceReachable :
      Gate3NormDictionaryReceipt.limit71InequalitySurface
        normDictionaryReceipt
        (Gate3NormDictionaryReceipt.limit71ReachableFactorVec
          normDictionaryReceipt)
        (Gate3NormDictionaryReceipt.limit71ReachableCutoff
          normDictionaryReceipt)
      ≡
      true

    contractiveBridgeSurfaceAlreadyPresent :
      Bool

    contractiveBridgeSurfaceAlreadyPresentIsTrue :
      contractiveBridgeSurfaceAlreadyPresent ≡ true

    largeFieldHkNormStoryRecorded :
      Bool

    largeFieldHkNormStoryRecordedIsTrue :
      largeFieldHkNormStoryRecorded ≡ true

    smallFieldHkNormStoryRecorded :
      Bool

    smallFieldHkNormStoryRecordedIsTrue :
      smallFieldHkNormStoryRecorded ≡ true

    analyticHkHilbertScaleConstructed :
      Bool

    analyticHkHilbertScaleConstructedIsFalse :
      analyticHkHilbertScaleConstructed ≡ false

    largeSmallFieldDecompositionProved :
      Bool

    largeSmallFieldDecompositionProvedIsFalse :
      largeSmallFieldDecompositionProved ≡ false

    contractiveAnalyticTheoremPromoted :
      Bool

    contractiveAnalyticTheoremPromotedIsFalse :
      contractiveAnalyticTheoremPromoted ≡ false

    adelicSobolevProofPromoted :
      Bool

    adelicSobolevProofPromotedIsFalse :
      adelicSobolevProofPromoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    pieces :
      List Gate3HkLargeSmallFieldNormPiece

    piecesAreCanonical :
      pieces ≡ canonicalGate3HkLargeSmallFieldNormPieces

    reading :
      String

    readingIsCanonical :
      reading ≡ hkLargeSmallFieldNormReading

    promotionFlags :
      List HkAnalyticPromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open Gate3HkLargeSmallFieldNormStoryReceipt public

canonicalGate3HkLargeSmallFieldNormStoryReceipt :
  Gate3HkLargeSmallFieldNormStoryReceipt
canonicalGate3HkLargeSmallFieldNormStoryReceipt =
  record
    { status =
        hkLargeSmallFieldStoryRecorded_failClosed
    ; statusIsFailClosed =
        refl
    ; normDictionaryReceipt =
        canonicalGate3NormDictionaryReceipt
    ; pAdicCarrierNormAlreadyPresent =
        refl
    ; boundedModelLimit71AlreadyPresent =
        refl
    ; finiteLimit71SurfaceReachable =
        canonicalLimit71InequalityReachable
    ; contractiveBridgeSurfaceAlreadyPresent =
        true
    ; contractiveBridgeSurfaceAlreadyPresentIsTrue =
        refl
    ; largeFieldHkNormStoryRecorded =
        true
    ; largeFieldHkNormStoryRecordedIsTrue =
        refl
    ; smallFieldHkNormStoryRecorded =
        true
    ; smallFieldHkNormStoryRecordedIsTrue =
        refl
    ; analyticHkHilbertScaleConstructed =
        false
    ; analyticHkHilbertScaleConstructedIsFalse =
        refl
    ; largeSmallFieldDecompositionProved =
        false
    ; largeSmallFieldDecompositionProvedIsFalse =
        refl
    ; contractiveAnalyticTheoremPromoted =
        false
    ; contractiveAnalyticTheoremPromotedIsFalse =
        refl
    ; adelicSobolevProofPromoted =
        false
    ; adelicSobolevProofPromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; pieces =
        canonicalGate3HkLargeSmallFieldNormPieces
    ; piecesAreCanonical =
        refl
    ; reading =
        hkLargeSmallFieldNormReading
    ; readingIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

gate3HkLargeSmallFieldNoAnalyticPromotion :
  contractiveAnalyticTheoremPromoted
    canonicalGate3HkLargeSmallFieldNormStoryReceipt
  ≡
  false
gate3HkLargeSmallFieldNoAnalyticPromotion =
  refl
