module DASHI.Biology.FiniteSymmetryStabiliserExact where

open import DASHI.Core.Prelude
open import DASHI.Biology.TriadicKernelLiftQuotientExact

------------------------------------------------------------------------
-- Exact finite group-action analogue of crystal stabilisers and fundamental
-- domains.  A larger stabiliser lowers the number of independent site values
-- needed to reconstruct a reflection-symmetric pattern, but does not by itself
-- prove energetic or MDL optimality in an unrestricted model class.

data Reflection2 : Set where
  identityReflection : Reflection2
  swapReflection : Reflection2

composeReflection : Reflection2 → Reflection2 → Reflection2
composeReflection identityReflection h = h
composeReflection swapReflection identityReflection = swapReflection
composeReflection swapReflection swapReflection = identityReflection

reflectionIdentityLeft :
  (g : Reflection2) → composeReflection identityReflection g ≡ g
reflectionIdentityLeft identityReflection = refl
reflectionIdentityLeft swapReflection = refl

reflectionIdentityRight :
  (g : Reflection2) → composeReflection g identityReflection ≡ g
reflectionIdentityRight identityReflection = refl
reflectionIdentityRight swapReflection = refl

reflectionAssociative :
  (g h k : Reflection2) →
  composeReflection (composeReflection g h) k
  ≡
  composeReflection g (composeReflection h k)
reflectionAssociative identityReflection identityReflection identityReflection = refl
reflectionAssociative identityReflection identityReflection swapReflection = refl
reflectionAssociative identityReflection swapReflection identityReflection = refl
reflectionAssociative identityReflection swapReflection swapReflection = refl
reflectionAssociative swapReflection identityReflection identityReflection = refl
reflectionAssociative swapReflection identityReflection swapReflection = refl
reflectionAssociative swapReflection swapReflection identityReflection = refl
reflectionAssociative swapReflection swapReflection swapReflection = refl

data Site2 : Set where
  leftSite : Site2
  rightSite : Site2

actSite : Reflection2 → Site2 → Site2
actSite identityReflection x = x
actSite swapReflection leftSite = rightSite
actSite swapReflection rightSite = leftSite

siteActionComposition :
  (g h : Reflection2) (x : Site2) →
  actSite (composeReflection g h) x ≡ actSite g (actSite h x)
siteActionComposition identityReflection identityReflection leftSite = refl
siteActionComposition identityReflection identityReflection rightSite = refl
siteActionComposition identityReflection swapReflection leftSite = refl
siteActionComposition identityReflection swapReflection rightSite = refl
siteActionComposition swapReflection identityReflection leftSite = refl
siteActionComposition swapReflection identityReflection rightSite = refl
siteActionComposition swapReflection swapReflection leftSite = refl
siteActionComposition swapReflection swapReflection rightSite = refl

Pattern2 : Set
Pattern2 = Site2 → KernelTrit

actPattern : Reflection2 → Pattern2 → Pattern2
actPattern g pattern x = pattern (actSite g x)

patternActionComposition :
  (g h : Reflection2) (pattern : Pattern2) (x : Site2) →
  actPattern (composeReflection g h) pattern x
  ≡
  actPattern g (actPattern h pattern) x
patternActionComposition identityReflection identityReflection pattern leftSite = refl
patternActionComposition identityReflection identityReflection pattern rightSite = refl
patternActionComposition identityReflection swapReflection pattern leftSite = refl
patternActionComposition identityReflection swapReflection pattern rightSite = refl
patternActionComposition swapReflection identityReflection pattern leftSite = refl
patternActionComposition swapReflection identityReflection pattern rightSite = refl
patternActionComposition swapReflection swapReflection pattern leftSite = refl
patternActionComposition swapReflection swapReflection pattern rightSite = refl

constantPattern : Pattern2
constantPattern leftSite = positiveTrit
constantPattern rightSite = positiveTrit

asymmetricPattern : Pattern2
asymmetricPattern leftSite = positiveTrit
asymmetricPattern rightSite = negativeTrit

sameTrit : KernelTrit → KernelTrit → Bool
sameTrit negativeTrit negativeTrit = true
sameTrit zeroTrit zeroTrit = true
sameTrit positiveTrit positiveTrit = true
sameTrit _ _ = false

andBool : Bool → Bool → Bool
andBool true true = true
andBool _ _ = false

fixedBy : Reflection2 → Pattern2 → Bool
fixedBy g pattern =
  andBool
    (sameTrit (actPattern g pattern leftSite) (pattern leftSite))
    (sameTrit (actPattern g pattern rightSite) (pattern rightSite))

boolToNat : Bool → Nat
boolToNat false = 0
boolToNat true = 1

stabiliserSize : Pattern2 → Nat
stabiliserSize pattern =
  boolToNat (fixedBy identityReflection pattern)
  +
  boolToNat (fixedBy swapReflection pattern)

constantPatternHasFullStabiliser : stabiliserSize constantPattern ≡ 2
constantPatternHasFullStabiliser = refl

asymmetricPatternHasTrivialStabiliser : stabiliserSize asymmetricPattern ≡ 1
asymmetricPatternHasTrivialStabiliser = refl

swapFixesConstantPattern :
  (x : Site2) → actPattern swapReflection constantPattern x ≡ constantPattern x
swapFixesConstantPattern leftSite = refl
swapFixesConstantPattern rightSite = refl

swapChangesAsymmetricPatternAtLeft :
  sameTrit
    (actPattern swapReflection asymmetricPattern leftSite)
    (asymmetricPattern leftSite)
  ≡
  false
swapChangesAsymmetricPatternAtLeft = refl

------------------------------------------------------------------------
-- Fundamental-domain encoding.  One value reconstructs a symmetric pattern;
-- a generic pattern needs both site values.

record SymmetricFundamentalDatum : Set where
  constructor symmetricFundamentalDatum
  field
    representativeValue : KernelTrit

open SymmetricFundamentalDatum public

reconstructSymmetric : SymmetricFundamentalDatum → Pattern2
reconstructSymmetric datum leftSite = representativeValue datum
reconstructSymmetric datum rightSite = representativeValue datum

constantPatternFromOneDatum :
  (x : Site2) →
  reconstructSymmetric (symmetricFundamentalDatum positiveTrit) x
  ≡
  constantPattern x
constantPatternFromOneDatum leftSite = refl
constantPatternFromOneDatum rightSite = refl

independentSiteCount : Pattern2 → Nat
independentSiteCount pattern with fixedBy swapReflection pattern
... | true = 1
... | false = 2

constantPatternNeedsOneIndependentSite :
  independentSiteCount constantPattern ≡ 1
constantPatternNeedsOneIndependentSite = refl

asymmetricPatternNeedsTwoIndependentSites :
  independentSiteCount asymmetricPattern ≡ 2
asymmetricPatternNeedsTwoIndependentSites = refl

record SymmetryStabiliserBoundary : Set where
  constructor symmetryStabiliserBoundary
  field
    largerStabiliserForcesLowerPhysicalEnergy : Bool
    largerStabiliserForcesLowerPhysicalEnergyIsFalse :
      largerStabiliserForcesLowerPhysicalEnergy ≡ false

    largerStabiliserForcesGlobalMDLMinimum : Bool
    largerStabiliserForcesGlobalMDLMinimumIsFalse :
      largerStabiliserForcesGlobalMDLMinimum ≡ false

    fundamentalDomainCanReduceIndependentData : Bool
    fundamentalDomainCanReduceIndependentDataIsTrue :
      fundamentalDomainCanReduceIndependentData ≡ true

open SymmetryStabiliserBoundary public

canonicalSymmetryStabiliserBoundary : SymmetryStabiliserBoundary
canonicalSymmetryStabiliserBoundary =
  symmetryStabiliserBoundary false refl false refl true refl
