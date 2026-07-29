module DASHI.Physics.YangMills.BalabanClayGate4SU2HaarIdentityPositivityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2LiteralActivityLossConstantsExact as Loss

------------------------------------------------------------------------
-- Primary provenance.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press, open-access
-- reissue (2022). DOI: 10.1017/9781009290395.
--
-- For SU(2) exponential coordinates the normalized Haar density is the square
-- of a sinc factor. At the identity chart point the norm is zero, sinc(0)=1,
-- and hence the density is exactly one and strictly positive.
------------------------------------------------------------------------

record SU2HaarIdentityData (Link Polymer Scalar : Set) : Set₁ where
  field
    haar : Loss.SU2HaarLossData Link Polymer Scalar
    identityLink : Link

    identityInChart : Loss.InChart haar identityLink
    identityNormZero : Loss.norm haar identityLink ≡ Loss.zero haar
    divideZeroByTwo :
      Loss.divide haar (Loss.zero haar) (Loss.two haar) ≡ Loss.zero haar
    sincAtZero : Loss.sinOverX haar (Loss.zero haar) ≡ Loss.one haar
    squareOne :
      Loss.square haar (Loss.one haar) (Loss.one haar) ≡ Loss.one haar

    Positive : Scalar → Set
    onePositive : Positive (Loss.one haar)

open SU2HaarIdentityData public

haarDensityAtIdentityExact :
  ∀ {Link Polymer Scalar} →
  (dataSet : SU2HaarIdentityData Link Polymer Scalar) →
  Loss.haarDensity (haar dataSet) (identityLink dataSet)
  ≡ Loss.one (haar dataSet)
haarDensityAtIdentityExact dataSet =
  trans
    (Loss.su2HaarDensityExponentialCoordinatesExact
      (haar dataSet) (identityLink dataSet) (identityInChart dataSet))
    (trans
      (cong
        (λ radiusValue →
          Loss.square (haar dataSet)
            (Loss.sinOverX (haar dataSet)
              (Loss.divide (haar dataSet) radiusValue
                (Loss.two (haar dataSet))))
            (Loss.one (haar dataSet)))
        (identityNormZero dataSet))
      (trans
        (cong
          (λ dividedValue →
            Loss.square (haar dataSet)
              (Loss.sinOverX (haar dataSet) dividedValue)
              (Loss.one (haar dataSet)))
          (divideZeroByTwo dataSet))
        (trans
          (cong
            (λ sincValue →
              Loss.square (haar dataSet) sincValue
                (Loss.one (haar dataSet)))
            (sincAtZero dataSet))
          (squareOne dataSet))))

haarDensityAtIdentityPositive :
  ∀ {Link Polymer Scalar} →
  (dataSet : SU2HaarIdentityData Link Polymer Scalar) →
  Positive dataSet
    (Loss.haarDensity (haar dataSet) (identityLink dataSet))
haarDensityAtIdentityPositive dataSet =
  subst (Positive dataSet)
    (sym (haarDensityAtIdentityExact dataSet))
    (onePositive dataSet)

su2HaarIdentityDensityLevel : ProofLevel
su2HaarIdentityDensityLevel = machineChecked

su2HaarIdentityPositivityLevel : ProofLevel
su2HaarIdentityPositivityLevel = machineChecked

physicalIdentityLinkHaarFormulaInputsLevel : ProofLevel
physicalIdentityLinkHaarFormulaInputsLevel = conditional
