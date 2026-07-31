module DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Standard SU(2) principal logarithm on a strict sub-ball.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- In the standard bi-invariant normalization, exp is injective on the open
-- Lie-algebra ball of radius pi and maps it onto SU(2) minus the antipodal
-- element -I.  The carrier below does not hard-code a metric convention: it
-- records the selected radius, its comparison with the standard injectivity
-- radius, and the exact exp/log laws.  A physical instantiation must prove that
-- Bałaban's small-field norm is the selected normalization.
------------------------------------------------------------------------

record StandardSU2PrincipalLogBall
    (Lie Group Radius : Set) : Set₁ where
  field
    expSU2 : Lie → Group
    principalLog : Group → Lie
    negateLie : Lie → Lie
    inverseGroup : Group → Group
    normLie : Lie → Radius

    selectedRadius standardPiRadius : Radius
    LessThan : Radius → Radius → Set

    InSelectedBall : Lie → Set
    InPrincipalImage : Group → Set

    selectedRadiusBelowPi :
      LessThan selectedRadius standardPiRadius

    selectedBallMeaning : ∀ lie →
      InSelectedBall lie ≡ LessThan (normLie lie) selectedRadius

    expMapsSelectedBall : ∀ lie →
      InSelectedBall lie → InPrincipalImage (expSU2 lie)

    principalLogMapsImage : ∀ group →
      InPrincipalImage group → InSelectedBall (principalLog group)

    expPrincipalLog : ∀ group →
      InPrincipalImage group →
      expSU2 (principalLog group) ≡ group

    principalLogExp : ∀ lie →
      InSelectedBall lie →
      principalLog (expSU2 lie) ≡ lie

    expInjectiveOnSelectedBall : ∀ left right →
      InSelectedBall left → InSelectedBall right →
      expSU2 left ≡ expSU2 right → left ≡ right

    negatePreservesSelectedBall : ∀ lie →
      InSelectedBall lie → InSelectedBall (negateLie lie)

    expNegate : ∀ lie →
      expSU2 (negateLie lie) ≡ inverseGroup (expSU2 lie)

    inversePreservesPrincipalImage : ∀ group →
      InPrincipalImage group → InPrincipalImage (inverseGroup group)

open StandardSU2PrincipalLogBall public

principalLogBranchUnique :
  ∀ {Lie Group Radius}
    (dataSet : StandardSU2PrincipalLogBall Lie Group Radius)
    group →
  InPrincipalImage dataSet group →
  ∀ lie →
  InSelectedBall dataSet lie →
  expSU2 dataSet lie ≡ group →
  lie ≡ principalLog dataSet group
principalLogBranchUnique dataSet group groupInImage lie lieInBall expLie≡group =
  expInjectiveOnSelectedBall dataSet
    lie
    (principalLog dataSet group)
    lieInBall
    (principalLogMapsImage dataSet group groupInImage)
    (trans expLie≡group
      (sym (expPrincipalLog dataSet group groupInImage)))

principalLogOfInverse :
  ∀ {Lie Group Radius}
    (dataSet : StandardSU2PrincipalLogBall Lie Group Radius)
    group →
  InPrincipalImage dataSet group →
  principalLog dataSet (inverseGroup dataSet group)
  ≡ negateLie dataSet (principalLog dataSet group)
principalLogOfInverse dataSet group groupInImage =
  sym
    (principalLogBranchUnique dataSet
      (inverseGroup dataSet group)
      (inversePreservesPrincipalImage dataSet group groupInImage)
      (negateLie dataSet (principalLog dataSet group))
      (negatePreservesSelectedBall dataSet
        (principalLog dataSet group)
        (principalLogMapsImage dataSet group groupInImage))
      (trans
        (expNegate dataSet (principalLog dataSet group))
        (cong (inverseGroup dataSet)
          (expPrincipalLog dataSet group groupInImage))))

record PhysicalSU2PrincipalLogMeaning
    (Field CoarseBond FineBond Lie Group Radius : Set) : Set₁ where
  field
    chart : StandardSU2PrincipalLogBall Lie Group Radius

    PhysicalSmallField : Field → Set
    transportedRelativeBond : Field → CoarseBond → FineBond → Group
    physicalLog : Field → CoarseBond → FineBond → Lie

    smallFieldImage : ∀ field →
      PhysicalSmallField field →
      ∀ coarse fine →
      InPrincipalImage chart
        (transportedRelativeBond field coarse fine)

    physicalLogMeaning : ∀ field coarse fine →
      physicalLog field coarse fine
      ≡ principalLog chart
          (transportedRelativeBond field coarse fine)

    PhysicalSmallFieldRadiusMatchesSelectedChart : Set
    physicalSmallFieldRadiusMatchesSelectedChart :
      PhysicalSmallFieldRadiusMatchesSelectedChart

open PhysicalSU2PrincipalLogMeaning public

physicalLogExpInverse :
  ∀ {Field CoarseBond FineBond Lie Group Radius}
    (meaning : PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond Lie Group Radius)
    field →
  PhysicalSmallField meaning field →
  ∀ coarse fine →
  expSU2 (chart meaning) (physicalLog meaning field coarse fine)
  ≡ transportedRelativeBond meaning field coarse fine
physicalLogExpInverse meaning field small coarse fine
  rewrite physicalLogMeaning meaning field coarse fine =
  expPrincipalLog (chart meaning)
    (transportedRelativeBond meaning field coarse fine)
    (smallFieldImage meaning field small coarse fine)

su2PrincipalLogStandardTheoremLevel : ProofLevel
su2PrincipalLogStandardTheoremLevel = standardImported

principalLogBranchUniquenessAssemblyLevel : ProofLevel
principalLogBranchUniquenessAssemblyLevel = machineChecked

principalLogInverseOrientationAssemblyLevel : ProofLevel
principalLogInverseOrientationAssemblyLevel = machineChecked

physicalLogExpInverseAssemblyLevel : ProofLevel
physicalLogExpInverseAssemblyLevel = machineChecked

physicalSmallFieldRadiusAndMetricInputsLevel : ProofLevel
physicalSmallFieldRadiusAndMetricInputsLevel = conditional

physicalTransportedBondImageInputsLevel : ProofLevel
physicalTransportedBondImageInputsLevel = conditional
