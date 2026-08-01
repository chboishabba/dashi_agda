module DASHI.Physics.YangMills.BalabanClayGate4SU2PauliNormConventionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One Pauli/R^3 norm convention for all physical SU(2) estimates.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- The intended normalization is X = (i/2) x.sigma.  In that convention the
-- Lie bracket is the signed Euclidean cross product, so
--
--   ||[X,Y]|| <= ||X|| ||Y||
--
-- and the induced adjoint operator satisfies ||ad_X|| <= ||X||.  Equality may
-- be proved later for the Euclidean operator norm, but only the upper bound is
-- required by the shared chart and Newton estimates.  The sign is irrelevant
-- to the norm and remains part of the literal bracket identification.
------------------------------------------------------------------------

record NormedCrossProduct (Vector Scalar : Set) : Set₁ where
  field
    cross : Vector → Vector → Vector
    norm : Vector → Scalar
    multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    crossProductBound : ∀ left right →
      LessEqual
        (norm (cross left right))
        (multiply (norm left) (norm right))

open NormedCrossProduct public

record PauliSU2NormConvention
    (Lie Vector Scalar : Set) : Set₁ where
  field
    vectorGeometry : NormedCrossProduct Vector Scalar

    encode : Vector → Lie
    decode : Lie → Vector

    decodeEncode : ∀ vector → decode (encode vector) ≡ vector
    encodeDecode : ∀ lie → encode (decode lie) ≡ lie

    bracket : Lie → Lie → Lie
    lieNorm : Lie → Scalar

    bracketAsSignedCross : ∀ left right →
      decode (bracket left right)
      ≡ cross vectorGeometry (decode left) (decode right)

    normAsEuclidean : ∀ lie →
      lieNorm lie ≡ norm vectorGeometry (decode lie)

open PauliSU2NormConvention public

adAction :
  ∀ {Lie Vector Scalar} →
  PauliSU2NormConvention Lie Vector Scalar →
  Lie → Lie → Lie
adAction convention x y = bracket convention x y

pauliBracketNormBound :
  ∀ {Lie Vector Scalar}
    (convention : PauliSU2NormConvention Lie Vector Scalar)
    left right →
  LessEqual (vectorGeometry convention)
    (lieNorm convention (bracket convention left right))
    (multiply (vectorGeometry convention)
      (lieNorm convention left) (lieNorm convention right))
pauliBracketNormBound convention left right =
  subst
    (λ lower → LessEqual (vectorGeometry convention) lower
      (multiply (vectorGeometry convention)
        (lieNorm convention left) (lieNorm convention right)))
    (sym (normAsEuclidean convention (bracket convention left right)))
    (subst
      (λ decodedBracket →
        LessEqual (vectorGeometry convention)
          (norm (vectorGeometry convention) decodedBracket)
          (multiply (vectorGeometry convention)
            (lieNorm convention left) (lieNorm convention right)))
      (sym (bracketAsSignedCross convention left right))
      (subst
        (λ leftNorm →
          LessEqual (vectorGeometry convention)
            (norm (vectorGeometry convention)
              (cross (vectorGeometry convention)
                (decode convention left) (decode convention right)))
            (multiply (vectorGeometry convention)
              leftNorm (lieNorm convention right)))
        (sym (normAsEuclidean convention left))
        (subst
          (λ rightNorm →
            LessEqual (vectorGeometry convention)
              (norm (vectorGeometry convention)
                (cross (vectorGeometry convention)
                  (decode convention left) (decode convention right)))
              (multiply (vectorGeometry convention)
                (norm (vectorGeometry convention) (decode convention left))
                rightNorm))
          (sym (normAsEuclidean convention right))
          (crossProductBound (vectorGeometry convention)
            (decode convention left) (decode convention right)))))

record PauliAdjointOperatorNormMeaning
    (Lie Vector Scalar : Set) : Set₁ where
  field
    convention : PauliSU2NormConvention Lie Vector Scalar

    operatorNorm : (Lie → Lie) → Scalar
    OperatorLessEqual : Scalar → Scalar → Set

    orderAgrees :
      OperatorLessEqual ≡ LessEqual (vectorGeometry convention)

    adjointOperatorUpperFromBracket : ∀ x →
      OperatorLessEqual
        (operatorNorm (adAction convention x))
        (lieNorm convention x)

open PauliAdjointOperatorNormMeaning public

pauliAdjointNormBelowLieNorm :
  ∀ {Lie Vector Scalar}
    (meaning : PauliAdjointOperatorNormMeaning Lie Vector Scalar)
    x →
  OperatorLessEqual meaning
    (operatorNorm meaning (adAction (convention meaning) x))
    (lieNorm (convention meaning) x)
pauliAdjointNormBelowLieNorm meaning x =
  adjointOperatorUpperFromBracket meaning x

record ConservativeHalfChartRadius (Scalar : Set) : Set₁ where
  field
    one two half cutRadius : Scalar
    divide : Scalar → Scalar → Scalar
    StrictlyBelow : Scalar → Scalar → Set

    halfMeaning : half ≡ divide one two
    halfBelowCutRadius : StrictlyBelow half cutRadius

open ConservativeHalfChartRadius public

pauliSU2BracketNormLevel : ProofLevel
pauliSU2BracketNormLevel = machineChecked

pauliSU2AdjointNormTransportLevel : ProofLevel
pauliSU2AdjointNormTransportLevel = machineChecked

su2ConservativeHalfRadiusSelectionLevel : ProofLevel
su2ConservativeHalfRadiusSelectionLevel = computed

physicalPauliMatrixIdentificationInputsLevel : ProofLevel
physicalPauliMatrixIdentificationInputsLevel = conditional

physicalSU2EuclideanOperatorNormInputsLevel : ProofLevel
physicalSU2EuclideanOperatorNormInputsLevel = conditional

physicalHalfRadiusBelowCutLocusInputsLevel : ProofLevel
physicalHalfRadiusBelowCutLocusInputsLevel = conditional
