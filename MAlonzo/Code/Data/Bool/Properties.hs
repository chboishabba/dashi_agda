{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Data.Bool.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Properties.BooleanAlgebra
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Bool.Properties._._Absorbs_
d__Absorbs__8 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d__Absorbs__8 = erased
-- Data.Bool.Properties._._DistributesOver_
d__DistributesOver__10 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d__DistributesOver__10 = erased
-- Data.Bool.Properties._._DistributesOverʳ_
d__DistributesOver'691'__12 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d__DistributesOver'691'__12 = erased
-- Data.Bool.Properties._._DistributesOverˡ_
d__DistributesOver'737'__14 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d__DistributesOver'737'__14 = erased
-- Data.Bool.Properties._._IdempotentOn_
d__IdempotentOn__16 :: (Bool -> Bool -> Bool) -> Bool -> ()
d__IdempotentOn__16 = erased
-- Data.Bool.Properties._.Absorptive
d_Absorptive_20 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_Absorptive_20 = erased
-- Data.Bool.Properties._.Associative
d_Associative_30 :: (Bool -> Bool -> Bool) -> ()
d_Associative_30 = erased
-- Data.Bool.Properties._.Commutative
d_Commutative_34 :: (Bool -> Bool -> Bool) -> ()
d_Commutative_34 = erased
-- Data.Bool.Properties._.Conical
d_Conical_40 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_Conical_40 = erased
-- Data.Bool.Properties._.Idempotent
d_Idempotent_44 :: (Bool -> Bool -> Bool) -> ()
d_Idempotent_44 = erased
-- Data.Bool.Properties._.Identity
d_Identity_50 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_Identity_50 = erased
-- Data.Bool.Properties._.Inverse
d_Inverse_54 ::
  Bool -> (Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_Inverse_54 = erased
-- Data.Bool.Properties._.Involutive
d_Involutive_58 :: (Bool -> Bool) -> ()
d_Involutive_58 = erased
-- Data.Bool.Properties._.LeftConical
d_LeftConical_68 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_LeftConical_68 = erased
-- Data.Bool.Properties._.LeftIdentity
d_LeftIdentity_76 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_LeftIdentity_76 = erased
-- Data.Bool.Properties._.LeftInverse
d_LeftInverse_78 ::
  Bool -> (Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_LeftInverse_78 = erased
-- Data.Bool.Properties._.LeftZero
d_LeftZero_84 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_LeftZero_84 = erased
-- Data.Bool.Properties._.RightConical
d_RightConical_98 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_RightConical_98 = erased
-- Data.Bool.Properties._.RightIdentity
d_RightIdentity_106 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_RightIdentity_106 = erased
-- Data.Bool.Properties._.RightInverse
d_RightInverse_108 ::
  Bool -> (Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_RightInverse_108 = erased
-- Data.Bool.Properties._.RightZero
d_RightZero_114 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_RightZero_114 = erased
-- Data.Bool.Properties._.Selective
d_Selective_116 :: (Bool -> Bool -> Bool) -> ()
d_Selective_116 = erased
-- Data.Bool.Properties._.Zero
d_Zero_134 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_Zero_134 = erased
-- Data.Bool.Properties._.IsAbelianGroup
d_IsAbelianGroup_138 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsAlternativeMagma
d_IsAlternativeMagma_140 a0 = ()
-- Data.Bool.Properties._.IsBand
d_IsBand_142 a0 = ()
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring
d_IsCancellativeCommutativeSemiring_144 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsCommutativeBand
d_IsCommutativeBand_146 a0 = ()
-- Data.Bool.Properties._.IsCommutativeMagma
d_IsCommutativeMagma_148 a0 = ()
-- Data.Bool.Properties._.IsCommutativeMonoid
d_IsCommutativeMonoid_150 a0 a1 = ()
-- Data.Bool.Properties._.IsCommutativeRing
d_IsCommutativeRing_152 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsCommutativeSemigroup
d_IsCommutativeSemigroup_154 a0 = ()
-- Data.Bool.Properties._.IsCommutativeSemiring
d_IsCommutativeSemiring_156 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne
d_IsCommutativeSemiringWithoutOne_158 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsFlexibleMagma
d_IsFlexibleMagma_160 a0 = ()
-- Data.Bool.Properties._.IsGroup
d_IsGroup_162 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_164 a0 a1 = ()
-- Data.Bool.Properties._.IsIdempotentMagma
d_IsIdempotentMagma_166 a0 = ()
-- Data.Bool.Properties._.IsIdempotentMonoid
d_IsIdempotentMonoid_168 a0 a1 = ()
-- Data.Bool.Properties._.IsIdempotentSemiring
d_IsIdempotentSemiring_170 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsInvertibleMagma
d_IsInvertibleMagma_172 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsInvertibleUnitalMagma
d_IsInvertibleUnitalMagma_174 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsKleeneAlgebra
d_IsKleeneAlgebra_176 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsLeftBolLoop
d_IsLeftBolLoop_178 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsLoop
d_IsLoop_180 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsMagma
d_IsMagma_182 a0 = ()
-- Data.Bool.Properties._.IsMedialMagma
d_IsMedialMagma_184 a0 = ()
-- Data.Bool.Properties._.IsMiddleBolLoop
d_IsMiddleBolLoop_186 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsMonoid
d_IsMonoid_188 a0 a1 = ()
-- Data.Bool.Properties._.IsMoufangLoop
d_IsMoufangLoop_190 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsNearSemiring
d_IsNearSemiring_192 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsNearring
d_IsNearring_194 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsNonAssociativeRing
d_IsNonAssociativeRing_196 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsQuasigroup
d_IsQuasigroup_198 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsQuasiring
d_IsQuasiring_200 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsRightBolLoop
d_IsRightBolLoop_202 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsRing
d_IsRing_204 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsRingWithoutOne
d_IsRingWithoutOne_206 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsSelectiveMagma
d_IsSelectiveMagma_208 a0 = ()
-- Data.Bool.Properties._.IsSemigroup
d_IsSemigroup_210 a0 = ()
-- Data.Bool.Properties._.IsSemimedialMagma
d_IsSemimedialMagma_212 a0 = ()
-- Data.Bool.Properties._.IsSemiring
d_IsSemiring_214 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_216 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsSemiringWithoutOne
d_IsSemiringWithoutOne_218 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsUnitalMagma
d_IsUnitalMagma_222 a0 a1 = ()
-- Data.Bool.Properties._.IsAbelianGroup.assoc
d_assoc_228 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_228 = erased
-- Data.Bool.Properties._.IsAbelianGroup.comm
d_comm_230 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_230 = erased
-- Data.Bool.Properties._.IsAbelianGroup.identity
d_identity_232 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_232 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)))
-- Data.Bool.Properties._.IsAbelianGroup.inverse
d_inverse_238 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_238 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1052
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))
-- Data.Bool.Properties._.IsAbelianGroup.isEquivalence
d_isEquivalence_250 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_250 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)))))
-- Data.Bool.Properties._.IsAbelianGroup.isGroup
d_isGroup_252 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_252 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)
-- Data.Bool.Properties._.IsAbelianGroup.isMagma
d_isMagma_258 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_258 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))))
-- Data.Bool.Properties._.IsAbelianGroup.isMonoid
d_isMonoid_260 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_260 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))
-- Data.Bool.Properties._.IsAbelianGroup.isSemigroup
d_isSemigroup_264 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_264 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)))
-- Data.Bool.Properties._.IsAbelianGroup.⁻¹-cong
d_'8315''185''45'cong_282 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_282 = erased
-- Data.Bool.Properties._.IsAbelianGroup.∙-cong
d_'8729''45'cong_284 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_284 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.alter
d_alter_292 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alter_292 v0
  = coe MAlonzo.Code.Algebra.Structures.d_alter_294 (coe v0)
-- Data.Bool.Properties._.IsAlternativeMagma.isEquivalence
d_isEquivalence_298 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_298 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_292 (coe v0))
-- Data.Bool.Properties._.IsAlternativeMagma.isMagma
d_isMagma_300 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_300 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_292 (coe v0)
-- Data.Bool.Properties._.IsAlternativeMagma.∙-cong
d_'8729''45'cong_314 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_284 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_314 = erased
-- Data.Bool.Properties._.IsBand.assoc
d_assoc_322 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_322 = erased
-- Data.Bool.Properties._.IsBand.idem
d_idem_324 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_324 = erased
-- Data.Bool.Properties._.IsBand.isEquivalence
d_isEquivalence_326 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_326 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v0)))
-- Data.Bool.Properties._.IsBand.isMagma
d_isMagma_328 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_328 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v0))
-- Data.Bool.Properties._.IsBand.isSemigroup
d_isSemigroup_332 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_332 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v0)
-- Data.Bool.Properties._.IsBand.∙-cong
d_'8729''45'cong_344 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_344 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-assoc
d_'42''45'assoc_352 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_352 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-cancelˡ-nonZero
d_'42''45'cancel'737''45'nonZero_356 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Bool ->
  Bool ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45'nonZero_356 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-comm
d_'42''45'comm_358 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_358 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-cong
d_'42''45'cong_360 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_360 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-identity
d_'42''45'identity_366 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_366 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
               (coe v0))))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.assoc
d_assoc_384 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_384 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.comm
d_comm_386 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_386 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.∙-cong
d_'8729''45'cong_388 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_388 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.identity
d_identity_394 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_394 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                     (coe v0))))))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_402 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_402 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
               (coe v0))))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isMagma
d_isMagma_406 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_406 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                        (coe v0)))))))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isMonoid
d_isMonoid_408 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_408 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                  (coe v0)))))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isSemigroup
d_isSemigroup_410 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_410 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                     (coe v0))))))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.distrib
d_distrib_414 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_414 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
               (coe v0))))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiring
d_isCommutativeSemiring_420 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_isCommutativeSemiring_420 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
      (coe v0)
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isEquivalence
d_isEquivalence_424 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_424 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                           (coe v0))))))))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isSemiring
d_isSemiring_430 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_430 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
         (coe v0))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_432 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_432 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
            (coe v0)))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.zero
d_zero_446 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_446 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1586
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
            (coe v0)))
-- Data.Bool.Properties._.IsCommutativeBand.assoc
d_assoc_454 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_454 = erased
-- Data.Bool.Properties._.IsCommutativeBand.comm
d_comm_456 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_456 = erased
-- Data.Bool.Properties._.IsCommutativeBand.idem
d_idem_458 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_458 = erased
-- Data.Bool.Properties._.IsCommutativeBand.isBand
d_isBand_460 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_460 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)
-- Data.Bool.Properties._.IsCommutativeBand.isEquivalence
d_isEquivalence_466 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_466 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))))
-- Data.Bool.Properties._.IsCommutativeBand.isMagma
d_isMagma_468 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_468 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeBand.isSemigroup
d_isSemigroup_472 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_472 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))
-- Data.Bool.Properties._.IsCommutativeBand.∙-cong
d_'8729''45'cong_484 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_484 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.comm
d_comm_492 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_492 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.isEquivalence
d_isEquivalence_494 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_494 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_220 (coe v0))
-- Data.Bool.Properties._.IsCommutativeMagma.isMagma
d_isMagma_496 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_496 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_220 (coe v0)
-- Data.Bool.Properties._.IsCommutativeMagma.∙-cong
d_'8729''45'cong_510 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_510 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.assoc
d_assoc_518 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_518 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.comm
d_comm_520 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_520 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.identity
d_identity_522 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_522 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0))
-- Data.Bool.Properties._.IsCommutativeMonoid.isEquivalence
d_isEquivalence_532 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_532 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0))))
-- Data.Bool.Properties._.IsCommutativeMonoid.isMagma
d_isMagma_534 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_534 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeMonoid.isMonoid
d_isMonoid_536 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_536 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0)
-- Data.Bool.Properties._.IsCommutativeMonoid.isSemigroup
d_isSemigroup_540 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_540 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0))
-- Data.Bool.Properties._.IsCommutativeMonoid.∙-cong
d_'8729''45'cong_554 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_554 = erased
-- Data.Bool.Properties._.IsCommutativeRing.*-assoc
d_'42''45'assoc_564 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_564 = erased
-- Data.Bool.Properties._.IsCommutativeRing.*-comm
d_'42''45'comm_566 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_566 = erased
-- Data.Bool.Properties._.IsCommutativeRing.*-cong
d_'42''45'cong_568 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_568 = erased
-- Data.Bool.Properties._.IsCommutativeRing.*-identity
d_'42''45'identity_574 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_574 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2678
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0))
-- Data.Bool.Properties._.IsCommutativeRing.assoc
d_assoc_592 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_592 = erased
-- Data.Bool.Properties._.IsCommutativeRing.comm
d_comm_594 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_594 = erased
-- Data.Bool.Properties._.IsCommutativeRing.∙-cong
d_'8729''45'cong_596 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_596 = erased
-- Data.Bool.Properties._.IsCommutativeRing.identity
d_identity_602 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_602 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_602 v5
du_identity_602 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_602 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_698
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                  (coe v1)))))
-- Data.Bool.Properties._.IsCommutativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_608 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_608 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0))
-- Data.Bool.Properties._.IsCommutativeRing.isGroup
d_isGroup_616 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_616 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_616 v5
du_isGroup_616 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
du_isGroup_616 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
            (coe v1)))
-- Data.Bool.Properties._.IsCommutativeRing.isMagma
d_isMagma_622 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_622 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_622 v5
du_isMagma_622 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_622 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                     (coe v1))))))
-- Data.Bool.Properties._.IsCommutativeRing.isMonoid
d_isMonoid_624 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_624 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_624 v5
du_isMonoid_624 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_isMonoid_624 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
               (coe v1))))
-- Data.Bool.Properties._.IsCommutativeRing.isSemigroup
d_isSemigroup_626 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_626 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_626 v5
du_isSemigroup_626 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_626 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                  (coe v1)))))
-- Data.Bool.Properties._.IsCommutativeRing.⁻¹-cong
d_'8315''185''45'cong_630 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_630 = erased
-- Data.Bool.Properties._.IsCommutativeRing.inverse
d_inverse_632 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_632 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_632 v5
du_inverse_632 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_632 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_inverse_1052
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
               (coe v1))))
-- Data.Bool.Properties._.IsCommutativeRing.distrib
d_distrib_638 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_638 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2680
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0))
-- Data.Bool.Properties._.IsCommutativeRing.isEquivalence
d_isEquivalence_648 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_648 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_648 v5
du_isEquivalence_648 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_648 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                        (coe v1)))))))
-- Data.Bool.Properties._.IsCommutativeRing.isRing
d_isRing_654 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
d_isRing_654 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0)
-- Data.Bool.Properties._.IsCommutativeRing.isRingWithoutOne
d_isRingWithoutOne_656 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286
d_isRingWithoutOne_656 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isRingWithoutOne_656 v5
du_isRingWithoutOne_656 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286
du_isRingWithoutOne_656 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2682
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemigroup.assoc
d_assoc_686 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_686 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.comm
d_comm_688 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_688 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.isEquivalence
d_isEquivalence_692 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_692 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeSemigroup.isMagma
d_isMagma_694 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_694 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_698 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_698 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v0)
-- Data.Bool.Properties._.IsCommutativeSemigroup.∙-cong
d_'8729''45'cong_710 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_710 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.*-assoc
d_'42''45'assoc_718 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_718 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.*-comm
d_'42''45'comm_720 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_720 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.*-cong
d_'42''45'cong_722 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_722 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.*-identity
d_'42''45'identity_728 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_728 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeSemiring.assoc
d_assoc_746 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_746 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.comm
d_comm_748 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_748 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.∙-cong
d_'8729''45'cong_750 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_750 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.identity
d_identity_756 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_756 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))))
-- Data.Bool.Properties._.IsCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_764 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_764 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeSemiring.isMagma
d_isMagma_768 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_768 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0))))))
-- Data.Bool.Properties._.IsCommutativeSemiring.isMonoid
d_isMonoid_770 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_770 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0))))
-- Data.Bool.Properties._.IsCommutativeSemiring.isSemigroup
d_isSemigroup_772 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_772 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))))
-- Data.Bool.Properties._.IsCommutativeSemiring.distrib
d_distrib_776 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_776 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeSemiring.isEquivalence
d_isEquivalence_784 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_784 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))))))
-- Data.Bool.Properties._.IsCommutativeSemiring.isSemiring
d_isSemiring_790 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_790 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)
-- Data.Bool.Properties._.IsCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_792 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_792 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemiring.zero
d_zero_806 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_806 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1586
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.*-assoc
d_'42''45'assoc_818 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_818 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.*-comm
d_'42''45'comm_820 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_820 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.*-cong
d_'42''45'cong_822 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_822 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.comm
d_comm_836 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_836 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_840 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_840 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1316
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
         (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isMonoid
d_isMonoid_844 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_844 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1316
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
            (coe v0)))
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.distrib
d_distrib_848 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_848 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1322
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
         (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne
d_isSemiringWithoutOne_856 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_856 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
      (coe v0)
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.zero
d_zero_870 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_870 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1324
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
         (coe v0))
-- Data.Bool.Properties._.IsFlexibleMagma.flex
d_flex_878 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_324 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flex_878 = erased
-- Data.Bool.Properties._.IsFlexibleMagma.isEquivalence
d_isEquivalence_880 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_324 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_880 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_332 (coe v0))
-- Data.Bool.Properties._.IsFlexibleMagma.isMagma
d_isMagma_882 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_324 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_882 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_332 (coe v0)
-- Data.Bool.Properties._.IsFlexibleMagma.∙-cong
d_'8729''45'cong_896 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_324 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_896 = erased
-- Data.Bool.Properties._.IsGroup.assoc
d_assoc_910 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_910 = erased
-- Data.Bool.Properties._.IsGroup.identity
d_identity_912 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_912 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0))
-- Data.Bool.Properties._.IsGroup.inverse
d_inverse_918 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_918 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1052 (coe v0)
-- Data.Bool.Properties._.IsGroup.isEquivalence
d_isEquivalence_924 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_924 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0))))
-- Data.Bool.Properties._.IsGroup.isMagma
d_isMagma_930 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_930 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0)))
-- Data.Bool.Properties._.IsGroup.isMonoid
d_isMonoid_932 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_932 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0)
-- Data.Bool.Properties._.IsGroup.isSemigroup
d_isSemigroup_936 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_936 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0))
-- Data.Bool.Properties._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_954 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_954 = erased
-- Data.Bool.Properties._.IsGroup.∙-cong
d_'8729''45'cong_956 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_956 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.assoc
d_assoc_964 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_964 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.comm
d_comm_966 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_966 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.idem
d_idem_968 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_968 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.identity
d_identity_970 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_970 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe v0)))
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_982 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_isCommutativeMonoid_982 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862 (coe v0)
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isEquivalence
d_isEquivalence_986 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_986 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                  (coe v0)))))
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isMagma
d_isMagma_990 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_990 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
               (coe v0))))
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isMonoid
d_isMonoid_992 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_992 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862 (coe v0))
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isSemigroup
d_isSemigroup_996 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_996 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe v0)))
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.∙-cong
d_'8729''45'cong_1010 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1010 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.idem
d_idem_1018 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_248 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1018 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.isEquivalence
d_isEquivalence_1020 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1020 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_256 (coe v0))
-- Data.Bool.Properties._.IsIdempotentMagma.isMagma
d_isMagma_1022 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_248 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1022 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_256 (coe v0)
-- Data.Bool.Properties._.IsIdempotentMagma.∙-cong
d_'8729''45'cong_1036 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_248 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1036 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.assoc
d_assoc_1044 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1044 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.idem
d_idem_1046 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1046 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.identity
d_identity_1048 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1048 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0))
-- Data.Bool.Properties._.IsIdempotentMonoid.isEquivalence
d_isEquivalence_1056 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1056 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0))))
-- Data.Bool.Properties._.IsIdempotentMonoid.isMagma
d_isMagma_1058 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1058 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0)))
-- Data.Bool.Properties._.IsIdempotentMonoid.isMonoid
d_isMonoid_1060 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_1060 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0)
-- Data.Bool.Properties._.IsIdempotentMonoid.isSemigroup
d_isSemigroup_1064 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1064 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0))
-- Data.Bool.Properties._.IsIdempotentMonoid.∙-cong
d_'8729''45'cong_1078 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1078 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.*-assoc
d_'42''45'assoc_1086 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1086 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.*-cong
d_'42''45'cong_1088 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1088 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.*-identity
d_'42''45'identity_1094 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1094 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))
-- Data.Bool.Properties._.IsIdempotentSemiring.assoc
d_assoc_1106 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1106 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.comm
d_comm_1108 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1108 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.∙-cong
d_'8729''45'cong_1110 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1110 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.+-idem
d_'43''45'idem_1116 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1116 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.identity
d_identity_1118 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1118 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))))
-- Data.Bool.Properties._.IsIdempotentSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1130 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1130 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))
-- Data.Bool.Properties._.IsIdempotentSemiring.isMagma
d_isMagma_1138 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1138 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0))))))
-- Data.Bool.Properties._.IsIdempotentSemiring.isMonoid
d_isMonoid_1140 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_1140 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0))))
-- Data.Bool.Properties._.IsIdempotentSemiring.isSemigroup
d_isSemigroup_1142 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1142 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))))
-- Data.Bool.Properties._.IsIdempotentSemiring.distrib
d_distrib_1146 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1146 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))
-- Data.Bool.Properties._.IsIdempotentSemiring.isEquivalence
d_isEquivalence_1152 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1152 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))))))
-- Data.Bool.Properties._.IsIdempotentSemiring.isSemiring
d_isSemiring_1158 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_1158 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)
-- Data.Bool.Properties._.IsIdempotentSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1160 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_1160 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0))
-- Data.Bool.Properties._.IsIdempotentSemiring.zero
d_zero_1174 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1174 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1586
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0))
-- Data.Bool.Properties._.IsInvertibleMagma.inverse
d_inverse_1182 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1182 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_940 (coe v0)
-- Data.Bool.Properties._.IsInvertibleMagma.isEquivalence
d_isEquivalence_1188 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1188 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_938 (coe v0))
-- Data.Bool.Properties._.IsInvertibleMagma.isMagma
d_isMagma_1190 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1190 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_938 (coe v0)
-- Data.Bool.Properties._.IsInvertibleMagma.⁻¹-cong
d_'8315''185''45'cong_1204 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1204 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.∙-cong
d_'8729''45'cong_1206 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1206 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.identity
d_identity_1214 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1214 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_990 (coe v0)
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.inverse
d_inverse_1220 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1220 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_940
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_988 (coe v0))
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.isEquivalence
d_isEquivalence_1226 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1226 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_938
         (coe
            MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_988 (coe v0)))
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.isInvertibleMagma
d_isInvertibleMagma_1228 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924
d_isInvertibleMagma_1228 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_988 (coe v0)
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.isMagma
d_isMagma_1230 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1230 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_938
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_988 (coe v0))
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.⁻¹-cong
d_'8315''185''45'cong_1246 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1246 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.∙-cong
d_'8729''45'cong_1248 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1248 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.*-assoc
d_'42''45'assoc_1256 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1256 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.*-cong
d_'42''45'cong_1258 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1258 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.*-identity
d_'42''45'identity_1264 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1264 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
               (coe v0))))
-- Data.Bool.Properties._.IsKleeneAlgebra.assoc
d_assoc_1276 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1276 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.comm
d_comm_1278 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1278 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.∙-cong
d_'8729''45'cong_1280 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1280 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.+-idem
d_'43''45'idem_1286 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1286 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.identity
d_identity_1288 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1288 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                     (coe v0))))))
-- Data.Bool.Properties._.IsKleeneAlgebra.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1300 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1300 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
               (coe v0))))
-- Data.Bool.Properties._.IsKleeneAlgebra.isMagma
d_isMagma_1308 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1308 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                        (coe v0)))))))
-- Data.Bool.Properties._.IsKleeneAlgebra.isMonoid
d_isMonoid_1310 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_1310 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                  (coe v0)))))
-- Data.Bool.Properties._.IsKleeneAlgebra.isSemigroup
d_isSemigroup_1312 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1312 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                     (coe v0))))))
-- Data.Bool.Properties._.IsKleeneAlgebra.distrib
d_distrib_1316 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1316 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
               (coe v0))))
-- Data.Bool.Properties._.IsKleeneAlgebra.isEquivalence
d_isEquivalence_1322 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1322 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                           (coe v0))))))))
-- Data.Bool.Properties._.IsKleeneAlgebra.isIdempotentSemiring
d_isIdempotentSemiring_1324 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922
d_isIdempotentSemiring_1324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
      (coe v0)
-- Data.Bool.Properties._.IsKleeneAlgebra.isSemiring
d_isSemiring_1330 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_1330 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
         (coe v0))
-- Data.Bool.Properties._.IsKleeneAlgebra.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1332 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_1332 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
            (coe v0)))
-- Data.Bool.Properties._.IsKleeneAlgebra.starDestructive
d_starDestructive_1342 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starDestructive_1342 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_starDestructive_2066 (coe v0)
-- Data.Bool.Properties._.IsKleeneAlgebra.starExpansive
d_starExpansive_1348 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starExpansive_1348 v0
  = coe MAlonzo.Code.Algebra.Structures.d_starExpansive_2064 (coe v0)
-- Data.Bool.Properties._.IsKleeneAlgebra.zero
d_zero_1358 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1358 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1586
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
            (coe v0)))
-- Data.Bool.Properties._.IsLeftBolLoop.//-cong
d_'47''47''45'cong_1366 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1366 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.\\-cong
d_'92''92''45'cong_1372 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1372 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.identity
d_identity_1378 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1378 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3042
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0))
-- Data.Bool.Properties._.IsLeftBolLoop.isEquivalence
d_isEquivalence_1384 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1384 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0))))
-- Data.Bool.Properties._.IsLeftBolLoop.isLoop
d_isLoop_1386 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_1386 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0)
-- Data.Bool.Properties._.IsLeftBolLoop.isMagma
d_isMagma_1388 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1388 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0)))
-- Data.Bool.Properties._.IsLeftBolLoop.isQuasigroup
d_isQuasigroup_1392 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_1392 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0))
-- Data.Bool.Properties._.IsLeftBolLoop.leftBol
d_leftBol_1394 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1394 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.leftDivides
d_leftDivides_1396 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1396 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0)))
-- Data.Bool.Properties._.IsLeftBolLoop.rightDivides
d_rightDivides_1406 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1406 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0)))
-- Data.Bool.Properties._.IsLeftBolLoop.∙-cong
d_'8729''45'cong_1418 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1418 = erased
-- Data.Bool.Properties._.IsLoop.//-cong
d_'47''47''45'cong_1426 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1426 = erased
-- Data.Bool.Properties._.IsLoop.\\-cong
d_'92''92''45'cong_1432 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1432 = erased
-- Data.Bool.Properties._.IsLoop.identity
d_identity_1438 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1438 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_3042 (coe v0)
-- Data.Bool.Properties._.IsLoop.isEquivalence
d_isEquivalence_1444 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1444 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0)))
-- Data.Bool.Properties._.IsLoop.isMagma
d_isMagma_1446 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1446 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0))
-- Data.Bool.Properties._.IsLoop.isQuasigroup
d_isQuasigroup_1450 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_1450 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0)
-- Data.Bool.Properties._.IsLoop.leftDivides
d_leftDivides_1452 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1452 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0))
-- Data.Bool.Properties._.IsLoop.rightDivides
d_rightDivides_1462 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1462 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0))
-- Data.Bool.Properties._.IsLoop.∙-cong
d_'8729''45'cong_1474 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1474 = erased
-- Data.Bool.Properties._.IsMagma.isEquivalence
d_isEquivalence_1482 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1482 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v0)
-- Data.Bool.Properties._.IsMagma.∙-cong
d_'8729''45'cong_1496 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1496 = erased
-- Data.Bool.Properties._.IsMedialMagma.isEquivalence
d_isEquivalence_1504 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_360 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1504 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_368 (coe v0))
-- Data.Bool.Properties._.IsMedialMagma.isMagma
d_isMagma_1506 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_360 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1506 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_368 (coe v0)
-- Data.Bool.Properties._.IsMedialMagma.medial
d_medial_1510 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_360 ->
  Bool ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_medial_1510 = erased
-- Data.Bool.Properties._.IsMedialMagma.∙-cong
d_'8729''45'cong_1522 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_360 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1522 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.//-cong
d_'47''47''45'cong_1530 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1530 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.\\-cong
d_'92''92''45'cong_1536 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1536 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.identity
d_identity_1542 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1542 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3042
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0))
-- Data.Bool.Properties._.IsMiddleBolLoop.isEquivalence
d_isEquivalence_1548 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1548 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0))))
-- Data.Bool.Properties._.IsMiddleBolLoop.isLoop
d_isLoop_1550 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_1550 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0)
-- Data.Bool.Properties._.IsMiddleBolLoop.isMagma
d_isMagma_1552 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1552 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0)))
-- Data.Bool.Properties._.IsMiddleBolLoop.isQuasigroup
d_isQuasigroup_1556 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_1556 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0))
-- Data.Bool.Properties._.IsMiddleBolLoop.leftDivides
d_leftDivides_1558 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1558 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0)))
-- Data.Bool.Properties._.IsMiddleBolLoop.middleBol
d_middleBol_1564 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_middleBol_1564 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.rightDivides
d_rightDivides_1570 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1570 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0)))
-- Data.Bool.Properties._.IsMiddleBolLoop.∙-cong
d_'8729''45'cong_1582 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1582 = erased
-- Data.Bool.Properties._.IsMonoid.assoc
d_assoc_1590 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1590 = erased
-- Data.Bool.Properties._.IsMonoid.identity
d_identity_1592 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1592 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_698 (coe v0)
-- Data.Bool.Properties._.IsMonoid.isEquivalence
d_isEquivalence_1598 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1598 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0)))
-- Data.Bool.Properties._.IsMonoid.isMagma
d_isMagma_1600 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1600 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0))
-- Data.Bool.Properties._.IsMonoid.isSemigroup
d_isSemigroup_1604 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1604 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0)
-- Data.Bool.Properties._.IsMonoid.∙-cong
d_'8729''45'cong_1618 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1618 = erased
-- Data.Bool.Properties._.IsMoufangLoop.//-cong
d_'47''47''45'cong_1626 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1626 = erased
-- Data.Bool.Properties._.IsMoufangLoop.\\-cong
d_'92''92''45'cong_1632 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1632 = erased
-- Data.Bool.Properties._.IsMoufangLoop.identical
d_identical_1638 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identical_1638 = erased
-- Data.Bool.Properties._.IsMoufangLoop.identity
d_identity_1640 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1640 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3042
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3118
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0)))
-- Data.Bool.Properties._.IsMoufangLoop.isEquivalence
d_isEquivalence_1646 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1646 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLoop_3118
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0)))))
-- Data.Bool.Properties._.IsMoufangLoop.isLeftBolLoop
d_isLeftBolLoop_1648 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104
d_isLeftBolLoop_1648 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0)
-- Data.Bool.Properties._.IsMoufangLoop.isLoop
d_isLoop_1650 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_1650 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isLoop_3118
      (coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0))
-- Data.Bool.Properties._.IsMoufangLoop.isMagma
d_isMagma_1652 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1652 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3118
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0))))
-- Data.Bool.Properties._.IsMoufangLoop.isQuasigroup
d_isQuasigroup_1656 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_1656 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3118
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0)))
-- Data.Bool.Properties._.IsMoufangLoop.leftBol
d_leftBol_1658 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1658 = erased
-- Data.Bool.Properties._.IsMoufangLoop.leftDivides
d_leftDivides_1660 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1660 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3118
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0))))
-- Data.Bool.Properties._.IsMoufangLoop.rightBol
d_rightBol_1670 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_1670 = erased
-- Data.Bool.Properties._.IsMoufangLoop.rightDivides
d_rightDivides_1672 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1672 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3118
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0))))
-- Data.Bool.Properties._.IsMoufangLoop.∙-cong
d_'8729''45'cong_1684 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1684 = erased
-- Data.Bool.Properties._.IsNearSemiring.*-assoc
d_'42''45'assoc_1692 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1692 = erased
-- Data.Bool.Properties._.IsNearSemiring.*-cong
d_'42''45'cong_1694 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1694 = erased
-- Data.Bool.Properties._.IsNearSemiring.assoc
d_assoc_1704 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1704 = erased
-- Data.Bool.Properties._.IsNearSemiring.∙-cong
d_'8729''45'cong_1706 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1706 = erased
-- Data.Bool.Properties._.IsNearSemiring.identity
d_identity_1712 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1712 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0))
-- Data.Bool.Properties._.IsNearSemiring.isMagma
d_isMagma_1718 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1718 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0)))
-- Data.Bool.Properties._.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1720 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'isMonoid_1720 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0)
-- Data.Bool.Properties._.IsNearSemiring.isSemigroup
d_isSemigroup_1722 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1722 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0))
-- Data.Bool.Properties._.IsNearSemiring.distribʳ
d_distrib'691'_1726 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1726 = erased
-- Data.Bool.Properties._.IsNearSemiring.isEquivalence
d_isEquivalence_1728 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1728 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0))))
-- Data.Bool.Properties._.IsNearSemiring.zeroˡ
d_zero'737'_1742 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1742 = erased
-- Data.Bool.Properties._.IsNearring.*-assoc
d_'42''45'assoc_1746 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1746 = erased
-- Data.Bool.Properties._.IsNearring.*-cong
d_'42''45'cong_1748 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1748 = erased
-- Data.Bool.Properties._.IsNearring.*-identity
d_'42''45'identity_1754 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1754 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2208
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))
-- Data.Bool.Properties._.IsNearring.assoc
d_assoc_1766 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1766 = erased
-- Data.Bool.Properties._.IsNearring.∙-cong
d_'8729''45'cong_1768 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1768 = erased
-- Data.Bool.Properties._.IsNearring.identity
d_identity_1774 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1774 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0)))
-- Data.Bool.Properties._.IsNearring.+-inverse
d_'43''45'inverse_1780 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_1780 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'inverse_2558 (coe v0)
-- Data.Bool.Properties._.IsNearring.isMagma
d_isMagma_1786 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1786 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
            (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))))
-- Data.Bool.Properties._.IsNearring.+-isMonoid
d_'43''45'isMonoid_1788 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'isMonoid_1788 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))
-- Data.Bool.Properties._.IsNearring.isSemigroup
d_isSemigroup_1790 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1790 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0)))
-- Data.Bool.Properties._.IsNearring.distrib
d_distrib_1794 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1794 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2210
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))
-- Data.Bool.Properties._.IsNearring.isEquivalence
d_isEquivalence_1804 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1804 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0)))))
-- Data.Bool.Properties._.IsNearring.isQuasiring
d_isQuasiring_1808 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180
d_isQuasiring_1808 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0)
-- Data.Bool.Properties._.IsNearring.zero
d_zero_1820 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1820 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_2212
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))
-- Data.Bool.Properties._.IsNearring.⁻¹-cong
d_'8315''185''45'cong_1826 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1826 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.*-cong
d_'42''45'cong_1832 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1832 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.*-identity
d_'42''45'identity_1838 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1838 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2434 (coe v0)
-- Data.Bool.Properties._.IsNonAssociativeRing.assoc
d_assoc_1848 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1848 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.comm
d_comm_1850 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1850 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.∙-cong
d_'8729''45'cong_1852 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1852 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.identity
d_identity_1858 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1858 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
               (coe v0))))
-- Data.Bool.Properties._.IsNonAssociativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_1864 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_1864 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
      (coe v0)
-- Data.Bool.Properties._.IsNonAssociativeRing.isGroup
d_isGroup_1872 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_1872 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1144
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
         (coe v0))
-- Data.Bool.Properties._.IsNonAssociativeRing.isMagma
d_isMagma_1878 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1878 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
                  (coe v0)))))
-- Data.Bool.Properties._.IsNonAssociativeRing.isMonoid
d_isMonoid_1880 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_1880 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
            (coe v0)))
-- Data.Bool.Properties._.IsNonAssociativeRing.isSemigroup
d_isSemigroup_1882 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1882 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
               (coe v0))))
-- Data.Bool.Properties._.IsNonAssociativeRing.⁻¹-cong
d_'8315''185''45'cong_1886 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1886 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.inverse
d_inverse_1888 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1888 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1052
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
            (coe v0)))
-- Data.Bool.Properties._.IsNonAssociativeRing.distrib
d_distrib_1894 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1894 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2436 (coe v0)
-- Data.Bool.Properties._.IsNonAssociativeRing.isEquivalence
d_isEquivalence_1900 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1900 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
                     (coe v0))))))
-- Data.Bool.Properties._.IsNonAssociativeRing.zero
d_zero_1918 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1918 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2438 (coe v0)
-- Data.Bool.Properties._.IsQuasigroup.//-cong
d_'47''47''45'cong_1926 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1926 = erased
-- Data.Bool.Properties._.IsQuasigroup.\\-cong
d_'92''92''45'cong_1932 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1932 = erased
-- Data.Bool.Properties._.IsQuasigroup.isEquivalence
d_isEquivalence_1938 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1938 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v0))
-- Data.Bool.Properties._.IsQuasigroup.isMagma
d_isMagma_1940 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1940 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v0)
-- Data.Bool.Properties._.IsQuasigroup.leftDivides
d_leftDivides_1944 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1944 v0
  = coe MAlonzo.Code.Algebra.Structures.d_leftDivides_2968 (coe v0)
-- Data.Bool.Properties._.IsQuasigroup.rightDivides
d_rightDivides_1954 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1954 v0
  = coe MAlonzo.Code.Algebra.Structures.d_rightDivides_2970 (coe v0)
-- Data.Bool.Properties._.IsQuasigroup.∙-cong
d_'8729''45'cong_1966 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1966 = erased
-- Data.Bool.Properties._.IsQuasiring.*-assoc
d_'42''45'assoc_1974 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1974 = erased
-- Data.Bool.Properties._.IsQuasiring.*-cong
d_'42''45'cong_1976 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1976 = erased
-- Data.Bool.Properties._.IsQuasiring.*-identity
d_'42''45'identity_1982 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1982 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2208 (coe v0)
-- Data.Bool.Properties._.IsQuasiring.assoc
d_assoc_1994 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1994 = erased
-- Data.Bool.Properties._.IsQuasiring.∙-cong
d_'8729''45'cong_1996 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1996 = erased
-- Data.Bool.Properties._.IsQuasiring.identity
d_identity_2002 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2002 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0))
-- Data.Bool.Properties._.IsQuasiring.isMagma
d_isMagma_2008 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2008 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0)))
-- Data.Bool.Properties._.IsQuasiring.+-isMonoid
d_'43''45'isMonoid_2010 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'isMonoid_2010 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0)
-- Data.Bool.Properties._.IsQuasiring.isSemigroup
d_isSemigroup_2012 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2012 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0))
-- Data.Bool.Properties._.IsQuasiring.distrib
d_distrib_2016 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2016 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2210 (coe v0)
-- Data.Bool.Properties._.IsQuasiring.isEquivalence
d_isEquivalence_2026 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2026 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0))))
-- Data.Bool.Properties._.IsQuasiring.zero
d_zero_2040 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2040 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2212 (coe v0)
-- Data.Bool.Properties._.IsRightBolLoop.//-cong
d_'47''47''45'cong_2048 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_2048 = erased
-- Data.Bool.Properties._.IsRightBolLoop.\\-cong
d_'92''92''45'cong_2054 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_2054 = erased
-- Data.Bool.Properties._.IsRightBolLoop.identity
d_identity_2060 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2060 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3042
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0))
-- Data.Bool.Properties._.IsRightBolLoop.isEquivalence
d_isEquivalence_2066 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2066 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0))))
-- Data.Bool.Properties._.IsRightBolLoop.isLoop
d_isLoop_2068 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_2068 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)
-- Data.Bool.Properties._.IsRightBolLoop.isMagma
d_isMagma_2070 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2070 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)))
-- Data.Bool.Properties._.IsRightBolLoop.isQuasigroup
d_isQuasigroup_2074 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_2074 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0))
-- Data.Bool.Properties._.IsRightBolLoop.leftDivides
d_leftDivides_2076 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2076 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)))
-- Data.Bool.Properties._.IsRightBolLoop.rightBol
d_rightBol_2086 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_2086 = erased
-- Data.Bool.Properties._.IsRightBolLoop.rightDivides
d_rightDivides_2088 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2088 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)))
-- Data.Bool.Properties._.IsRightBolLoop.∙-cong
d_'8729''45'cong_2100 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2100 = erased
-- Data.Bool.Properties._.IsRing.*-assoc
d_'42''45'assoc_2110 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2110 = erased
-- Data.Bool.Properties._.IsRing.*-cong
d_'42''45'cong_2112 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2112 = erased
-- Data.Bool.Properties._.IsRing.*-identity
d_'42''45'identity_2118 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2118 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2678 (coe v0)
-- Data.Bool.Properties._.IsRing.assoc
d_assoc_2130 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2130 = erased
-- Data.Bool.Properties._.IsRing.comm
d_comm_2132 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2132 = erased
-- Data.Bool.Properties._.IsRing.∙-cong
d_'8729''45'cong_2134 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2134 = erased
-- Data.Bool.Properties._.IsRing.identity
d_identity_2140 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2140 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_2140 v5
du_identity_2140 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_2140 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
               (coe v0))))
-- Data.Bool.Properties._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2146 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2146 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
      (coe v0)
-- Data.Bool.Properties._.IsRing.isGroup
d_isGroup_2154 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_2154 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_2154 v5
du_isGroup_2154 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
du_isGroup_2154 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1144
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
         (coe v0))
-- Data.Bool.Properties._.IsRing.isMagma
d_isMagma_2160 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2160 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_2160 v5
du_isMagma_2160 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_2160 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                  (coe v0)))))
-- Data.Bool.Properties._.IsRing.isMonoid
d_isMonoid_2162 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2162 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_2162 v5
du_isMonoid_2162 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_isMonoid_2162 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
            (coe v0)))
-- Data.Bool.Properties._.IsRing.isSemigroup
d_isSemigroup_2164 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2164 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_2164 v5
du_isSemigroup_2164 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_2164 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
               (coe v0))))
-- Data.Bool.Properties._.IsRing.⁻¹-cong
d_'8315''185''45'cong_2168 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2168 = erased
-- Data.Bool.Properties._.IsRing.inverse
d_inverse_2170 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2170 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_2170 v5
du_inverse_2170 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_2170 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1052
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
            (coe v0)))
-- Data.Bool.Properties._.IsRing.distrib
d_distrib_2176 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2176 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2680 (coe v0)
-- Data.Bool.Properties._.IsRing.isEquivalence
d_isEquivalence_2182 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2182 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_2182 v5
du_isEquivalence_2182 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2182 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                     (coe v0))))))
-- Data.Bool.Properties._.IsRing.isRingWithoutOne
d_isRingWithoutOne_2188 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286
d_isRingWithoutOne_2188 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2682 v5
-- Data.Bool.Properties._.IsRingWithoutOne.*-assoc
d_'42''45'assoc_2220 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2220 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.*-cong
d_'42''45'cong_2222 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2222 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.assoc
d_assoc_2232 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2232 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.comm
d_comm_2234 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2234 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.∙-cong
d_'8729''45'cong_2236 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2236 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.identity
d_identity_2242 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2242 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
               (coe v0))))
-- Data.Bool.Properties._.IsRingWithoutOne.+-isAbelianGroup
d_'43''45'isAbelianGroup_2248 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2248 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
      (coe v0)
-- Data.Bool.Properties._.IsRingWithoutOne.isGroup
d_isGroup_2256 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_2256 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1144
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
         (coe v0))
-- Data.Bool.Properties._.IsRingWithoutOne.isMagma
d_isMagma_2262 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2262 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
                  (coe v0)))))
-- Data.Bool.Properties._.IsRingWithoutOne.isMonoid
d_isMonoid_2264 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2264 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
            (coe v0)))
-- Data.Bool.Properties._.IsRingWithoutOne.isSemigroup
d_isSemigroup_2266 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2266 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
               (coe v0))))
-- Data.Bool.Properties._.IsRingWithoutOne.⁻¹-cong
d_'8315''185''45'cong_2270 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2270 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.inverse
d_inverse_2272 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2272 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1052
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
            (coe v0)))
-- Data.Bool.Properties._.IsRingWithoutOne.distrib
d_distrib_2278 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2278 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2310 (coe v0)
-- Data.Bool.Properties._.IsRingWithoutOne.isEquivalence
d_isEquivalence_2284 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2284 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
                     (coe v0))))))
-- Data.Bool.Properties._.IsSelectiveMagma.isEquivalence
d_isEquivalence_2310 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2310 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_444 (coe v0))
-- Data.Bool.Properties._.IsSelectiveMagma.isMagma
d_isMagma_2312 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2312 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_444 (coe v0)
-- Data.Bool.Properties._.IsSelectiveMagma.sel
d_sel_2320 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436 ->
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_2320 v0
  = coe MAlonzo.Code.Algebra.Structures.d_sel_446 (coe v0)
-- Data.Bool.Properties._.IsSelectiveMagma.∙-cong
d_'8729''45'cong_2328 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2328 = erased
-- Data.Bool.Properties._.IsSemigroup.assoc
d_assoc_2336 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2336 = erased
-- Data.Bool.Properties._.IsSemigroup.isEquivalence
d_isEquivalence_2338 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2338 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v0))
-- Data.Bool.Properties._.IsSemigroup.isMagma
d_isMagma_2340 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2340 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v0)
-- Data.Bool.Properties._.IsSemigroup.∙-cong
d_'8729''45'cong_2354 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2354 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.isEquivalence
d_isEquivalence_2362 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2362 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_404 (coe v0))
-- Data.Bool.Properties._.IsSemimedialMagma.isMagma
d_isMagma_2364 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2364 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_404 (coe v0)
-- Data.Bool.Properties._.IsSemimedialMagma.semiMedial
d_semiMedial_2372 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semiMedial_2372 v0
  = coe MAlonzo.Code.Algebra.Structures.d_semiMedial_406 (coe v0)
-- Data.Bool.Properties._.IsSemimedialMagma.∙-cong
d_'8729''45'cong_2384 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_396 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2384 = erased
-- Data.Bool.Properties._.IsSemiring.*-assoc
d_'42''45'assoc_2392 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2392 = erased
-- Data.Bool.Properties._.IsSemiring.*-cong
d_'42''45'cong_2394 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2394 = erased
-- Data.Bool.Properties._.IsSemiring.*-identity
d_'42''45'identity_2400 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2400 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe v0))
-- Data.Bool.Properties._.IsSemiring.assoc
d_assoc_2412 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2412 = erased
-- Data.Bool.Properties._.IsSemiring.comm
d_comm_2414 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2414 = erased
-- Data.Bool.Properties._.IsSemiring.∙-cong
d_'8729''45'cong_2416 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2416 = erased
-- Data.Bool.Properties._.IsSemiring.identity
d_identity_2422 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2422 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe v0))))
-- Data.Bool.Properties._.IsSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2430 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2430 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe v0))
-- Data.Bool.Properties._.IsSemiring.isMagma
d_isMagma_2434 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2434 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe v0)))))
-- Data.Bool.Properties._.IsSemiring.isMonoid
d_isMonoid_2436 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2436 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe v0)))
-- Data.Bool.Properties._.IsSemiring.isSemigroup
d_isSemigroup_2438 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2438 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe v0))))
-- Data.Bool.Properties._.IsSemiring.distrib
d_distrib_2442 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2442 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe v0))
-- Data.Bool.Properties._.IsSemiring.isEquivalence
d_isEquivalence_2448 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2448 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe v0))))))
-- Data.Bool.Properties._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2454 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_2454 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe v0)
-- Data.Bool.Properties._.IsSemiring.zero
d_zero_2468 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2468 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1586 (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2476 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2476 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2478 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2478 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2484 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2484 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494 (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.assoc
d_assoc_2496 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2496 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.comm
d_comm_2498 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2498 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.∙-cong
d_'8729''45'cong_2500 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2500 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.identity
d_identity_2506 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2506 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe v0)))
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2514 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2514 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isMagma
d_isMagma_2518 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2518 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe v0))))
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isMonoid
d_isMonoid_2520 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2520 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe v0))
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isSemigroup
d_isSemigroup_2522 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2522 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe v0)))
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2526 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2526 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1496 (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isEquivalence
d_isEquivalence_2532 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2532 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe v0)))))
-- Data.Bool.Properties._.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_2552 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2552 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.*-cong
d_'42''45'cong_2554 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2554 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.comm
d_comm_2564 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2564 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2568 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2568 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1316
      (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutOne.isMonoid
d_isMonoid_2572 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2572 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1316
         (coe v0))
-- Data.Bool.Properties._.IsSemiringWithoutOne.distrib
d_distrib_2576 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2576 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1322 (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutOne.zero
d_zero_2596 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2596 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1324 (coe v0)
-- Data.Bool.Properties._.IsUnitalMagma.identity
d_identity_2622 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2622 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_654 (coe v0)
-- Data.Bool.Properties._.IsUnitalMagma.isEquivalence
d_isEquivalence_2628 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2628 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_652 (coe v0))
-- Data.Bool.Properties._.IsUnitalMagma.isMagma
d_isMagma_2630 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2630 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_652 (coe v0)
-- Data.Bool.Properties._.IsUnitalMagma.∙-cong
d_'8729''45'cong_2644 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2644 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra
d_IsBooleanAlgebra_2652 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsBoundedJoinSemilattice
d_IsBoundedJoinSemilattice_2654 ::
  (Bool -> Bool -> Bool) -> Bool -> ()
d_IsBoundedJoinSemilattice_2654 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice
d_IsBoundedMeetSemilattice_2656 ::
  (Bool -> Bool -> Bool) -> Bool -> ()
d_IsBoundedMeetSemilattice_2656 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice
d_IsBoundedSemilattice_2658 :: (Bool -> Bool -> Bool) -> Bool -> ()
d_IsBoundedSemilattice_2658 = erased
-- Data.Bool.Properties._.IsDistributiveLattice
d_IsDistributiveLattice_2660 a0 a1 = ()
-- Data.Bool.Properties._.IsJoinSemilattice
d_IsJoinSemilattice_2662 :: (Bool -> Bool -> Bool) -> ()
d_IsJoinSemilattice_2662 = erased
-- Data.Bool.Properties._.IsLattice
d_IsLattice_2664 a0 a1 = ()
-- Data.Bool.Properties._.IsMeetSemilattice
d_IsMeetSemilattice_2666 :: (Bool -> Bool -> Bool) -> ()
d_IsMeetSemilattice_2666 = erased
-- Data.Bool.Properties._.IsSemilattice
d_IsSemilattice_2668 :: (Bool -> Bool -> Bool) -> ()
d_IsSemilattice_2668 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.absorptive
d_absorptive_2672 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_2672 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_2998
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe v0)))
-- Data.Bool.Properties._.IsBooleanAlgebra.isDistributiveLattice
d_isDistributiveLattice_2674 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_isDistributiveLattice_2674 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
      (coe v0)
-- Data.Bool.Properties._.IsBooleanAlgebra.isEquivalence
d_isEquivalence_2676 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2676 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe v0)))
-- Data.Bool.Properties._.IsBooleanAlgebra.isLattice
d_isLattice_2678 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_isLattice_2678 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
         (coe v0))
-- Data.Bool.Properties._.IsBooleanAlgebra.¬-cong
d_'172''45'cong_2690 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172''45'cong_2690 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-assoc
d_'8743''45'assoc_2694 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc_2694 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-comm
d_'8743''45'comm_2696 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'comm_2696 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-complement
d_'8743''45'complement_2698 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_2698 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3136
      (coe v0)
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-cong
d_'8743''45'cong_2704 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong_2704 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-distrib-∨
d_'8743''45'distrib'45''8744'_2710 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_2710 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3052
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
         (coe v0))
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-assoc
d_'8744''45'assoc_2718 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'assoc_2718 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-comm
d_'8744''45'comm_2720 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'comm_2720 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-complement
d_'8744''45'complement_2722 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_2722 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3134
      (coe v0)
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-cong
d_'8744''45'cong_2728 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong_2728 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-distrib-∧
d_'8744''45'distrib'45''8743'_2734 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_2734 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3050
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
         (coe v0))
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.assoc
d_assoc_2742 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2742 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.comm
d_comm_2744 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2744 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.idem
d_idem_2746 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_2746 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.identity
d_identity_2748 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2748 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe v0)))
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isBand
d_isBand_2754 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_2754 ~v0 ~v1 v2 = du_isBand_2754 v2
du_isBand_2754 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_isBand_2754 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_598
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v0))
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isEquivalence
d_isEquivalence_2756 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2756 ~v0 ~v1 v2 = du_isEquivalence_2756 v2
du_isEquivalence_2756 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2756 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))))
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isCommutativeBand
d_isCommutativeBand_2758 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_isCommutativeBand_2758 ~v0 ~v1 v2 = du_isCommutativeBand_2758 v2
du_isCommutativeBand_2758 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_isCommutativeBand_2758 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v0)
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isMagma
d_isMagma_2760 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2760 ~v0 ~v1 v2 = du_isMagma_2760 v2
du_isMagma_2760 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_2760 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isSemigroup
d_isSemigroup_2764 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2764 ~v0 ~v1 v2 = du_isSemigroup_2764 v2
du_isSemigroup_2764 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_2764 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.∙-cong
d_'8729''45'cong_2776 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2776 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.assoc
d_assoc_2784 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2784 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.comm
d_comm_2786 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2786 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.idem
d_idem_2788 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_2788 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.identity
d_identity_2790 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2790 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe v0)))
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isBand
d_isBand_2796 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_2796 ~v0 ~v1 v2 = du_isBand_2796 v2
du_isBand_2796 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_isBand_2796 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_598
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v0))
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isEquivalence
d_isEquivalence_2798 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2798 ~v0 ~v1 v2 = du_isEquivalence_2798 v2
du_isEquivalence_2798 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2798 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))))
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isMagma
d_isMagma_2800 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2800 ~v0 ~v1 v2 = du_isMagma_2800 v2
du_isMagma_2800 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_2800 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isCommutativeBand
d_isCommutativeBand_2802 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_isCommutativeBand_2802 ~v0 ~v1 v2 = du_isCommutativeBand_2802 v2
du_isCommutativeBand_2802 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_isCommutativeBand_2802 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v0)
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isSemigroup
d_isSemigroup_2806 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2806 ~v0 ~v1 v2 = du_isSemigroup_2806 v2
du_isSemigroup_2806 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_2806 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.∙-cong
d_'8729''45'cong_2818 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2818 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.assoc
d_assoc_2826 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2826 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.comm
d_comm_2828 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2828 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.idem
d_idem_2830 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_2830 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.identity
d_identity_2832 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2832 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe v0)))
-- Data.Bool.Properties._.IsBoundedSemilattice.isCommutativeMonoid
d_isCommutativeMonoid_2842 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_isCommutativeMonoid_2842 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862 (coe v0)
-- Data.Bool.Properties._.IsBoundedSemilattice.isEquivalence
d_isEquivalence_2846 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2846 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                  (coe v0)))))
-- Data.Bool.Properties._.IsBoundedSemilattice.isMagma
d_isMagma_2850 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2850 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
               (coe v0))))
-- Data.Bool.Properties._.IsBoundedSemilattice.isMonoid
d_isMonoid_2852 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2852 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862 (coe v0))
-- Data.Bool.Properties._.IsBoundedSemilattice.isSemigroup
d_isSemigroup_2856 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2856 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe v0)))
-- Data.Bool.Properties._.IsBoundedSemilattice.isCommutativeBand
d_isCommutativeBand_2858 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_isCommutativeBand_2858 ~v0 ~v1 v2 = du_isCommutativeBand_2858 v2
du_isCommutativeBand_2858 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_isCommutativeBand_2858 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v0)
-- Data.Bool.Properties._.IsBoundedSemilattice.∙-cong
d_'8729''45'cong_2872 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2872 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.absorptive
d_absorptive_2880 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_2880 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_2998
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v0))
-- Data.Bool.Properties._.IsDistributiveLattice.isEquivalence
d_isEquivalence_2882 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2882 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v0))
-- Data.Bool.Properties._.IsDistributiveLattice.isLattice
d_isLattice_2884 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_isLattice_2884 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v0)
-- Data.Bool.Properties._.IsDistributiveLattice.∧-assoc
d_'8743''45'assoc_2898 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc_2898 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-comm
d_'8743''45'comm_2900 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'comm_2900 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-cong
d_'8743''45'cong_2902 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong_2902 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-distrib-∨
d_'8743''45'distrib'45''8744'_2908 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_2908 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3052
      (coe v0)
-- Data.Bool.Properties._.IsDistributiveLattice.∨-assoc
d_'8744''45'assoc_2916 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'assoc_2916 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-comm
d_'8744''45'comm_2918 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'comm_2918 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-cong
d_'8744''45'cong_2920 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong_2920 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-distrib-∧
d_'8744''45'distrib'45''8743'_2926 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_2926 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3050
      (coe v0)
-- Data.Bool.Properties._.IsJoinSemilattice.assoc
d_assoc_2934 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2934 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.comm
d_comm_2936 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2936 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.idem
d_idem_2938 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_2938 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.isBand
d_isBand_2940 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_2940 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)
-- Data.Bool.Properties._.IsJoinSemilattice.isEquivalence
d_isEquivalence_2942 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2942 ~v0 v1 = du_isEquivalence_2942 v1
du_isEquivalence_2942 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2942 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))))
-- Data.Bool.Properties._.IsJoinSemilattice.isMagma
d_isMagma_2944 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2944 ~v0 v1 = du_isMagma_2944 v1
du_isMagma_2944 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_2944 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)))
-- Data.Bool.Properties._.IsJoinSemilattice.isSemigroup
d_isSemigroup_2948 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2948 ~v0 v1 = du_isSemigroup_2948 v1
du_isSemigroup_2948 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_2948 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))
-- Data.Bool.Properties._.IsJoinSemilattice.∙-cong
d_'8729''45'cong_2960 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2960 = erased
-- Data.Bool.Properties._.IsLattice.absorptive
d_absorptive_2968 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_2968 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_2998 (coe v0)
-- Data.Bool.Properties._.IsLattice.isEquivalence
d_isEquivalence_2970 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2970 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
      (coe v0)
-- Data.Bool.Properties._.IsLattice.∧-assoc
d_'8743''45'assoc_2984 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc_2984 = erased
-- Data.Bool.Properties._.IsLattice.∧-comm
d_'8743''45'comm_2986 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'comm_2986 = erased
-- Data.Bool.Properties._.IsLattice.∧-cong
d_'8743''45'cong_2988 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong_2988 = erased
-- Data.Bool.Properties._.IsLattice.∨-assoc
d_'8744''45'assoc_2996 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'assoc_2996 = erased
-- Data.Bool.Properties._.IsLattice.∨-comm
d_'8744''45'comm_2998 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'comm_2998 = erased
-- Data.Bool.Properties._.IsLattice.∨-cong
d_'8744''45'cong_3000 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong_3000 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.assoc
d_assoc_3008 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_3008 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.comm
d_comm_3010 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_3010 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.idem
d_idem_3012 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_3012 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.isBand
d_isBand_3014 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_3014 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)
-- Data.Bool.Properties._.IsMeetSemilattice.isEquivalence
d_isEquivalence_3016 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3016 ~v0 v1 = du_isEquivalence_3016 v1
du_isEquivalence_3016 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_3016 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))))
-- Data.Bool.Properties._.IsMeetSemilattice.isMagma
d_isMagma_3018 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_3018 ~v0 v1 = du_isMagma_3018 v1
du_isMagma_3018 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_3018 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)))
-- Data.Bool.Properties._.IsMeetSemilattice.isSemigroup
d_isSemigroup_3022 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_3022 ~v0 v1 = du_isSemigroup_3022 v1
du_isSemigroup_3022 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_3022 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))
-- Data.Bool.Properties._.IsMeetSemilattice.∙-cong
d_'8729''45'cong_3034 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_3034 = erased
-- Data.Bool.Properties._.IsSemilattice.assoc
d_assoc_3042 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_3042 = erased
-- Data.Bool.Properties._.IsSemilattice.comm
d_comm_3044 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_3044 = erased
-- Data.Bool.Properties._.IsSemilattice.idem
d_idem_3046 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_3046 = erased
-- Data.Bool.Properties._.IsSemilattice.isBand
d_isBand_3048 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_3048 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)
-- Data.Bool.Properties._.IsSemilattice.isEquivalence
d_isEquivalence_3050 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3050 ~v0 v1 = du_isEquivalence_3050 v1
du_isEquivalence_3050 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_3050 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))))
-- Data.Bool.Properties._.IsSemilattice.isMagma
d_isMagma_3052 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_3052 ~v0 v1 = du_isMagma_3052 v1
du_isMagma_3052 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_3052 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)))
-- Data.Bool.Properties._.IsSemilattice.isSemigroup
d_isSemigroup_3056 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_3056 ~v0 v1 = du_isSemigroup_3056 v1
du_isSemigroup_3056 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_3056 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))
-- Data.Bool.Properties._.IsSemilattice.∙-cong
d_'8729''45'cong_3068 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_3068 = erased
-- Data.Bool.Properties._≟_
d__'8799'__3082 ::
  Bool ->
  Bool -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__3082 v0 v1
  = if coe v0
      then if coe v1
             then coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe v1)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             else coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe v1) (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      else (if coe v1
              then coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe v0) (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
              else coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
-- Data.Bool.Properties.≡-setoid
d_'8801''45'setoid_3084 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8801''45'setoid_3084
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Bool.Properties.≡-decSetoid
d_'8801''45'decSetoid_3086 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8801''45'decSetoid_3086
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__3082)
-- Data.Bool.Properties.≤-reflexive
d_'8804''45'reflexive_3088 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'reflexive_3088 ~v0 ~v1 ~v2
  = du_'8804''45'reflexive_3088
du_'8804''45'reflexive_3088 ::
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10
du_'8804''45'reflexive_3088
  = coe MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16
-- Data.Bool.Properties.≤-refl
d_'8804''45'refl_3090 ::
  Bool -> MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'refl_3090 ~v0 = du_'8804''45'refl_3090
du_'8804''45'refl_3090 :: MAlonzo.Code.Data.Bool.Base.T__'8804'__10
du_'8804''45'refl_3090 = coe du_'8804''45'reflexive_3088
-- Data.Bool.Properties.≤-trans
d_'8804''45'trans_3092 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'trans_3092 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45'trans_3092 v3 v4
du_'8804''45'trans_3092 ::
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10
du_'8804''45'trans_3092 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Bool.Base.C_f'8804't_12
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Bool.Properties.≤-antisym
d_'8804''45'antisym_3096 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_3096 = erased
-- Data.Bool.Properties.≤-minimum
d_'8804''45'minimum_3098 ::
  Bool -> MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'minimum_3098 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Bool.Base.C_f'8804't_12
      else coe MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16
-- Data.Bool.Properties.≤-maximum
d_'8804''45'maximum_3100 ::
  Bool -> MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'maximum_3100 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16
      else coe MAlonzo.Code.Data.Bool.Base.C_f'8804't_12
-- Data.Bool.Properties.≤-total
d_'8804''45'total_3102 ::
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_3102 v0 v1
  = if coe v0
      then coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe d_'8804''45'maximum_3100 (coe v1))
      else coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe d_'8804''45'minimum_3098 (coe v1))
-- Data.Bool.Properties._≤?_
d__'8804''63'__3108 ::
  Bool ->
  Bool -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__3108 v0 v1
  = if coe v0
      then if coe v1
             then coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe v1)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16))
             else coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe v1) (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      else coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe d_'8804''45'minimum_3098 (coe v1)))
-- Data.Bool.Properties.≤-irrelevant
d_'8804''45'irrelevant_3112 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_3112 = erased
-- Data.Bool.Properties.≤-isPreorder
d_'8804''45'isPreorder_3114 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder_3114
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_3993
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_3088)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45'trans_3092 v3 v4)
-- Data.Bool.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_3116 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8804''45'isPartialOrder_3116
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9831
      (coe d_'8804''45'isPreorder_3114) erased
-- Data.Bool.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_3118 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8804''45'isTotalOrder_3118
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_20499
      (coe d_'8804''45'isPartialOrder_3116) (coe d_'8804''45'total_3102)
-- Data.Bool.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_3120 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8804''45'isDecTotalOrder_3120
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_22635
      (coe d_'8804''45'isTotalOrder_3118) (coe d__'8799'__3082)
      (coe d__'8804''63'__3108)
-- Data.Bool.Properties.≤-poset
d_'8804''45'poset_3122 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8804''45'poset_3122
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6347
      d_'8804''45'isPartialOrder_3116
-- Data.Bool.Properties.≤-preorder
d_'8804''45'preorder_3124 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_'8804''45'preorder_3124
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2249
      d_'8804''45'isPreorder_3114
-- Data.Bool.Properties.≤-totalOrder
d_'8804''45'totalOrder_3126 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
d_'8804''45'totalOrder_3126
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_15657
      d_'8804''45'isTotalOrder_3118
-- Data.Bool.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_3128 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_'8804''45'decTotalOrder_3128
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17747
      d_'8804''45'isDecTotalOrder_3120
-- Data.Bool.Properties.<-irrefl
d_'60''45'irrefl_3130 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_3130 = erased
-- Data.Bool.Properties.<-asym
d_'60''45'asym_3132 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_3132 = erased
-- Data.Bool.Properties.<-trans
d_'60''45'trans_3134 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18
d_'60''45'trans_3134 = erased
-- Data.Bool.Properties.<-transʳ
d_'60''45'trans'691'_3136 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18
d_'60''45'trans'691'_3136 = erased
-- Data.Bool.Properties.<-transˡ
d_'60''45'trans'737'_3138 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18
d_'60''45'trans'737'_3138 = erased
-- Data.Bool.Properties.<-cmp
d_'60''45'cmp_3140 ::
  Bool -> Bool -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_3140 v0 v1
  = if coe v0
      then if coe v1
             then coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
             else coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 erased
      else (if coe v1
              then coe
                     MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 erased
              else coe
                     MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased)
-- Data.Bool.Properties._<?_
d__'60''63'__3142 ::
  Bool ->
  Bool -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__3142 v0 v1
  = if coe v0
      then coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      else (if coe v1
              then coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe v1)
                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
              else coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe v1)
                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
-- Data.Bool.Properties.<-resp₂-≡
d_'60''45'resp'8322''45''8801'_3144 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'8322''45''8801'_3144
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Bool.Properties.<-irrelevant
d_'60''45'irrelevant_3150 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_3150 = erased
-- Data.Bool.Properties.<-wellFounded
d_'60''45'wellFounded_3152 ::
  Bool -> MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''45'wellFounded_3152 = erased
-- Data.Bool.Properties._.<-acc
d_'60''45'acc_3162 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''45'acc_3162 = erased
-- Data.Bool.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_3164 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder_3164
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14011
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased d_'60''45'resp'8322''45''8801'_3144
-- Data.Bool.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_3166 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''45'isStrictTotalOrder_3166
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24885
      (coe d_'60''45'isStrictPartialOrder_3164) (coe d_'60''45'cmp_3140)
-- Data.Bool.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_3168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder_3168
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11031
      d_'60''45'isStrictPartialOrder_3164
-- Data.Bool.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_3170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_'60''45'strictTotalOrder_3170
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_20945
      d_'60''45'isStrictTotalOrder_3166
-- Data.Bool.Properties.∨-assoc
d_'8744''45'assoc_3172 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'assoc_3172 = erased
-- Data.Bool.Properties.∨-comm
d_'8744''45'comm_3182 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'comm_3182 = erased
-- Data.Bool.Properties.∨-identityˡ
d_'8744''45'identity'737'_3184 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'identity'737'_3184 = erased
-- Data.Bool.Properties.∨-identityʳ
d_'8744''45'identity'691'_3186 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'identity'691'_3186 = erased
-- Data.Bool.Properties.∨-identity
d_'8744''45'identity_3188 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'identity_3188
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-zeroˡ
d_'8744''45'zero'737'_3190 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'zero'737'_3190 = erased
-- Data.Bool.Properties.∨-zeroʳ
d_'8744''45'zero'691'_3192 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'zero'691'_3192 = erased
-- Data.Bool.Properties.∨-zero
d_'8744''45'zero_3194 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'zero_3194
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-inverseˡ
d_'8744''45'inverse'737'_3196 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'inverse'737'_3196 = erased
-- Data.Bool.Properties.∨-inverseʳ
d_'8744''45'inverse'691'_3198 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'inverse'691'_3198 = erased
-- Data.Bool.Properties.∨-inverse
d_'8744''45'inverse_3202 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'inverse_3202
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-idem
d_'8744''45'idem_3204 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'idem_3204 = erased
-- Data.Bool.Properties.∨-sel
d_'8744''45'sel_3206 ::
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8744''45'sel_3206 v0 ~v1 = du_'8744''45'sel_3206 v0
du_'8744''45'sel_3206 ::
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8744''45'sel_3206 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Bool.Properties.∨-conicalˡ
d_'8744''45'conical'737'_3212 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'conical'737'_3212 = erased
-- Data.Bool.Properties.∨-conicalʳ
d_'8744''45'conical'691'_3214 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'conical'691'_3214 = erased
-- Data.Bool.Properties.∨-conical
d_'8744''45'conical_3216 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'conical_3216
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-isMagma
d_'8744''45'isMagma_3218 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8744''45'isMagma_3218
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1865
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Bool.Properties.∨-magma
d_'8744''45'magma_3220 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8744''45'magma_3220
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1259
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30 d_'8744''45'isMagma_3218
-- Data.Bool.Properties.∨-isSemigroup
d_'8744''45'isSemigroup_3222 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8744''45'isSemigroup_3222
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10399
      (coe d_'8744''45'isMagma_3218) erased
-- Data.Bool.Properties.∨-semigroup
d_'8744''45'semigroup_3224 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8744''45'semigroup_3224
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9677
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      d_'8744''45'isSemigroup_3222
-- Data.Bool.Properties.∨-isBand
d_'8744''45'isBand_3226 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8744''45'isBand_3226
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsBand'46'constructor_11185
      (coe d_'8744''45'isSemigroup_3222) erased
-- Data.Bool.Properties.∨-band
d_'8744''45'band_3228 :: MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8744''45'band_3228
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Band'46'constructor_10753
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30 d_'8744''45'isBand_3226
-- Data.Bool.Properties.∨-isSemilattice
d_'8744''45'isSemilattice_3230 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8744''45'isSemilattice_3230
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeBand'46'constructor_13085
      (coe d_'8744''45'isBand_3226) erased
-- Data.Bool.Properties.∨-semilattice
d_'8744''45'semilattice_3232 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8744''45'semilattice_3232
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_Semilattice'46'constructor_193
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      d_'8744''45'isSemilattice_3230
-- Data.Bool.Properties.∨-isMonoid
d_'8744''45'isMonoid_3234 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8744''45'isMonoid_3234
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15845
      (coe d_'8744''45'isSemigroup_3222) (coe d_'8744''45'identity_3188)
-- Data.Bool.Properties.∨-isCommutativeMonoid
d_'8744''45'isCommutativeMonoid_3236 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'8744''45'isCommutativeMonoid_3236
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17665
      (coe d_'8744''45'isMonoid_3234) erased
-- Data.Bool.Properties.∨-commutativeMonoid
d_'8744''45'commutativeMonoid_3238 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'8744''45'commutativeMonoid_3238
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17727
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      d_'8744''45'isCommutativeMonoid_3236
-- Data.Bool.Properties.∨-isIdempotentCommutativeMonoid
d_'8744''45'isIdempotentCommutativeMonoid_3240 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852
d_'8744''45'isIdempotentCommutativeMonoid_3240
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsIdempotentCommutativeMonoid'46'constructor_20651
      (coe d_'8744''45'isCommutativeMonoid_3236) erased
-- Data.Bool.Properties.∨-idempotentCommutativeMonoid
d_'8744''45'idempotentCommutativeMonoid_3242 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148
d_'8744''45'idempotentCommutativeMonoid_3242
  = coe
      MAlonzo.Code.Algebra.Bundles.C_IdempotentCommutativeMonoid'46'constructor_21255
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      d_'8744''45'isIdempotentCommutativeMonoid_3240
-- Data.Bool.Properties.∧-assoc
d_'8743''45'assoc_3244 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc_3244 = erased
-- Data.Bool.Properties.∧-comm
d_'8743''45'comm_3254 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'comm_3254 = erased
-- Data.Bool.Properties.∧-identityˡ
d_'8743''45'identity'737'_3256 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'identity'737'_3256 = erased
-- Data.Bool.Properties.∧-identityʳ
d_'8743''45'identity'691'_3258 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'identity'691'_3258 = erased
-- Data.Bool.Properties.∧-identity
d_'8743''45'identity_3260 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'identity_3260
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-zeroˡ
d_'8743''45'zero'737'_3262 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'zero'737'_3262 = erased
-- Data.Bool.Properties.∧-zeroʳ
d_'8743''45'zero'691'_3264 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'zero'691'_3264 = erased
-- Data.Bool.Properties.∧-zero
d_'8743''45'zero_3266 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'zero_3266
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-inverseˡ
d_'8743''45'inverse'737'_3268 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'inverse'737'_3268 = erased
-- Data.Bool.Properties.∧-inverseʳ
d_'8743''45'inverse'691'_3270 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'inverse'691'_3270 = erased
-- Data.Bool.Properties.∧-inverse
d_'8743''45'inverse_3274 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'inverse_3274
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-idem
d_'8743''45'idem_3276 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'idem_3276 = erased
-- Data.Bool.Properties.∧-sel
d_'8743''45'sel_3278 ::
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8743''45'sel_3278 v0 ~v1 = du_'8743''45'sel_3278 v0
du_'8743''45'sel_3278 ::
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8743''45'sel_3278 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
-- Data.Bool.Properties.∧-conicalˡ
d_'8743''45'conical'737'_3284 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'conical'737'_3284 = erased
-- Data.Bool.Properties.∧-conicalʳ
d_'8743''45'conical'691'_3286 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'conical'691'_3286 = erased
-- Data.Bool.Properties.∧-conical
d_'8743''45'conical_3288 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'conical_3288
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_3290 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'737''45''8744'_3290 = erased
-- Data.Bool.Properties.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_3300 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'691''45''8744'_3300 = erased
-- Data.Bool.Properties.∧-distrib-∨
d_'8743''45'distrib'45''8744'_3308 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_3308
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_3310 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'737''45''8743'_3310 = erased
-- Data.Bool.Properties.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_3320 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'691''45''8743'_3320 = erased
-- Data.Bool.Properties.∨-distrib-∧
d_'8744''45'distrib'45''8743'_3328 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_3328
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-abs-∨
d_'8743''45'abs'45''8744'_3330 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'abs'45''8744'_3330 = erased
-- Data.Bool.Properties.∨-abs-∧
d_'8744''45'abs'45''8743'_3336 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'abs'45''8743'_3336 = erased
-- Data.Bool.Properties.∨-∧-absorptive
d_'8744''45''8743''45'absorptive_3342 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45''8743''45'absorptive_3342
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-isMagma
d_'8743''45'isMagma_3344 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8743''45'isMagma_3344
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1865
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Bool.Properties.∧-magma
d_'8743''45'magma_3346 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8743''45'magma_3346
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1259
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24 d_'8743''45'isMagma_3344
-- Data.Bool.Properties.∧-isSemigroup
d_'8743''45'isSemigroup_3348 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8743''45'isSemigroup_3348
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10399
      (coe d_'8743''45'isMagma_3344) erased
-- Data.Bool.Properties.∧-semigroup
d_'8743''45'semigroup_3350 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8743''45'semigroup_3350
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9677
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      d_'8743''45'isSemigroup_3348
-- Data.Bool.Properties.∧-isBand
d_'8743''45'isBand_3352 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8743''45'isBand_3352
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsBand'46'constructor_11185
      (coe d_'8743''45'isSemigroup_3348) erased
-- Data.Bool.Properties.∧-band
d_'8743''45'band_3354 :: MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8743''45'band_3354
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Band'46'constructor_10753
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24 d_'8743''45'isBand_3352
-- Data.Bool.Properties.∧-isSemilattice
d_'8743''45'isSemilattice_3356 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8743''45'isSemilattice_3356
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeBand'46'constructor_13085
      (coe d_'8743''45'isBand_3352) erased
-- Data.Bool.Properties.∧-semilattice
d_'8743''45'semilattice_3358 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8743''45'semilattice_3358
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_Semilattice'46'constructor_193
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      d_'8743''45'isSemilattice_3356
-- Data.Bool.Properties.∧-isMonoid
d_'8743''45'isMonoid_3360 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8743''45'isMonoid_3360
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15845
      (coe d_'8743''45'isSemigroup_3348) (coe d_'8743''45'identity_3260)
-- Data.Bool.Properties.∧-isCommutativeMonoid
d_'8743''45'isCommutativeMonoid_3362 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'8743''45'isCommutativeMonoid_3362
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17665
      (coe d_'8743''45'isMonoid_3360) erased
-- Data.Bool.Properties.∧-commutativeMonoid
d_'8743''45'commutativeMonoid_3364 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'8743''45'commutativeMonoid_3364
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17727
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      d_'8743''45'isCommutativeMonoid_3362
-- Data.Bool.Properties.∧-isIdempotentCommutativeMonoid
d_'8743''45'isIdempotentCommutativeMonoid_3366 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852
d_'8743''45'isIdempotentCommutativeMonoid_3366
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsIdempotentCommutativeMonoid'46'constructor_20651
      (coe d_'8743''45'isCommutativeMonoid_3362) erased
-- Data.Bool.Properties.∧-idempotentCommutativeMonoid
d_'8743''45'idempotentCommutativeMonoid_3368 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148
d_'8743''45'idempotentCommutativeMonoid_3368
  = coe
      MAlonzo.Code.Algebra.Bundles.C_IdempotentCommutativeMonoid'46'constructor_21255
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      d_'8743''45'isIdempotentCommutativeMonoid_3366
-- Data.Bool.Properties.∨-∧-isSemiring
d_'8744''45''8743''45'isSemiring_3370 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_'8744''45''8743''45'isSemiring_3370
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_47957
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43717
         (coe d_'8744''45'isCommutativeMonoid_3236) erased erased
         (coe d_'8743''45'identity_3260)
         (coe d_'8743''45'distrib'45''8744'_3308))
      (coe d_'8743''45'zero_3266)
-- Data.Bool.Properties.∨-∧-isCommutativeSemiring
d_'8744''45''8743''45'isCommutativeSemiring_3372 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_'8744''45''8743''45'isCommutativeSemiring_3372
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_51779
      (coe d_'8744''45''8743''45'isSemiring_3370) erased
-- Data.Bool.Properties.∨-∧-commutativeSemiring
d_'8744''45''8743''45'commutativeSemiring_3374 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
d_'8744''45''8743''45'commutativeSemiring_3374
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_44173
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      d_'8744''45''8743''45'isCommutativeSemiring_3372
-- Data.Bool.Properties.∧-∨-isSemiring
d_'8743''45''8744''45'isSemiring_3376 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_'8743''45''8744''45'isSemiring_3376
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_47957
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43717
         (coe d_'8743''45'isCommutativeMonoid_3362) erased erased
         (coe d_'8744''45'identity_3188)
         (coe d_'8744''45'distrib'45''8743'_3328))
      (coe d_'8744''45'zero_3194)
-- Data.Bool.Properties.∧-∨-isCommutativeSemiring
d_'8743''45''8744''45'isCommutativeSemiring_3378 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_'8743''45''8744''45'isCommutativeSemiring_3378
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_51779
      (coe d_'8743''45''8744''45'isSemiring_3376) erased
-- Data.Bool.Properties.∧-∨-commutativeSemiring
d_'8743''45''8744''45'commutativeSemiring_3380 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
d_'8743''45''8744''45'commutativeSemiring_3380
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_44173
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      d_'8743''45''8744''45'isCommutativeSemiring_3378
-- Data.Bool.Properties.∨-∧-isLattice
d_'8744''45''8743''45'isLattice_3382 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_'8744''45''8743''45'isLattice_3382
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsLattice'46'constructor_36793
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased erased erased erased erased erased
      (coe d_'8744''45''8743''45'absorptive_3342)
-- Data.Bool.Properties.∨-∧-lattice
d_'8744''45''8743''45'lattice_3384 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8744''45''8743''45'lattice_3384
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_Lattice'46'constructor_7829
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      d_'8744''45''8743''45'isLattice_3382
-- Data.Bool.Properties.∨-∧-isDistributiveLattice
d_'8744''45''8743''45'isDistributiveLattice_3386 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_'8744''45''8743''45'isDistributiveLattice_3386
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsDistributiveLattice'46'constructor_40887
      (coe d_'8744''45''8743''45'isLattice_3382)
      (coe d_'8744''45'distrib'45''8743'_3328)
      (coe d_'8743''45'distrib'45''8744'_3308)
-- Data.Bool.Properties.∨-∧-distributiveLattice
d_'8744''45''8743''45'distributiveLattice_3388 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8744''45''8743''45'distributiveLattice_3388
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_DistributiveLattice'46'constructor_9399
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      d_'8744''45''8743''45'isDistributiveLattice_3386
-- Data.Bool.Properties.∨-∧-isBooleanAlgebra
d_'8744''45''8743''45'isBooleanAlgebra_3390 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112
d_'8744''45''8743''45'isBooleanAlgebra_3390
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsBooleanAlgebra'46'constructor_43953
      (coe d_'8744''45''8743''45'isDistributiveLattice_3386)
      (coe d_'8744''45'inverse_3202) (coe d_'8743''45'inverse_3274)
      erased
-- Data.Bool.Properties.∨-∧-booleanAlgebra
d_'8744''45''8743''45'booleanAlgebra_3392 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682
d_'8744''45''8743''45'booleanAlgebra_3392
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_BooleanAlgebra'46'constructor_11373
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      MAlonzo.Code.Data.Bool.Base.d_not_22
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      d_'8744''45''8743''45'isBooleanAlgebra_3390
-- Data.Bool.Properties.not-involutive
d_not'45'involutive_3394 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'involutive_3394 = erased
-- Data.Bool.Properties.not-injective
d_not'45'injective_3400 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'injective_3400 = erased
-- Data.Bool.Properties.not-¬
d_not'45''172'_3410 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_not'45''172'_3410 = erased
-- Data.Bool.Properties.¬-not
d_'172''45'not_3416 ::
  Bool ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172''45'not_3416 = erased
-- Data.Bool.Properties.xor-is-ok
d_xor'45'is'45'ok_3426 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'is'45'ok_3426 = erased
-- Data.Bool.Properties.true-xor
d_true'45'xor_3434 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_true'45'xor_3434 = erased
-- Data.Bool.Properties.xor-same
d_xor'45'same_3438 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'same_3438 = erased
-- Data.Bool.Properties.not-distribˡ-xor
d_not'45'distrib'737''45'xor_3444 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'distrib'737''45'xor_3444 = erased
-- Data.Bool.Properties.not-distribʳ-xor
d_not'45'distrib'691''45'xor_3454 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'distrib'691''45'xor_3454 = erased
-- Data.Bool.Properties.xor-assoc
d_xor'45'assoc_3460 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'assoc_3460 = erased
-- Data.Bool.Properties.xor-comm
d_xor'45'comm_3470 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'comm_3470 = erased
-- Data.Bool.Properties.xor-identityˡ
d_xor'45'identity'737'_3472 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'identity'737'_3472 = erased
-- Data.Bool.Properties.xor-identityʳ
d_xor'45'identity'691'_3474 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'identity'691'_3474 = erased
-- Data.Bool.Properties.xor-identity
d_xor'45'identity_3476 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_xor'45'identity_3476
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.xor-inverseˡ
d_xor'45'inverse'737'_3478 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'inverse'737'_3478 = erased
-- Data.Bool.Properties.xor-inverseʳ
d_xor'45'inverse'691'_3480 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'inverse'691'_3480 = erased
-- Data.Bool.Properties.xor-inverse
d_xor'45'inverse_3484 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_xor'45'inverse_3484
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-distribˡ-xor
d_'8743''45'distrib'737''45'xor_3486 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'737''45'xor_3486 = erased
-- Data.Bool.Properties.∧-distribʳ-xor
d_'8743''45'distrib'691''45'xor_3496 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'691''45'xor_3496 = erased
-- Data.Bool.Properties.∧-distrib-xor
d_'8743''45'distrib'45'xor_3506 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45'xor_3506
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.xor-annihilates-not
d_xor'45'annihilates'45'not_3512 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'annihilates'45'not_3512 = erased
-- Data.Bool.Properties.xor-∧-commutativeRing
d_xor'45''8743''45'commutativeRing_3518 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4016
d_xor'45''8743''45'commutativeRing_3518
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.BooleanAlgebra.du_'8853''45''8743''45'commutativeRing_3706
      (coe d_'8744''45''8743''45'booleanAlgebra_3392)
      (coe MAlonzo.Code.Data.Bool.Base.d__xor__36) erased
-- Data.Bool.Properties.if-float
d_if'45'float_3792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'float_3792 = erased
-- Data.Bool.Properties.T-≡
d_T'45''8801'_3796 ::
  Bool -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_T'45''8801'_3796 v0
  = if coe v0
      then coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
             (let v1 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
              coe (coe (\ v2 -> v1)))
      else coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased erased
-- Data.Bool.Properties.T-not-≡
d_T'45'not'45''8801'_3800 ::
  Bool -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_T'45'not'45''8801'_3800 v0
  = if coe v0
      then coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased erased
      else coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
             (let v1 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
              coe (coe (\ v2 -> v1)))
-- Data.Bool.Properties.T-∧
d_T'45''8743'_3806 ::
  Bool -> Bool -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_T'45''8743'_3806 v0 v1
  = if coe v0
      then if coe v1
             then coe
                    MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
                    (let v2
                           = coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                     coe (coe (\ v3 -> v2)))
                    (let v2 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
                     coe (coe (\ v3 -> v2)))
             else coe
                    MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
                    (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
      else coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
             (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
-- Data.Bool.Properties.T-∨
d_T'45''8744'_3812 ::
  Bool -> Bool -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_T'45''8744'_3812 v0 v1
  = if coe v0
      then coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
             (let v2 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
              coe (coe (\ v3 -> v2)))
      else (if coe v1
              then coe
                     MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                     (let v2 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
                      coe (coe (\ v3 -> v2)))
              else coe
                     MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                     (coe
                        MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52 (coe (\ v2 -> v2))
                        (coe (\ v2 -> v2))))
-- Data.Bool.Properties.T-irrelevant
d_T'45'irrelevant_3814 ::
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'45'irrelevant_3814 = erased
-- Data.Bool.Properties.T?-diag
d_T'63''45'diag_3818 :: Bool -> AgdaAny -> AgdaAny
d_T'63''45'diag_3818 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_fromWitness_140
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
         (coe v0)
         (coe
            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
            (coe v0)))
-- Data.Bool.Properties.⇔→≡
d_'8660''8594''8801'_3828 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8660''8594''8801'_3828 = erased
-- Data.Bool.Properties.push-function-into-if
d_push'45'function'45'into'45'if_3842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45'function'45'into'45'if_3842 = erased
