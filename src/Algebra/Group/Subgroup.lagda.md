```agda
open import Algebra.Group
open import Algebra.Monoid
open import Algebra.Semigroup
open import Algebra.Magma
open import Data.Predicate

open import 1Lab.Prelude

module Algebra.Group.Subgroup where
```

# Subgroups

A __subgroup__ of a group $G$ is defined as a injective homomorphism
into $G$. This simplifies a lot of definitions, as there's no subtype
issues to be handled. Nonetheless, we also show the equivalence to the
alternative definition of a subgroup as a subset of the carrier set
of $G$ that contains the group's unit, is closed under the group's
operation as well as its inverses. 

```agda
record Subgroup {ℓ ℓ'} (group : Group ℓ)
  : Type (ℓ ⊔ lsuc ℓ') where
  private
    A = group .fst
  open GroupOn (group .snd)
  field
    subgroup : Group ℓ'
    inclusion-hom : GroupHom subgroup group
    inclusion-hom-is-embedding : isEmbedding (inclusion-hom .fst)

  subgroupContains : Predicate A (ℓ ⊔ ℓ')
  subgroupContains = embedding-set-image
    (hasIsSet (hasIsMagma (hasIsSemigroup hasIsMonoid)))
    (inclusion-hom .fst , inclusion-hom-is-embedding)

record SubgroupPred {ℓ ℓ'} (group : Group ℓ)
  : Type (ℓ ⊔ lsuc ℓ') where
  private
    A = group .fst
  open GroupOn (group .snd)
  field
    subgroup-pred : Predicate A ℓ'
    subgroup-closed-operation : isClosed-binary subgroup-pred .contains _⋆_
    subgroup-closed-inverse : isClosed-unary subgroup-pred .contains inverse
    subgroup-contains-unit : subgroup-pred .contains unit
```

From the predicate definition, we can also recover subgroups in the
morphism sense.

```agda
  induced-group : GroupOn (Σ (subgroup-pred .contains))
  induced-group .GroupOn._⋆_ (x , x-prf) (y , y-prf) =
    (x ⋆ y) , (subgroup-closed-operation x y x-prf y-prf)
  induced-group .GroupOn.hasIsGroup .isGroup.unit =
    unit , subgroup-contains-unit
  induced-group .GroupOn.hasIsGroup .isGroup.hasIsMonoid .hasIsSemigroup
    .hasIsMagma .hasIsSet = is-set-subtype-is-set subgroup-pred
      (hasIsSet (hasIsMagma (hasIsSemigroup hasIsMonoid)))
  induced-group .GroupOn.hasIsGroup .isGroup.hasIsMonoid .hasIsSemigroup
    .associative = Σ≡Prop (subgroup-pred .isPointwiseProp)
      (associative (hasIsSemigroup hasIsMonoid))
  induced-group .GroupOn.hasIsGroup .isGroup.hasIsMonoid .isMonoid.idˡ =
    Σ≡Prop (subgroup-pred .isPointwiseProp) (idˡ hasIsMonoid)
  induced-group .GroupOn.hasIsGroup .isGroup.hasIsMonoid .isMonoid.idʳ =
    Σ≡Prop (subgroup-pred .isPointwiseProp) (idʳ hasIsMonoid)
  induced-group .GroupOn.hasIsGroup .isGroup.inverse (x , x-prf) =
    inverse x , subgroup-closed-inverse x x-prf
  induced-group .GroupOn.hasIsGroup .isGroup.inverseˡ {x , x-prf} =
    Σ≡Prop (subgroup-pred .isPointwiseProp) inverseˡ
  induced-group .GroupOn.hasIsGroup .isGroup.inverseʳ =
    Σ≡Prop (subgroup-pred .isPointwiseProp) inverseʳ

  induced-group-hom : GroupHom (_ , induced-group) group
  induced-group-hom .fst = fst
  induced-group-hom .snd .pres-⋆ (x , prf-x) (y , prf-y) = refl

  induced-group-hom-is-embedding : isEmbedding (induced-group-hom .fst)
  induced-group-hom-is-embedding = embed subgroup-pred .snd

  induced-subgroup : Subgroup {ℓ' = ℓ' ⊔ ℓ} group
  induced-subgroup .Subgroup.subgroup = _ , induced-group
  induced-subgroup .Subgroup.inclusion-hom = induced-group-hom
  induced-subgroup .Subgroup.inclusion-hom-is-embedding = induced-group-hom-is-embedding
  
open Subgroup public
```

This also works in the opposite direction - every subgroup given by a
embedding defines a subset of the original group that is a subgroup
in the set-based sense.

```agda
module _ {ℓ ℓ'} {G : Group ℓ} where
  open SubgroupPred
  Subgroup→SubgroupPred :
    Subgroup {ℓ' = ℓ'} G → SubgroupPred {ℓ' = ℓ ⊔ ℓ'} G
  Subgroup→SubgroupPred sg .subgroup-pred = subgroupContains sg
  Subgroup→SubgroupPred sg .subgroup-closed-operation x y
    (prex , xprf) (prey , yprf) = (prex ⋆ prey) ,
       sg .inclusion-hom .snd .pres-⋆ prex prey ∙
         ap₂ (G .snd .GroupOn._⋆_) xprf yprf
    where open GroupOn (sg .subgroup .snd)
  Subgroup→SubgroupPred sg .subgroup-closed-inverse x (prex , xprf) =
    inverse prex ,
      pres-inv (sg .inclusion-hom .snd) prex ∙
        ap (GroupOn.inverse (G .snd)) xprf 
     where open GroupOn (sg .subgroup .snd)
  Subgroup→SubgroupPred sg .subgroup-contains-unit =
    (GroupOn.unit (sg .subgroup .snd)) , pres-id (sg .inclusion-hom .snd)

```

We also define the __image__ subgroup given by a group homomorphism. This
definition is essential to a lot of group theory, for example, the
isomorphism theorems.


```agda
module _ where
  open SubgroupPred
  group-image' : ∀ {ℓ ℓ'} {A : Σ (GroupOn {ℓ = ℓ})} {B : Σ (GroupOn {ℓ = ℓ'})}
    → GroupHom A B → SubgroupPred {ℓ' = ℓ ⊔ ℓ'} B
  group-image' (f , ishom) .subgroup-pred = image f
  group-image' {A = A} {B = B} (f , ishom) .subgroup-closed-operation x y
    (inc (ax , eqx)) (inc (ay , eqy)) =
    inc (A .snd .GroupOn._⋆_ ax ay ,
        ishom .pres-⋆ ax ay ∙ ap₂ (B .snd .GroupOn._⋆_) eqx eqy)
  group-image' {A = A} {B = B} (f , ishom) .subgroup-closed-operation x y
    (inc (prex , prfx)) (squash prfy prfy₁ i) =
      isProp→PathP (λ i → isProp-∥-∥)
        {!acquire-preimage-of-product prfy!} {!!} i
    where open GroupOn (A .snd)
          acquire-preimage-of-product :
            ∃ _ (λ x₁ → f x₁ ≡ y) →
            ∃ _ (λ x₁ → f x₁ ≡ B .snd .GroupOn._⋆_ x y)
          acquire-preimage-of-product = ∥-∥-map {A = Σ (λ x₁ → f x₁ ≡ y)}
            (λ {(prey' , prfy') → (prex ⋆ prey' ,
              ishom .pres-⋆ prex prey' ∙ ap₂
                (B .snd .GroupOn._⋆_) prfx prfy')})
  group-image' (f , ishom) .subgroup-closed-operation x y (squash prfx prfx₁ i) (inc x₁) = {!!}
  group-image' (f , ishom) .subgroup-closed-operation x y (squash prfx prfx₁ i) (squash prfy prfy₁ i₁) = {!!}
  group-image' (f , ishom) .subgroup-closed-inverse = {!!}
  group-image' (f , ishom) .subgroup-contains-unit = {!!}
```
