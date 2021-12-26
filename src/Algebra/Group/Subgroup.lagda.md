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

A __subgroup__ of a group $G$ is defined as a subset of the carrier set
of $G$ that contains the group's unit, is closed under the group's
operation as well as its inverses. 

```agda
record Subgroup {ℓ ℓ'} {A : Type ℓ} (group : GroupOn A)
  : Type (ℓ ⊔ lsuc ℓ') where
  open GroupOn group
  field
    subgroup-pred : Predicate A ℓ'
    subgroup-closed-operation : isClosed-binary subgroup-pred .contains _⋆_
    subgroup-closed-inverse : isClosed-unary subgroup-pred .contains inverse
    subgroup-contains-unit : subgroup-pred .contains unit
```

From this definition, we can also extract the notion of subgroups as
groups equipped with an injective homomorphism into $G$.

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

  induced-group-hom : GroupHom (_ , induced-group) (_ , group)
  induced-group-hom .fst = fst
  induced-group-hom .snd .pres-⋆ (x , prf-x) (y , prf-y) = refl

  induced-group-hom-is-embedding : isEmbedding (induced-group-hom .fst)
  induced-group-hom-is-embedding = embed subgroup-pred .snd
