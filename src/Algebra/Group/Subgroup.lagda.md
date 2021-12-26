```agda
open import Algebra.Group
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
