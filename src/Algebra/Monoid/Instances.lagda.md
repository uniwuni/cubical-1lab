```agda
open import 1Lab.Prelude

open import Algebra.Monoid
open import Algebra.Semigroup
open import Algebra.Magma

module Algebra.Monoid.Instances where
```

# Monoids

The natural numbers form monoids under addition and multiplication:

```agda
open import 1Lab.Data.Nat

+-isMonoid : isMonoid 0 _+_
+-isMonoid .hasIsSemigroup .hasIsMagma .hasIsSet = isSet-Nat
+-isMonoid .hasIsSemigroup .associative {x} {y} {z} = sym (+-associative x y z)
+-isMonoid .idˡ = refl
+-isMonoid .idʳ = +-zeroʳ _

*-isMonoid : isMonoid 1 _*_
*-isMonoid .hasIsSemigroup .hasIsMagma .hasIsSet = isSet-Nat
*-isMonoid .hasIsSemigroup .associative {x} {y} {z} = sym (*-associative x y z)
*-isMonoid .idˡ {x} = *-commutative 1 x ∙ (*-oneʳ _)
*-isMonoid .idʳ = *-oneʳ _
```
