```agda
open import 1Lab.Type

open import Agda.Builtin.Bool

module 1Lab.Data.Bool.Base where

```

# The Booleans - basics

The boolean type is already built-in into Agda - in this module,
we re-export it and define the basic boolean operations. Their properties
are studied in closer detail in the corresponding module.

```agda
open import Agda.Builtin.Bool public

not : Bool → Bool
not true = false
not false = true

and or : Bool → Bool → Bool
and false y = false
and true false = false
and true true = true

or false false = false
or false true = true
or true y = true
```

We also define a dependent if-then-else-clause:

```agda
if_then_else : {ℓ : _} {P : Bool → Type ℓ} (x : Bool) → P true → P false → P x
if false then tru else fls = fls
if true then tru else fls = tru

```
