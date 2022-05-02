```agda
open import 1Lab.Path

open import Cat.Base

import Cat.Reasoning

module Cat.Functor.Reasoning
  {o ℓ o′ ℓ′}
  {𝒞 : Precategory o ℓ} {𝒟 : Precategory o′ ℓ′}
  (F : Functor 𝒞 𝒟) where

module 𝒞 = Cat.Reasoning 𝒞
module 𝒟 = Cat.Reasoning 𝒟
open Functor F public
```

<!--
```agda
private variable
  A B C : 𝒞.Ob
  a b c d : 𝒞.Hom A B
  X Y Z : 𝒟.Ob
  f g h i : 𝒟.Hom X Y
```
-->


# Reasoning Combinators for Functors

The combinators exposed in [category reasoning] abstract out a lot of common
algebraic manipulations, and make proofs much more concise. However, once functors
get involved, those combinators start to get unwieldy! Therefore, we have
to write some new combinators for working with functors specifically.
This module is meant to be imported qualified.

[category reasoning]: Cat.Reasoning.html

## Identity Morphisms

```agda
module _ (a≡id : a ≡ 𝒞.id) where
  elim : F₁ a ≡ 𝒟.id
  elim = ap F₁ a≡id ∙ F-id

  eliml : F₁ a 𝒟.∘ f ≡ f 
  eliml = 𝒟.eliml elim

  elimr : f 𝒟.∘ F₁ a ≡ f
  elimr = 𝒟.elimr elim

  introl : f ≡ F₁ a 𝒟.∘ f
  introl = 𝒟.introl elim

  intror : f ≡ f 𝒟.∘ F₁ a
  intror = 𝒟.intror elim
```

## Reassociations

```agda
module _ (ab≡c : a 𝒞.∘ b ≡ c) where
  collapse : F₁ a 𝒟.∘ F₁ b ≡ F₁ c
  collapse = sym (F-∘ a b) ∙ ap F₁ ab≡c

  pulll : F₁ a 𝒟.∘ (F₁ b 𝒟.∘ f) ≡ F₁ c 𝒟.∘ f
  pulll = 𝒟.pulll collapse

  pullr : (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b ≡ f 𝒟.∘ F₁ c
  pullr = 𝒟.pullr collapse

module _ (c≡ab : c ≡ a 𝒞.∘ b) where
  expand : F₁ c ≡ F₁ a 𝒟.∘ F₁ b
  expand = sym (collapse (sym c≡ab))

  pushl : F₁ c 𝒟.∘ f ≡ F₁ a 𝒟.∘ (F₁ b 𝒟.∘ f)
  pushl = 𝒟.pushl expand

  pushr : f 𝒟.∘ F₁ c ≡ (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b
  pushr = 𝒟.pushr expand

module _ (p : a 𝒞.∘ c ≡ b 𝒞.∘ d) where
  weave : F₁ a 𝒟.∘ F₁ c ≡ F₁ b 𝒟.∘ F₁ d
  weave = sym (F-∘ a c) ∙ ap F₁ p ∙ F-∘ b d

  extendl : F₁ a 𝒟.∘ (F₁ c 𝒟.∘ f) ≡ F₁ b 𝒟.∘ (F₁ d 𝒟.∘ f)
  extendl = 𝒟.extendl weave

  extendr : (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ c ≡ (f 𝒟.∘ F₁ b) 𝒟.∘ F₁ d
  extendr = 𝒟.extendr weave

  extend-inner :
    f 𝒟.∘ F₁ a 𝒟.∘ F₁ c 𝒟.∘ g ≡ f 𝒟.∘ F₁ b 𝒟.∘ F₁ d 𝒟.∘ g
  extend-inner = 𝒟.extend-inner weave
```

## Cancellation

```agda
module _ (inv : a 𝒞.∘ b ≡ 𝒞.id) where
  annihilate : F₁ a 𝒟.∘ F₁ b ≡ 𝒟.id
  annihilate = sym (F-∘ a b) ∙ ap F₁ inv ∙ F-id

  cancell : F₁ a 𝒟.∘ (F₁ b 𝒟.∘ f) ≡ f
  cancell = 𝒟.cancell annihilate

  cancelr : (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b ≡ f
  cancelr = 𝒟.cancelr annihilate

  insertl : f ≡ F₁ a 𝒟.∘ (F₁ b 𝒟.∘ f)
  insertl = 𝒟.insertl annihilate

  insertr : f ≡ (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b
  insertr = 𝒟.insertr annihilate

  cancel-inner : (f 𝒟.∘ F₁ a) 𝒟.∘ (F₁ b 𝒟.∘ g) ≡ f 𝒟.∘ g
  cancel-inner = 𝒟.cancel-inner annihilate
```

## Notation

Writing `ap F₁ p` is somewhat clunky, so we define a bit of notation
to make it somewhat cleaner.

```agda
⟨_⟩ : a ≡ b → F₁ a ≡ F₁ b
⟨_⟩ = ap F₁
```

