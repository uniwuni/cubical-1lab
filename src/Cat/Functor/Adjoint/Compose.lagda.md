---
description: We compute the composite of two adjunctions.
---
```agda
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Reasoning

module Cat.Functor.Adjoint.Compose
```

# Composition of adjunctions

Suppose we have four functors $F \dashv G$ and $L \dashv R$, such that
they "fit together", i.e. the composites $LF$ and $GR$ both exist. What
can we say about their composites? The hope is that they would again be
adjoints, and this is indeed the case.

We prove this here by explicitly exhibiting the adjunction natural
transformations and the triangle identities, which is definitely
suboptimal for readability, but is the most efficient choice in terms of
the resulting Agda program.

```agda
    {o ℓ o₂ ℓ₂ o₃ ℓ₃}
    {A : Precategory o ℓ} {B : Precategory o₂ ℓ₂}
    {C : Precategory o₃ ℓ₃}
    {F : Functor A B} {G : Functor B A}
    {L : Functor B C} {R : Functor C B}
    (F⊣G : F ⊣ G)
    (L⊣R : L ⊣ R)
  where
```

<!--
```agda
private
  module fg = _⊣_ F⊣G
  module lr = _⊣_ L⊣R
  module A = Cat.Reasoning A
  module B = Cat.Reasoning B
  module C = Cat.Reasoning C
  module F = Functor F
  module G = Functor G
  module L = Functor L
  module R = Functor R
  open _⊣_
  open _=>_
  module LF = Functor (L F∘ F)
  module GR = Functor (G F∘ R)
```
-->

```agda
LF⊣GR : (L F∘ F) ⊣ (G F∘ R)
LF⊣GR .unit .η x          = G.₁ (lr.unit.η _) A.∘ fg.unit.η _
LF⊣GR .counit .η x        = lr.counit.ε _ C.∘ L.₁ (fg.counit.ε _)

LF⊣GR .unit .is-natural x y f = path where abstract
  path : LF⊣GR .unit .η y A.∘ f ≡ GR.₁ (LF.₁ f) A.∘ LF⊣GR .unit .η x
  path =
    (G.₁ (lr.unit.η _) A.∘ fg.unit.η _) A.∘ f                ≡⟨ A.pullr (fg.unit.is-natural _ _ _) ⟩
    G.₁ (lr.unit.η _) A.∘ G.₁ (F.₁ f) A.∘ fg.unit.η _        ≡⟨ A.pulll (sym (G.F-∘ _ _)) ⟩
    G.₁ (lr.unit.η _ B.∘ F.₁ f) A.∘ fg.unit.η _              ≡⟨ ap₂ A._∘_ (ap G.₁ (lr.unit.is-natural _ _ _)) refl ⟩
    G.₁ (R.₁ (L.₁ (F.₁ f)) B.∘ lr.unit .η _) A.∘ fg.unit.η _ ≡⟨ A.pushl (G.F-∘ _ _) ⟩
    GR.₁ (LF.₁ f) A.∘ G.₁ (lr.unit.η _) A.∘ (fg.unit.η _)    ∎

LF⊣GR .counit .is-natural x y f = path where abstract
  path : LF⊣GR .counit .η y C.∘ LF.₁ (GR.₁ f) ≡ f C.∘ LF⊣GR .counit .η x
  path =
    (lr.counit.ε _ C.∘ L.₁ (fg.counit.ε _)) C.∘ LF.₁ (GR.₁ f) ≡⟨ C.pullr (sym (L.F-∘ _ _)) ⟩
    lr.counit.ε _ C.∘ L.₁ (fg.counit.ε _ B.∘ F.₁ (GR.₁ f))    ≡⟨ ap (lr.counit.ε _ C.∘_) (ap L.₁ (fg.counit.is-natural _ _ _)) ⟩
    lr.counit.ε _ C.∘ L.₁ (R.F₁ f B.∘ fg.counit.ε _)          ≡⟨ ap (lr.counit.ε _ C.∘_) (L.F-∘ _ _) ⟩
    lr.counit.ε _ C.∘ L.₁ (R.F₁ f) C.∘ L.₁ (fg.counit.ε _)    ≡⟨ C.extendl (lr.counit.is-natural _ _ _) ⟩
    f C.∘ lr.counit.ε _ C.∘ L.₁ (fg.counit.ε _)               ∎

LF⊣GR .zig =
  (lr.counit.ε _ C.∘ L.₁ (fg.counit.ε _)) C.∘ LF.₁ (G.₁ (lr.unit.η _) A.∘ fg.unit.η _)           ≡⟨ ap₂ C._∘_ refl (LF.F-∘ _ _) ⟩
  (lr.counit.ε _ C.∘ L.₁ (fg.counit.ε _)) C.∘ LF.₁ (G.₁ (lr.unit.η _)) C.∘ LF.₁ (fg.unit.η _)    ≡⟨ solve C ⟩
  lr.counit.ε _ C.∘ ((L.₁ (fg.counit.ε _) C.∘ LF.₁ (G.₁ (lr.unit.η _))) C.∘ LF.₁ (fg.unit.η _))  ≡⟨ ap₂ C._∘_ refl (ap₂ C._∘_ (sym (L.F-∘ _ _) ·· ap L.₁ (fg.counit.is-natural _ _ _) ·· L.F-∘ _ _) refl) ⟩
  lr.counit.ε _ C.∘ (L.₁ (lr.unit.η _) C.∘ L.₁ (fg.counit.ε _)) C.∘ LF.₁ (fg.unit.η _)           ≡⟨ solve C ⟩
  (lr.counit.ε _ C.∘ L.₁ (lr.unit.η _)) C.∘ (L.₁ (fg.counit.ε _) C.∘ LF.₁ (fg.unit.η _))         ≡⟨ ap₂ C._∘_ lr.zig (sym (L.F-∘ _ _) ∙ ap L.₁ fg.zig ∙ L.F-id) ⟩
  C.id C.∘ C.id                                                                                  ≡⟨ C.eliml refl ⟩
  C.id                                                                                           ∎

LF⊣GR .zag =
  GR.₁ (lr.counit.ε _ C.∘ L.₁ (fg.counit.ε _)) A.∘ G.₁ (lr.unit.η _) A.∘ fg.unit .η _       ≡⟨ A.pulll (sym (G.F-∘ _ _)) ⟩
  G.₁ (R.₁ (lr.counit.ε _ C.∘ L.₁ (fg.counit.ε _)) B.∘ lr.unit.η _) A.∘ fg.unit .η _        ≡⟨ ap₂ A._∘_ (ap G.₁ (sym (B.pulll (sym (R.F-∘ _ _))))) refl ⟩
  G.₁ (R.₁ (lr.counit.ε _) B.∘ R.₁ (L.₁ (fg.counit.ε _)) B.∘ lr.unit.η _) A.∘ fg.unit .η _  ≡⟨ ap₂ A._∘_ (ap G.₁ (ap₂ B._∘_ refl (sym (lr.unit.is-natural _ _ _)))) refl ⟩
  G.₁ (R.₁ (lr.counit.ε _) B.∘ lr.unit.η _ B.∘ fg.counit.ε _) A.∘ fg.unit .η _              ≡⟨ ap₂ A._∘_ (ap G.₁ (B.cancell lr.zag)) refl ⟩
  G.₁ (fg.counit.ε _) A.∘ fg.unit .η _                                                      ≡⟨ fg.zag ⟩
  A.id                                                                                      ∎
```
