```agda
open import Cat.Instances.Functor.Duality
open import Cat.Instances.Functor
open import Cat.Prelude

import Cat.Reasoning

module Cat.Diagram.Duals {o h} (C : Precategory o h) where
```

<!--
```agda
import Cat.Reasoning C as C
```
-->

# Dualities of diagrams

Following [Hu and Carette][agda-categories], we've opted to have
_different_ concrete definitions for diagrams and their opposites. In
particular, we have the following pairs of "redundant" definitions:

[agda-categories]: https://arxiv.org/abs/2005.07059

- Products and coproducts
- Pullbacks and pushouts
- Equalisers and coequalisers
- Terminal objects and initial objects

For all four of the above pairs, we have that one in $C$ is the other in
$C\op$. We prove these correspondences here:

## Co/products

```agda
import Cat.Diagram.Product (C ^op) as Co-prod
import Cat.Diagram.Coproduct C as Coprod

is-co-product→is-coproduct
  : ∀ {A B P} {i1 : C.Hom A P} {i2 : C.Hom B P}
  → Co-prod.is-product i1 i2 → Coprod.is-coproduct i1 i2
is-co-product→is-coproduct isp =
  record
    { [_,_]      = isp.⟨_,_⟩
    ; in₀∘factor = isp.π₁∘factor
    ; in₁∘factor = isp.π₂∘factor
    ; unique     = isp.unique
    }
  where module isp = Co-prod.is-product isp

is-coproduct→is-co-product
  : ∀ {A B P} {i1 : C.Hom A P} {i2 : C.Hom B P}
  → Coprod.is-coproduct i1 i2 → Co-prod.is-product i1 i2
is-coproduct→is-co-product iscop =
  record
    { ⟨_,_⟩     = iscop.[_,_]
    ; π₁∘factor = iscop.in₀∘factor
    ; π₂∘factor = iscop.in₁∘factor
    ; unique    = iscop.unique
    }
  where module iscop = Coprod.is-coproduct iscop
```

## Co/equalisers

```agda
import Cat.Diagram.Equaliser (C ^op) as Co-equ
import Cat.Diagram.Coequaliser C as Coequ

is-co-equaliser→is-coequaliser
  : ∀ {A B E} {f g : C.Hom A B} {coeq : C.Hom B E}
  → Co-equ.is-equaliser f g coeq → Coequ.is-coequaliser f g coeq
is-co-equaliser→is-coequaliser eq =
  record
    { coequal    = eq.equal
    ; coequalise = eq.limiting
    ; universal  = eq.universal
    ; unique     = eq.unique
    }
  where module eq = Co-equ.is-equaliser eq

is-coequaliser→is-co-equaliser
  : ∀ {A B E} {f g : C.Hom A B} {coeq : C.Hom B E}
  → Coequ.is-coequaliser f g coeq → Co-equ.is-equaliser f g coeq
is-coequaliser→is-co-equaliser coeq =
  record
    { equal     = coeq.coequal
    ; limiting  = coeq.coequalise
    ; universal = coeq.universal
    ; unique    = coeq.unique
    }
  where module coeq = Coequ.is-coequaliser coeq
```

## Initial/terminal

```agda
import Cat.Diagram.Terminal (C ^op) as Coterm
import Cat.Diagram.Initial C as Init

is-initial→is-coterminal
  : ∀ {A} → Coterm.is-terminal A → Init.is-initial A
is-initial→is-coterminal x = x

is-coterminal→is-initial
  : ∀ {A} → Init.is-initial A → Coterm.is-terminal A
is-coterminal→is-initial x = x
```

## Pullback/pushout

```agda
import Cat.Diagram.Pullback (C ^op) as Co-pull
import Cat.Diagram.Pushout C as Push

is-co-pullback→is-pushout
  : ∀ {P X Y Z} {p1 : C.Hom X P} {f : C.Hom Z X} {p2 : C.Hom Y P} {g : C.Hom Z Y}
  → Co-pull.is-pullback p1 f p2 g → Push.is-pushout f p1 g p2
is-co-pullback→is-pushout pb =
  record
    { square = pb.square
    ; colimiting = pb.limiting
    ; i₁∘colimiting = pb.p₁∘limiting
    ; i₂∘colimiting = pb.p₂∘limiting
    ; unique = pb.unique
    }
  where module pb = Co-pull.is-pullback pb

is-pushout→is-co-pullback
  : ∀ {P X Y Z} {p1 : C.Hom X P} {f : C.Hom Z X} {p2 : C.Hom Y P} {g : C.Hom Z Y}
  → Push.is-pushout f p1 g p2 → Co-pull.is-pullback p1 f p2 g
is-pushout→is-co-pullback po =
  record
    { square      = po.square
    ; limiting    = po.colimiting
    ; p₁∘limiting = po.i₁∘colimiting
    ; p₂∘limiting = po.i₂∘colimiting
    ; unique      = po.unique
    }
  where module po = Push.is-pushout po
```

## Co/cones

```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial

module _ {o ℓ} {J : Precategory o ℓ} {F : Functor J C} where
  open Functor F renaming (op to F^op)

  open Cocone-hom
  open Cone-hom
  open Terminal
  open Initial
  open Cocone
  open Cone

  Co-cone→Cocone : Cone F^op → Cocone F
  Co-cone→Cocone cone .coapex = cone .apex
  Co-cone→Cocone cone .ψ = cone .ψ
  Co-cone→Cocone cone .commutes = cone .commutes

  Cocone→Co-cone : Cocone F → Cone F^op
  Cocone→Co-cone cone .apex     = cone .coapex
  Cocone→Co-cone cone .ψ        = cone .ψ
  Cocone→Co-cone cone .commutes = cone .commutes

  Cocone→Co-cone→Cocone : ∀ K → Co-cone→Cocone (Cocone→Co-cone K) ≡ K
  Cocone→Co-cone→Cocone K i .coapex = K .coapex
  Cocone→Co-cone→Cocone K i .ψ = K .ψ
  Cocone→Co-cone→Cocone K i .commutes = K .commutes

  Co-cone→Cocone→Co-cone : ∀ K → Cocone→Co-cone (Co-cone→Cocone K) ≡ K
  Co-cone→Cocone→Co-cone K i .apex = K .apex
  Co-cone→Cocone→Co-cone K i .ψ = K .ψ
  Co-cone→Cocone→Co-cone K i .commutes = K .commutes

  Co-cone-hom→Cocone-hom
    : ∀ {x y}
    → Cone-hom F^op y x
    → Cocone-hom F (Co-cone→Cocone x) (Co-cone→Cocone y)
  Co-cone-hom→Cocone-hom ch .hom = ch .hom
  Co-cone-hom→Cocone-hom ch .commutes o = ch .commutes o

  Cocone-hom→Co-cone-hom
    : ∀ {x y}
    → Cocone-hom F x y
    → Cone-hom F^op (Cocone→Co-cone y) (Cocone→Co-cone x)
  Cocone-hom→Co-cone-hom ch .hom = ch .hom
  Cocone-hom→Co-cone-hom ch .commutes = ch .commutes
```

## Co/limits

```agda
  Colimit→Co-limit
    : Colimit F → Limit F^op
  Colimit→Co-limit colim = lim where
    lim : Limit F^op
    lim .top = Cocone→Co-cone (colim .bot)
    lim .has⊤ co-cone =
      retract→is-contr f g fg
        (colim .has⊥ (Co-cone→Cocone co-cone))
      where
        f : _ → _
        f x = subst (λ e → Cone-hom F^op e _)
          (Co-cone→Cocone→Co-cone _)
          (Cocone-hom→Co-cone-hom x)

        g : _ → _
        g x = subst (λ e → Cocone-hom F e _)
          (Cocone→Co-cone→Cocone _)
          (Co-cone-hom→Cocone-hom x)

        fg : is-left-inverse f g
        fg x = Cone-hom-path _ (transport-refl _ ∙ transport-refl _)

  Co-limit→Colimit
    : Limit F^op → Colimit F
  Co-limit→Colimit lim = colim where
    colim : Colimit F
    colim .bot = Co-cone→Cocone (lim .top)
    colim .has⊥ cocon =
      retract→is-contr f g fg
        (lim .has⊤ (Cocone→Co-cone cocon))
      where
        f : _ → _
        f x = subst (λ e → Cocone-hom F _ e)
          (Cocone→Co-cone→Cocone _)
          (Co-cone-hom→Cocone-hom x)

        g : _ → _
        g x = subst (λ e → Cone-hom F^op _ e)
          (Co-cone→Cocone→Co-cone _)
          (Cocone-hom→Co-cone-hom x)

        fg : is-left-inverse f g
        fg x = Cocone-hom-path _ (transport-refl _ ∙ transport-refl _)

module _ {o ℓ} {J : Precategory o ℓ} {F F′ : Functor J C} where
  private module JC = Cat.Reasoning Cat[ J , C ]

  Colimit-ap-iso : F JC.≅ F′ → Colimit F → Colimit F′
  Colimit-ap-iso f cl =
    Co-limit→Colimit (Limit-ap-iso (op-natural-iso f) (Colimit→Co-limit cl))
```
