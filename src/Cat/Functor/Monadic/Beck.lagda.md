---
description: |
  We define Beck's coequalisers, and establish their role in the crude
  monadicity theorem.
---
```agda
open import Cat.Functor.Adjoint.Monadic
open import Cat.Functor.Adjoint.Monad
open import Cat.Diagram.Coequaliser
open import Cat.Functor.Adjoint
open import Cat.Diagram.Monad
open import Cat.Prelude

import Cat.Functor.Reasoning as F-r
import Cat.Reasoning as C-r

module
  Cat.Functor.Monadic.Beck
  {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
  {F : Functor C D} {G : Functor D C}
  (F⊣G : F ⊣ G)
  where
```

<!--
```agda
private
  module F = F-r F
  module G = F-r G
  module C = C-r C
  module D = C-r D
  module GF = F-r (G F∘ F)
  module T = Monad (Adjunction→Monad F⊣G)
private
  T : Monad C
  T = Adjunction→Monad F⊣G
  C^T : Precategory _ _
  C^T = Eilenberg-Moore C T
open _⊣_ F⊣G
open _=>_
open Algebra-hom
open Algebra-on
```
-->

# Beck's coequaliser

Let $F : \ca{C} \to \ca{D}$ be a functor admitting a [right adjoint]
$U : \ca{D} \to \ca{C}$. Recall that every adjunction [induces] a
[monad] $UF$ (which we will call $T$ for short) on the category
$\ca{C}$, and a "[comparison]" functor $K : \ca{D} \to \ca{C}^{T}$ into
the [Eilenberg-Moore category] of $T$. In this module we will lay out a
sufficient condition for the functor $K$ to have a left adjoint, which
we call $K^{-1}$ (`Comparison⁻¹`). Let us first establish a result about
the presentation of $T$-[algebras] by "generators and relations".

[monad]: Cat.Diagram.Monad.html
[induces]: Cat.Functor.Adjoint.Monad.html
[right adjoint]: Cat.Functor.Adjoint.html
[comparison]: Cat.Functor.Adjoint.Monadic.html
[algebras]: Cat.Diagram.Monad.html#algebras-over-a-monad
[Eilenberg-Moore category]: Cat.Diagram.Monad.html#eilenberg-moore-category

Suppose that we are given a $T$-algebra $(A, \nu)$. Note that $(TA,
\mu)$ is also a $T$-algebra, namely the free $T$-algebra on the object
$A$. Let us illustrate this with a concrete example: Suppose we have the
cyclic group $\bb{Z}/n\bb{Z}$, for some natural number $n$, which we
regard as a subgroup of $\bb{Z}$. The corresponding algebra $(TA, \mu)$
would be the [free group] on one generator^[the group of integers]
whence^[I was feeling pretentious when I wrote this sentence] we
conclude that, in general, this "free-on-underlying" $(TA, \mu)$ algebra
is very far from being the $(A, \nu)$ algebra we started with.

[free group]: Algebra.Group.Free.html

Still, motivated by our $\bb{Z}/n\bb{Z}$ example, it feels like we
should be able to [quotient] the algebra $(TA, \mu)$ by some set of
_relations_ and get back the algebra $(A, \nu)$ we started with. This is
absolutely true, and it's true even when the category of $T$-algebras is
lacking in quotients! In particular, we have the following theorem:

[quotient]: Data.Set.Coequaliser.html#quotients

**Theorem**. Every $T$-algebra $(A, \nu)$ is the [coequaliser] of the diagram

[coequaliser]: Cat.Diagram.Coequaliser.html

~~~{.quiver .short-15}
\[\begin{tikzcd}
  {T^2A} & {TA} & {A,}
  \arrow["\mu", shift left=1, from=1-1, to=1-2]
  \arrow["T\nu"', shift right=1, from=1-1, to=1-2]
  \arrow["\nu", from=1-2, to=1-3]
\end{tikzcd}\]
~~~

called the **Beck coequaliser** (of $A$). Furthermore, this coequaliser
is _reflexive_ in $\ca{C}^T$, meaning that the arrows $\mu$ and $T\nu$
have a common right inverse. Elaborating a bit, this theorem lets us
decompose any $T$-algebra $(A, \nu)$ into a canonical presentation of
$A$ by generators and relations, as a quotient of a free algebra by a
relation (induced by) the fold $\nu$.

<!--
```agda
module _ (Aalg : Algebra C T) where
  private
    A = Aalg .fst
    module A = Algebra-on (Aalg .snd)

    TA : Algebra C T
    TA = Free C T .Functor.F₀ A

    TTA : Algebra C T
    TTA = Free C T .Functor.F₀ (T.M₀ A)

    mult : Algebra-hom C T TTA TA
    mult .morphism = T.mult .η _
    mult .commutes = sym T.mult-assoc

    fold : Algebra-hom C T TTA TA
    fold .morphism = T.M₁ A.ν
    fold .commutes =
      T.M₁ A.ν C.∘ T.mult .η _        ≡˘⟨ T.mult .is-natural _ _ _ ⟩
      T.mult .η _ C.∘ T.M₁ (T.M₁ A.ν) ∎
```
-->

**Proof**. The proof is by calculation, applying the monad laws where
applicable, so we present it without much further commentary. Observe
that $\nu$ coequalises $\mu$ and $T\nu$ essentially by the definition of
being an algebra map. Note that we do not make use of the fact that the
monad $T$ was given by a _specified_ adjunction $F \dashv U$ in the
proof, and any adjunction presenting $T$ will do.

```agda
  open is-coequaliser
  algebra-is-coequaliser
    : is-coequaliser C^T {A = TTA} {B = TA} {E = Aalg}
      mult fold (record { morphism = A.ν ; commutes = sym A.ν-mult })
  algebra-is-coequaliser .coequal = Algebra-hom-path C $
    A.ν C.∘ T.mult .η _ ≡˘⟨ A.ν-mult ⟩
    A.ν C.∘ T.M₁ A.ν    ∎
```

The colimiting map from $(A, \nu)$ to some other algebra $(F, \nu')$
which admits a map $e' : (TA, \mu) \to (F, \nu')$ is given by the
composite

$$
A \xto{\eta} TA \xto{e'} F\text{,}
$$

which is a map of algebras by a long computation, and satisfies the
properties of a coequalising map by slightly shorter computations, which
can be seen below. Uniqueness of this map follows almost immediately
from the algebra laws.

```agda
  algebra-is-coequaliser .coequalise {F = F} {e'} p .morphism =
    e' .morphism C.∘ T.unit .η A
  algebra-is-coequaliser .coequalise {F = F} {e'} p .commutes =
    (e' .morphism C.∘ unit.η A) C.∘ A.ν                   ≡⟨ C.extendr (unit.is-natural _ _ _) ⟩
    (e' .morphism C.∘ T.M₁ A.ν) C.∘ unit.η  (T.M₀ A)      ≡˘⟨ ap morphism p C.⟩∘⟨refl ⟩
    (e' .morphism C.∘ T.mult .η A) C.∘ unit.η  (T.M₀ A)   ≡⟨ C.cancelr T.right-ident ⟩
    e' .morphism                                          ≡⟨ C.intror (sym (T.M-∘ _ _) ∙ ap T.M₁ A.ν-unit ∙ T.M-id) ⟩
    e' .morphism C.∘ T.M₁ A.ν C.∘ T.M₁ (unit.η A)         ≡⟨ C.pulll (sym (ap morphism p)) ⟩
    (e' .morphism C.∘ T.mult .η A) C.∘ T.M₁ (unit.η A)    ≡⟨ C.pushl (e' .commutes) ⟩
    F .snd .ν C.∘ T.M₁ (e' .morphism) C.∘ T.M₁ (unit.η A) ≡˘⟨ C.refl⟩∘⟨ T.M-∘ _ _ ⟩
    F .snd .ν C.∘ T.M₁ (e' .morphism C.∘ unit.η A)        ∎
  algebra-is-coequaliser .universal {F = F} {e'} {p} = Algebra-hom-path C $
    (e' .morphism C.∘ unit.η _) C.∘ A.ν          ≡⟨ C.extendr (unit.is-natural _ _ _) ⟩
    (e' .morphism C.∘ T.M₁ A.ν) C.∘ unit.η  _    ≡˘⟨ ap morphism p C.⟩∘⟨refl ⟩
    (e' .morphism C.∘ T.mult .η _) C.∘ unit.η  _ ≡⟨ C.cancelr T.right-ident ⟩
    e' .morphism                                 ∎
  algebra-is-coequaliser .unique {F = F} {e'} {p} {colim} q =
    Algebra-hom-path C $ sym $
      e' .morphism C.∘ unit.η A              ≡⟨ ap morphism q C.⟩∘⟨refl ⟩
      (colim .morphism C.∘ A.ν) C.∘ unit.η A ≡⟨ C.cancelr A.ν-unit ⟩
      colim .morphism                        ∎
```

# Presented algebras

The lemma above says that every algebra which exists can be presented by
generators and relations; The relations are encoded by the pair of maps
$T^2A \tto TA$ in Beck's coequaliser, above. But what about the
converse?  The following lemma says that, if every algebra presented by
generators-and-relations (encoded by a parallel pair $T^2A \tto TA$) has
a coequaliser _in $\ca{D}$_, then the comparison functor $\ca{D} \to
\ca{C}^T$ has a left adjoint.

<!--
```agda
module _
  (has-coeq : (M : Algebra C T) → Coequaliser D (F.₁ (M .snd .ν)) (counit.ε _))
  where

  open Coequaliser
  open Functor
```
-->

On objects, this left adjoint acts by sending each algebra $M$ to the
coequaliser of (the diagram underlying) its Beck coequaliser. In a
sense, this is "the best approximation in $\ca{D}$ of the algebra". The
action on morphisms is uniquely determined since it's a map out of a
coequaliser.

If we consider the comparison functor as being "the $T$-algebra
underlying an object of $\ca{D}$", then the functor we construct below
is the "free object of $\ca{D}$ on a $T$-algebra". Why is this
adjunction relevant, though? Its failure to be an equivalence measures
just how far our original adjunction is from being monadic, that is, how
far $\ca{D}$ is from being the category of $T$-algebras.

```agda
  Comparison⁻¹ : Functor (Eilenberg-Moore C T) D
  Comparison⁻¹ .F₀ = coapex ⊙ has-coeq
  Comparison⁻¹ .F₁ {X} {Y} alg-map =
    has-coeq X .coequalise {e′ = e′} path where
      e′ : D.Hom (F.F₀ (X .fst)) (Comparison⁻¹ .F₀ Y)
      e′ = has-coeq Y .coeq D.∘ F.₁ (alg-map .morphism)
```
<!--
```agda
      abstract
        path : e′ D.∘ F.₁ (X .snd .ν) ≡ e′ D.∘ counit.ε (F.₀ (X .fst))
        path =
          (has-coeq Y .coeq D.∘ F.₁ (alg-map .morphism)) D.∘ F.₁ (X .snd .ν)      ≡⟨ D.pullr (F.weave (alg-map .commutes)) ⟩
          has-coeq Y .coeq D.∘ F.₁ (Y .snd .ν) D.∘ F.₁ (T.M₁ (alg-map .morphism)) ≡⟨ D.extendl (has-coeq Y .coequal) ⟩
          has-coeq Y .coeq D.∘ counit.ε _ D.∘ F.₁ (T.M₁ (alg-map .morphism))      ≡⟨ D.pushr (counit.is-natural _ _ _) ⟩
          (has-coeq Y .coeq D.∘ F.₁ (alg-map .morphism)) D.∘ counit.ε _           ∎
  Comparison⁻¹ .F-id {X} = sym $ has-coeq X .unique (F.elimr refl ∙ D.introl refl)
  Comparison⁻¹ .F-∘ {X} f g = sym $ has-coeq X .unique $ sym $
       D.pullr (has-coeq X .universal)
    ·· D.pulll (has-coeq _ .universal)
    ·· F.pullr refl

  open _⊣_
```
-->

The adjunction unit and counit are again very simple, and it's evident
to a human looking at them that they satisfy the triangle identities
(and are algebra homomorphisms). Agda is not as easy to convince,
though, so we leave the computation folded up for the bravest of
readers.

```agda
  Comparison⁻¹⊣Comparison : Comparison⁻¹ ⊣ Comparison F⊣G
  Comparison⁻¹⊣Comparison .unit .η x .morphism =
    G.₁ (has-coeq _ .coeq) C.∘ T.unit .η _
  Comparison⁻¹⊣Comparison .counit .η x =
    has-coeq _ .coequalise (F⊣G .counit.is-natural _ _ _)
```

<details>
<summary>Nah, really, it's quite ugly.</summary>

```agda
  Comparison⁻¹⊣Comparison .unit .η x .commutes =
      C.pullr (T.unit .is-natural _ _ _)
    ∙ G.extendl (has-coeq _ .coequal)
    ∙ C.elimr (F⊣G .zag)
    ∙ G.intror (F⊣G .zig)
    ∙ G.weave (D.pulll (sym (F⊣G .counit.is-natural _ _ _)) ∙ D.pullr (sym (F.F-∘ _ _)))
  Comparison⁻¹⊣Comparison .unit .is-natural x y f = Algebra-hom-path C $
    (G.₁ (has-coeq y .coeq) C.∘ T.unit.η _) C.∘ f .morphism                    ≡⟨ C.pullr (T.unit.is-natural _ _ _) ⟩
    G.₁ (has-coeq y .coeq) C.∘ T.M₁ (f .morphism) C.∘ T.unit .η (x .fst)       ≡⟨ C.pulll (sym (G.F-∘ _ _)) ⟩
    G.₁ (has-coeq y .coeq D.∘ F.₁ (f .morphism)) C.∘ T.unit .η (x .fst)        ≡⟨ ap G.₁ (sym (has-coeq _ .universal)) C.⟩∘⟨refl ⟩
    G.₁ (has-coeq x .coequalise _ D.∘ has-coeq x .coeq) C.∘ T.unit .η (x .fst) ≡⟨ C.pushl (G.F-∘ _ _) ⟩
    G.₁ (has-coeq x .coequalise _) C.∘ G.₁ (has-coeq x .coeq) C.∘ T.unit.η _   ∎
  Comparison⁻¹⊣Comparison .counit .is-natural x y f =
      has-coeq (F₀ (Comparison F⊣G) x) .unique
        {p = ap₂ D._∘_ (F⊣G .counit.is-natural _ _ _) refl
          ·· D.pullr (F⊣G .counit.is-natural _ _ _)
          ·· D.pulll (sym (F⊣G .counit.is-natural _ _ _))}
        (sym (D.pullr (has-coeq _ .universal) ∙ D.pulll (has-coeq _ .universal)))
    ∙ sym (has-coeq _ .unique (F⊣G .counit.is-natural _ _ _ ∙ D.pushr (sym (has-coeq _ .universal))))
  Comparison⁻¹⊣Comparison .zig =
    has-coeq _ .unique {e′ = has-coeq _ .coeq} {p = has-coeq _ .coequal}
      (sym (D.pullr (has-coeq _ .universal)
          ∙ D.pulll (has-coeq _ .universal)
          ∙ ap₂ D._∘_ refl (F.F-∘ _ _) ∙ D.pulll (F⊣G .counit.is-natural _ _ _)
          ∙ D.cancelr (F⊣G .zig)))
    ∙ sym (has-coeq _ .unique (D.introl refl))
  Comparison⁻¹⊣Comparison .zag = Algebra-hom-path C $
    G.pulll (has-coeq _ .universal) ∙ F⊣G .zag
```

</details>
