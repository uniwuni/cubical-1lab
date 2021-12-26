```agda
open import 1Lab.Prelude

module Data.Predicate where
```

# Predicates

We define the type of __predicates__ (or __subsets__) on a type $A$ as
all $A$-indexed types that are propositional, that is, functions
`f : A → Type` such that any two `x, y : f a` are equal. This condition
makes it impossible for a predicate to hold on a value in distinct ways.

Note that we need to quantify over an additional universe level predicate
since we do not assume impredicative propositions, that is, TODO.

```agda
record Predicate {ℓ} (A : Type ℓ) (ℓ' : _) : Type (ℓ ⊔ lsuc ℓ') where
  constructor makePredicate
  field
    contains : A → Type ℓ'
    isPointwiseProp : (x : A) → isProp (contains x)
```

From this, it is also possible to construct the other common
constructive definition of predicates, that is, predicates as
`embeddings`{.Agda isEmbedding} from another type. Since `P x` for some
predicate `P : Predicate A _ ` is always propositional, we can inject
from `Σ P` into `A`, as is shown in `Subset-proj-embedding`{.Agda}

```agda
  embed : Σ contains ↪ A
  embed .fst = fst
  embed .snd {x = x} {y = y} =
    Subset-proj-embedding isPointwiseProp

  is-set-subtype-is-set : isSet A → isSet (Σ contains)
  is-set-subtype-is-set isSet = isHLevelΣ 2 isSet
    λ x → isHLevel-suc 1 (isPointwiseProp x)
  
open Predicate public
```

We also define what it means for a predicate to be closed under unary
and binary operations, a statement that is itself a predicate on the
operations:

```agda
module _ {ℓ ℓ'} {A : Type ℓ} (P : Predicate A ℓ') where
  isClosed-unary : Predicate (A → A) (ℓ ⊔ ℓ')
  isClosed-unary .contains f = (x : _) → P .contains x → P .contains (f x) 
  isClosed-unary .isPointwiseProp f x y =
    funext λ x → funext λ prf → P .isPointwiseProp (f x) _ _

  isClosed-binary : Predicate (A → A → A) (ℓ ⊔ ℓ')
  isClosed-binary .contains f =
    (x y : _) → P .contains x → P .contains y → P .contains (f x y)
  isClosed-binary .isPointwiseProp f x y =
    funext λ x → funext λ y → funext λ prf → funext λ prf2 →
      P .isPointwiseProp (f x y) _ _
```

# Examples

On any type, we can also define the two very basic subsets: the empty set,
whose predicate does not apply to any element, as well as the "universe"
subset, whose predicate always holds.

```agda
∅ univ : ∀ {ℓ ℓ'} {A : Type ℓ} → Predicate A ℓ'
∅ {ℓ' = ℓ'} .contains = λ x → Lift ℓ' ⊥
∅ .isPointwiseProp a () ()

univ {ℓ' = ℓ'} .contains = λ x → Lift ℓ' ⊤
univ .isPointwiseProp a (lift tt) (lift tt) = refl
```

This also allows us to show that the embedding induced by `univ`{.Agda}
is an equivalence.

```agda
univ-embed≃ : ∀ {ℓ ℓ'} {A : Type ℓ} → isEquiv
  (Predicate.embed (univ {ℓ' = ℓ'} {A = A}) .fst)
univ-embed≃ = isIso→isEquiv
  (iso (λ z → z , lift tt)
       (λ x → refl)
       (λ x → refl))
```

Every function $f$ also defines a predicate on its codomain, the function's
__image__: Any value $x$ is an element of the image of $f$ if there is some
$y$ such that $f(y) = x$ holds. Since there could be multiple such $y$,
and, in the case that non-sets are involved, even multiple such paths,
truncating the proofs is necessary to ensure propositionality.

```agda
image : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Predicate B (ℓ ⊔ ℓ')
image f .contains y = ∃[ x ∈ _ ] (f x ≡ y) 
image f .isPointwiseProp x = isProp-∥-∥
```
However, a exception to that is provided by embeddings into sets, as in
their case, every element of the codomain is reached at most once. This,
combined with the fact that the codomain is a set, allows one to omit
the truncation.

```agda
embedding-set-image :
  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isSet B → A ↪ B → Predicate B (ℓ ⊔ ℓ')
embedding-set-image isSet (f , isEmbed) .contains y =
  Σ[ x ∈ _ ] (f x ≡ y)
embedding-set-image isSet (f , isEmbed)
  .isPointwiseProp x (a1 , prf1) (a2 , prf2) =
    Σ≡Prop (λ a prf prf' → isSet (f a) x prf prf')
    (embedding→injective f isEmbed (prf1 ∙ sym prf2))
```
