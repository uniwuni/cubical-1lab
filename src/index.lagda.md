```agda
module index where
```

# 1lab {style="margin-top: 0;"}

A formalised, cross-linked reference resource for cubical methods in
Homotopy Type Theory. Unlike the [HoTT book], the 1lab is not a "linear"
resource: Concepts are presented as a directed graph, with links
indicating _dependencies_. For instance, the statement of the univalence
principle depends on [universes], [identifications] and [equivalences].
In addition to the hyperlinked "web of concepts" provided by the Agda
code, there is a short introduction to homotopy type theory: **[Start
here](1Lab.intro.html)**.

[HoTT book]: https://homotopytypetheory.org/book/
[universes]: agda://1Lab.Type
[identifications]: agda://1Lab.Path
[equivalences]: agda://1Lab.Equiv

<!--
```agda
open import 1Lab.Type
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Univalence
open import 1Lab.HLevel
```
-->

```agda
_ : ∀ {ℓ} {A B : Type ℓ} → is-equiv (path→equiv {A = A} {B})
_ = univalence
```

The purpose of the "web of concepts" approach is to let each reader
approach the 1lab at their own pace: If you already know what all of the
code above means, you can click on `univalence`{.Agda} to be taken
directly to the construction of the equivalence --- but if you _don't_,
you can click on other definitions like `is-equiv`{.Agda} and
`path→equiv`{.Agda}, and in turn explore the dependencies of _those_
concepts, and so on.

The 1lab is a community project: we use [GitHub] for source control and
talk on [Discord]. Our purpose is to make cubical methods in homotopy
type theory accessible to, and inclusive of, everyone who is interested,
regardless of cultural background, age, ability, ethnicity, gender
identity, or expression. Correspondingly, interactions in those forums
are governed by the [Contributor Covenant Code of Conduct][cccc]. **We
believe HoTT is for everyone, and are committed to fostering a kind,
inclusive environment.**

[GitHub]: https://github.com/plt-amy/1lab
[Discord]: https://discord.gg/NvXkUVYcxV
[cccc]: https://github.com/plt-amy/1lab/blob/main/CODE_OF_CONDUCT.md

Mathematics is, fundamentally, a social activity. Correspondingly, we
have a page dedicated to letting authors introduce and talk a bit
themselves and their other work:

```agda
open import Authors
```

Similarly, we maintain this list of related resources which serve as an
introduction to HoTT in general:

* The “canonical” reference is [the HoTT Book], written by a
variety of mathematicians at the IAS Special Year for Univalent
Mathematics, held between 2012-2013 and organised by Steve Awodey,
Thierry Coquand, and the late Vladimir Voevodsky.

  The Book is often referred to on this site - with those words - so if
  you don't know which book "The Book" is, it's the HoTT book! It's
  split into two parts: Type Theory, which introduces the concepts of
  Homotopy Type Theory with no previous knowledge of type theory
  assumed; and Mathematics, which develops some mathematics (homotopy
  theory, category theory, set theory, and real analysis) in this theory.

[the HoTT Book]: https://homotopytypetheory.org/book

* Prof. Martín Escardó, at Birmingham, has done a great service to the
community by _also_ formalising a great deal of univalent mathematics in
Literate Agda, in his [Introduction to Univalent Foundations of
Mathematics with Agda].

  Prof. Escardó's notes, unlike the 1lab, are done in base Agda, with
  univalence assumed explicitly in the theorems that need it. This is a
  principled decision when the goal is introducing univalent
  mathematics, but it is not practical when the goal is to _practice_
  univalent mathematics in Agda.

  Even still, that document is _much better_ than this site will _ever_
  be as an introduction to the subject! While many of the pages of the
  1lab have introductory _flavour_, it is not meant as an introduction
  to the subject of univalent mathematics.

[Introduction to Univalent Foundations of Mathematics with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html

* Prof. Favonia has kindly uploaded the outline, videos and lecture
notes for their 2020 course on higher-dimensional type theory, which
also serves as an introduction to cubical methods in homotopy type
theory, aimed at graduate students. You can find the course page
[here](https://favonia.org/courses/hdtt2020/), the videos [here on their
YouTube](https://www.youtube.com/playlist?list=PL0OBHndHAAZrGQEkOZGyJu7S7KudAJ8M9),
and the notes [here](https://github.com/favonia/hdtt2020-notes/) (though
heed the warning in the README).

* Another comprehensive, formalised Agda resource is the [agda-unimath]
project, though unlike us (and like prof. Escardó's lecture notes) they
make use of _axiomatic_ HoTT: Univalence is a postulate, and thus does
not have computational content.

  Regardless, they have formalised a great deal of "ordinary"
  mathematics in the univalent context: elementary number theory, group
  theory and combinatorics being the most prominent projects.

[agda-unimath]: https://unimath.github.io/agda-unimath/

## Technology

The 1Lab uses [Iosevka](https://typeof.net/Iosevka/) as its monospace
typeface. Iosevka is licensed under the SIL Open Font License, v1.1, a
copy of which can be found [here](/static/licenses/LICENSE.Iosevka). As
the sans-serif typeface, we use the [Inria Sans] webfont, and as a serif
typeface, [EB Garamond]. These fonts are both open-source, though rather
than rehosting them, we use them from Google Fonts.

[Inria Sans]: https://fonts.google.com/specimen/Inria+Sans
[EB Garamond]: https://fonts.google.com/specimen/EB+Garamond

Mathematics is rendered using [KaTeX](https://katex.org), and as so, the
1Lab redistributes KaTeX's fonts and stylesheets, even though the
rendering is done entirely at build-time. KaTeX is licensed under the
MIT License, a copy of which can be found
[here](/static/licenses/LICENSE.KaTeX).

Our favicon is Noto Emoji's ice cube (cubical type theory - get it?),
codepoint U+1F9CA. This is the only image from Noto we redistribute.
Noto fonts are licensed under the Apache 2.0 License, a copy of which
can be found [here](/static/licenses/LICENSE.Noto).

Commutative diagrams appearing in body text are created using
[quiver](https://q.uiver.app), and rendered to SVG using a combination of
[LaTeX](https://tug.org/texlive/) and
[pdftocairo](https://poppler.freedesktop.org/), part of the Poppler
project. No part of these projects is redistributed.

And, of course, the formalisation would not be possible without
[Agda](https://github.com/agda/agda).

# Type Theory

<div class=warning>
Most of the modules in the 1Lab assume a baseline knowledge of type
theory. For this, [**read the introduction here**](1Lab.intro.html).
</div>

The first things to be explained are the foundational constructions in
(cubical) type theory - things like types themselves, [universes],
[paths], [equivalences], [glueing] and the [univalence] "axiom". These
are developed under the `1Lab` namespace. Start here:

[universes]: agda://1Lab.Type
[paths]: agda://1Lab.Path
[equivalences]: agda://1Lab.Equiv
[glueing]: agda://1Lab.Univalence#Glue
[univalence]: agda://1Lab.Univalence#univalence

```agda
-- All of these module names are links you can click!

open import 1Lab.Type -- Universes

open import 1Lab.Path          -- Path types
open import 1Lab.Path.Groupoid -- Groupoid structure of types

open import 1Lab.Equiv             -- “Contractible fibres” equivalences
open import 1Lab.Equiv.Biinv       -- Biinvertible maps
open import 1Lab.Equiv.FromPath    -- Transport is an equivalence, cubically
open import 1Lab.Equiv.Embedding   -- Embeddings
open import 1Lab.Equiv.Fibrewise   -- Fibrewise equivalences
open import 1Lab.Equiv.HalfAdjoint -- Half-adjoint equivalences

open import 1Lab.HLevel          -- h-levels
open import 1Lab.HLevel.Sets     -- K, Rijke's theorem, Hedberg's theorem
open import 1Lab.HLevel.Retracts -- Closure of h-levels under retractions/isos
open import 1Lab.HLevel.Universe -- The type of n-types is a (n+1)-type

open import 1Lab.Univalence            -- Equivalence is equivalent to identification
open import 1Lab.Univalence.SIP        -- Univalence + preservation of structure
open import 1Lab.Univalence.SIP.Auto   -- Derive is-univalent for families of types
open import 1Lab.Univalence.SIP.Record -- Derive is-univalent for record types

open import 1Lab.Type.Dec   -- Decidable types, discrete types
open import 1Lab.Type.Pi    -- Properties of dependent products
open import 1Lab.Type.Sigma -- Properties of dependent coproducts

open import 1Lab.HIT.S1         -- The circle as a cell complex
open import 1Lab.HIT.Sphere     -- Spheres of arbitrary dimension
open import 1Lab.HIT.Torus      -- Torus as a cell complex and as a product space
open import 1Lab.HIT.Sinfty     -- The infinity-dimensional sphere
open import 1Lab.HIT.Suspension -- The suspension operation
open import 1Lab.HIT.Truncation -- Propositional truncation

open import 1Lab.Counterexamples.IsIso   -- Counterexample: is-iso is not a prop
open import 1Lab.Counterexamples.Russell -- Counterexample: Russell's paradox
open import 1Lab.Counterexamples.Sigma   -- Counterexample: Sigma is not prop
```

## Data types

The `Data` namespace contains definitions of oft-used data types, which
are fundamental to the rest of the development but not “basic type
theory”. These modules contain (or re-export) the types themselves,
useful operations on them, characterisation of their path spaces, etc.

```agda
open import Data.Nat  -- The natural numbers
open import Data.Int  -- The integers
open import Data.Sum  -- Coproduct types
open import Data.Bool -- The booleans
open import Data.List -- Finite lists
open import Data.Power           -- Power sets
open import Data.Power.Lattice   -- Power sets form a lattice
open import Data.Set.Coequaliser -- Set coequalisers
```

# Category Theory

In addition to providing a framework for the synthetic study of higher
groupoids, HoTT also provides a natural place to develop constructive,
predicative category theory, while still being compatible with
classicality principles like the axiom of choice and/or the law of
excluded middle. Here, we do not assume any classicality principles.

## Basics

The main modules in the `Cat` namespace provide the foundation for the
rest of the development, defining basic constructions like precategories
themselves, functors, natural transformations, etc.

```agda
open import Cat.Base      -- Precategories, functors, natural transformations
open import Cat.Solver    -- Automatic solver for associativity problems
open import Cat.Morphism  -- Important classes of morphisms
open import Cat.Reasoning -- Categorical reasoning combinators
```

### Diagrams

For convenience, we define a plethora of "concrete" universal diagrams,
unpacking their definitions as limits or colimits. These are simpler to
work with since they provide the relevant data with fewer layers of
indirection.

```agda
open import Cat.Diagram.Congruence -- Internal equivalence relations

-- Colimits:
open import Cat.Diagram.Initial                -- Initial objects
open import Cat.Diagram.Pushout                -- Pushouts
open import Cat.Diagram.Coproduct              -- Binary coproducts
open import Cat.Diagram.Coequaliser            -- Coequalisers
open import Cat.Diagram.Colimit.Base           -- Conical colimits
open import Cat.Diagram.Coproduct.Indexed      -- Indexed coproducts
open import Cat.Diagram.Coequaliser.RegularEpi -- Regular epimorphisms

open import Cat.Diagram.Duals -- Dualisation of co/limits
open import Cat.Diagram.Image -- Image factorisations
open import Cat.Diagram.Idempotent -- Idempotent morphisms

-- Limits
open import Cat.Diagram.Product                -- Binary products
open import Cat.Diagram.Pullback               -- Fibred products
open import Cat.Diagram.Terminal               -- Terminal objects
open import Cat.Diagram.Equaliser              -- Equalisers
open import Cat.Diagram.Limit.Base             -- Conical limits
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Limit.Product
open import Cat.Diagram.Limit.Pullback
open import Cat.Diagram.Limit.Equaliser
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Equaliser.Kernel       -- Kernels
open import Cat.Diagram.Pullback.Properties    -- Properties of fibred products
open import Cat.Diagram.Equaliser.RegularMono  -- Regular monomorphisms

open import Cat.Diagram.Monad        -- Monads
open import Cat.Diagram.Monad.Limits -- Limits in Eilenberg-Moore categories

open import Cat.Diagram.Zero -- Zero objects
```

## Functors

This namespace has definitions of properties functors can have, utility
modules for working with functors, the definition of full subcategories,
and adjoint functors.

```agda
open import Cat.Functor.Hom -- Hom functor, Yoneda embedding, Coyoneda lemma
open import Cat.Functor.Base -- Compendium of functor properties
open import Cat.Functor.Pullback -- Base change, dependent sum, Σf ⊣ f*
open import Cat.Functor.Bifunctor -- Functors out of product categories
open import Cat.Functor.Equivalence -- Equivalences of (pre)categories
open import Cat.Functor.Conservative -- Functors which reflect isomorphisms
open import Cat.Functor.FullSubcategory -- Full subcategories
open import Cat.Functor.Equivalence.Complete -- Completeness respects equivalence
```

About adjoint functors, and their associated monads:

```agda
open import Cat.Diagram.Monad   -- Definition of monads
open import Cat.Functor.Adjoint -- Unit-counit adjunctions and universal arrows
open import Cat.Functor.Adjoint.Monad -- Monad from an adjunction
open import Cat.Functor.Adjoint.Monadic -- Monadic adjunctions
open import Cat.Functor.Adjoint.Compose -- Adjunctions compose
open import Cat.Functor.Adjoint.Continuous -- Right adjoints preserve limits
open import Cat.Functor.Adjoint.Reflective -- Reflective subcategories
```

About Kan extensions:

```agda
open import Cat.Functor.Kan -- Kan extensions
open import Cat.Functor.Kan.Nerve -- The nerve/realisation adjunction (Lan along よ)
```

## Univalent categories

In HoTT/UF, the word "category" is reserved for the precategories (what
the rest of the world refers to as just "category") in which isomorphic
objects are indistinguishable, i.e. the categories which satisfy a
version of the univalence axiom. Sometimes we also refer to these as
"univalent categories" to make the distinction clear.

```agda
open import Cat.Univalent      -- Basic properties of categories
open import Cat.Univalent.Rezk -- Free category on a precategory
open import Cat.Univalent.Instances.Algebra
  -- Eilenberg-Moore categories preserve univalence
```

## Category instances

Here's where we actually build some categories and prove that they have
desirable properties.

```agda
-- Comma categories:
open import Cat.Instances.Comma
open import Cat.Instances.Comma.Univalent

open import Cat.Instances.Delooping -- Delooping a monoid to give a category
open import Cat.Instances.Discrete -- Discrete categories
open import Cat.Instances.Elements -- Category of elements of a presheaf

-- Functor categories:
open import Cat.Instances.Functor
open import Cat.Instances.Functor.Limits -- Co/limits in functor categories
open import Cat.Instances.Functor.Duality -- 2-cell duality in Cat

-- Completion of a category under splitting idempotents
open import Cat.Instances.Karoubi

open import Cat.Instances.Lift -- Lifting a category to higher universes
open import Cat.Instances.Product -- Product categories

-- The category of sets
open import Cat.Instances.Sets -- is univalent
open import Cat.Instances.Sets.Complete -- is complete
open import Cat.Instances.Sets.Cocomplete -- is cocomplete, with disjoint coproducts
open import Cat.Instances.Sets.Congruences -- has effective congruences
open import Cat.Instances.Sets.CartesianClosed -- and is locally cartesian closed

-- Diagram shapes:
open import Cat.Instances.Shape.Join
open import Cat.Instances.Shape.Cospan
open import Cat.Instances.Shape.Interval
open import Cat.Instances.Shape.Parallel
open import Cat.Instances.Shape.Terminal

-- Slice categories:
open import Cat.Instances.Slice
open import Cat.Instances.Slice.Presheaf -- PSh(C)/X ≅ PSh(∫ X)

-- Strict categories
open import Cat.Instances.StrictCat
open import Cat.Instances.StrictCat.Cohesive
  -- ^ Strict category structure is a sort of "spatial" structure on a category
```

## Thin categories

Strict thin categories are a presentation of pre-ordered sets, i.e. sets
equipped with a transitive and reflexive relation --- so we call them
"prosets". When this relation is antisymmetric, we additionally have a
_univalent_ thin strict category --- so we call these "posets".

```agda
open import Cat.Thin            -- Basics of thin categories
open import Cat.Thin.Limits     -- Limits in thin categories
open import Cat.Thin.Completion -- Free poset on a proset
```

## Displayed categories

We also have a work-in-progress formalisation of [Foundations of
Relative Category Theory][frct], in which the core idea is thinking of
"categories over categories".

[frct]: https://www.jonmsterling.com/math/lectures/categorical-foundations.html

```agda
open import Cat.Displayed.Base             -- Displayed categories
open import Cat.Displayed.Total            -- Total category of a displayed category
open import Cat.Displayed.Cartesian        -- Cartesian lifts, cartesian fibrations
open import Cat.Displayed.Instances.Family -- Family fibration
open import Cat.Displayed.Instances.Slice  -- Canonical self-indexing
```

# Topos theory

Grothendieck topos theory developed constructively and predicatively.

```agda
open import Topoi.Base       -- Topoi, properties of topoi, geometric morphisms
open import Topoi.Reasoning  -- Exactness properties of topoi (cont'd), reasoning
open import Topoi.Classifying.Diaconescu
-- ^ Presheaf topoi classify flat functors on their site
```

# Algebra

In the `Algebra` namespace, the theory of universal algebra is developed
from a univalent perspective. Specifically, every definition of an
algebraic structure comes with an associated proof that it is univalent
--- concretely, identification of groups is group isomorphism (for
instance).

```agda
open import Algebra.Magma                      -- Binary operations
open import Algebra.Magma.Unital               -- Operations with two-sided units
open import Algebra.Magma.Unital.EckmannHilton -- The Eckmann-Hilton argument

open import Algebra.Semigroup   -- Semigroups (associative magmas)
open import Algebra.Monoid      -- Monoids as unital semigroups

open import Algebra.Group                      -- Groups as monoids with inverses
open import Algebra.Group.Free                 -- Free groups
open import Algebra.Group.Cayley               -- Cayley's theorem
open import Algebra.Group.Cat.Base             -- Category of groups
open import Algebra.Group.Cat.FinitelyComplete -- Finite limits in Groups
open import Algebra.Group.Homotopy             -- Homotopy groups
open import Algebra.Group.Subgroup             -- Subgroups, images and kernels

open import Algebra.Group.Ab -- Abelian groups, and the category Ab
open import Algebra.Group.Ab.Free -- The free abelian group on a group
```
