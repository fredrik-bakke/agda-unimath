# Strict discrete precategories

```agda
module category-theory.strict-discrete-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.fully-faithful-functors-precategories
open import category-theory.groupoids
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.pregroupoids
open import category-theory.preunivalent-categories
open import category-theory.strict-categories
open import category-theory.terminal-category

open import foundation.1-types
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

Given a [set](foundation-core.sets.md) `X`, we can define its **associated
strict discrete category**, as the category whose objects is `X` and morphisms
consists only of identities.

Observe that this is a special case of the construction of a
[groupoid](category-theory.groupoids.md) associated to a
[1-type](foundation.1-types.md), so a
[discrete category](category-theory.discrete-categories.md) more generally refer
to the underlying category of the groupoid associated to a 1-type.

## Definitions

### The discrete category associated to a set

```agda
module _
  {l : Level} (X : Set l)
  where

  obj-discrete-Category : UU l
  obj-discrete-Category = type-Set X

  hom-set-discrete-Category :
    obj-discrete-Category → obj-discrete-Category → Set l
  hom-set-discrete-Category x y = set-Prop (Id-Prop X x y)

  hom-discrete-Category :
    obj-discrete-Category → obj-discrete-Category → UU l
  hom-discrete-Category x y = type-Set (hom-set-discrete-Category x y)

module _
  {l : Level} (X : Set l)
  where

  groupoid-discrete-Category : Groupoid l l
  groupoid-discrete-Category = groupoid-1-Type (1-type-Set X)

  discrete-Category : Category l l
  discrete-Category = category-Groupoid groupoid-discrete-Category

  is-groupoid-discrete-Category : is-groupoid-Category discrete-Category
  is-groupoid-discrete-Category =
    is-groupoid-Groupoid groupoid-discrete-Category

  discrete-Precategory : Precategory l l
  discrete-Precategory = ?

  is-category-discrete-Category : is-category-Precategory (pre
```

## Properties

### The discrete category associated to a set is gaunt

###

## See also

- [Indiscrete precategories](category-theory.indiscrete-precategories.md)

## External links

- [discrete category](https://ncatlab.org/nlab/show/discrete+category) at nlab
- [Discrete category](https://en.wikipedia.org/wiki/Discrete_category) at
  Wikipedia

A wikidata identifier was not available for this concept.
