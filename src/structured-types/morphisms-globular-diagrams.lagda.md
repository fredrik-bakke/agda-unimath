# Morphisms of globular diagrams of types

```agda
module structured-types.morphisms-globular-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-inverse-sequential-diagrams
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families

open import structured-types.dependent-globular-diagrams
open import structured-types.globular-diagrams
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of globular diagrams of types" Agda=hom-globular-diagram}}
of [globular diagrams](structured-types.globular-diagrams.md) `A → B` is a
family of maps `f : (n : ℕ) → A n → B n` such that `f` restricted to both the
source [inverse sequential diagram](foundation.inverse-sequential-diagram.md)
and target inverse sequential diagram is a
[morphism of inverse sequential diagrams](foundation.morphisms-inverse-sequential-diagram.md).

## Definitions

### Morphisms of globular diagrams of types

```agda
module _
  {l1 l2 : Level} (A : globular-diagram l1) (B : globular-diagram l2)
  (h : (n : ℕ) → family-globular-diagram A n → family-globular-diagram B n)
  where

  naturality-source-hom-globular-diagram : UU (l1 ⊔ l2)
  naturality-source-hom-globular-diagram =
    naturality-source-section-dependent-globular-diagram A
      ( const-dependent-globular-diagram A B)
      h

  naturality-target-hom-globular-diagram : UU (l1 ⊔ l2)
  naturality-target-hom-globular-diagram =
    naturality-target-section-dependent-globular-diagram A
      ( const-dependent-globular-diagram A B)
      h

  naturality-hom-globular-diagram : UU (l1 ⊔ l2)
  naturality-hom-globular-diagram =
    naturality-section-dependent-globular-diagram A
      ( const-dependent-globular-diagram A B)
      h

hom-globular-diagram :
  {l1 l2 : Level}
  (A : globular-diagram l1)
  (B : globular-diagram l2) →
  UU (l1 ⊔ l2)
hom-globular-diagram A B =
  section-dependent-globular-diagram A
    ( const-dependent-globular-diagram A B)

module _
  {l1 l2 : Level}
  (A : globular-diagram l1)
  (B : globular-diagram l2)
  (f : hom-globular-diagram A B)
  where

  map-hom-globular-diagram :
    (n : ℕ) →
    family-globular-diagram A n →
    family-globular-diagram B n
  map-hom-globular-diagram =
    map-section-dependent-globular-diagram A
      ( const-dependent-globular-diagram A B)
      ( f)

  naturality-map-hom-globular-diagram :
    naturality-hom-globular-diagram A B map-hom-globular-diagram
  naturality-map-hom-globular-diagram =
    naturality-map-section-dependent-globular-diagram A
      ( const-dependent-globular-diagram A B)
      ( f)

  naturality-source-map-hom-globular-diagram :
    naturality-source-hom-globular-diagram A B map-hom-globular-diagram
  naturality-source-map-hom-globular-diagram =
    pr1 naturality-map-hom-globular-diagram

  naturality-target-map-hom-globular-diagram :
    naturality-target-hom-globular-diagram A B map-hom-globular-diagram
  naturality-target-map-hom-globular-diagram =
    pr2 naturality-map-hom-globular-diagram

  hom-source-diagram-globular-diagram :
    hom-inverse-sequential-diagram
      ( source-diagram-globular-diagram A)
      ( source-diagram-globular-diagram B)
  hom-source-diagram-globular-diagram =
    map-hom-globular-diagram , naturality-source-map-hom-globular-diagram

  hom-target-diagram-globular-diagram :
    hom-inverse-sequential-diagram
      ( target-diagram-globular-diagram A)
      ( target-diagram-globular-diagram B)
  hom-target-diagram-globular-diagram =
    map-hom-globular-diagram , naturality-target-map-hom-globular-diagram
```

### Identity morphism on globular diagrams of types

```agda
id-hom-globular-diagram :
  {l : Level} (A : globular-diagram l) →
  hom-globular-diagram A A
pr1 (id-hom-globular-diagram A) n = id
pr1 (pr2 (id-hom-globular-diagram A)) n = refl-htpy
pr2 (pr2 (id-hom-globular-diagram A)) n = refl-htpy
```

### Composition of morphisms of globular diagrams of types

```agda
module _
  {l1 l2 l3 : Level}
  (A : globular-diagram l1) (B : globular-diagram l2) (C : globular-diagram l3)
  (g : hom-globular-diagram B C) (f : hom-globular-diagram A B)
  where

  map-comp-hom-globular-diagram :
    (n : ℕ) → family-globular-diagram A n → family-globular-diagram C n
  map-comp-hom-globular-diagram n =
    map-hom-globular-diagram B C g n ∘ map-hom-globular-diagram A B f n

  naturality-source-comp-hom-globular-diagram :
    naturality-source-hom-globular-diagram A C map-comp-hom-globular-diagram
  naturality-source-comp-hom-globular-diagram =
    naturality-comp-hom-inverse-sequential-diagram
      ( source-diagram-globular-diagram A)
      ( source-diagram-globular-diagram B)
      ( source-diagram-globular-diagram C)
      ( hom-source-diagram-globular-diagram B C g)
      ( hom-source-diagram-globular-diagram A B f)

  naturality-target-comp-hom-globular-diagram :
    naturality-target-hom-globular-diagram A C map-comp-hom-globular-diagram
  naturality-target-comp-hom-globular-diagram =
    naturality-comp-hom-inverse-sequential-diagram
      ( target-diagram-globular-diagram A)
      ( target-diagram-globular-diagram B)
      ( target-diagram-globular-diagram C)
      ( hom-target-diagram-globular-diagram B C g)
      ( hom-target-diagram-globular-diagram A B f)

  naturality-comp-hom-globular-diagram :
    naturality-hom-globular-diagram A C map-comp-hom-globular-diagram
  naturality-comp-hom-globular-diagram =
    naturality-source-comp-hom-globular-diagram ,
    naturality-target-comp-hom-globular-diagram

  comp-hom-globular-diagram : hom-globular-diagram A C
  comp-hom-globular-diagram =
    ( map-comp-hom-globular-diagram , naturality-comp-hom-globular-diagram)
```

## Properties

### Characterization of equality of morphisms of globular diagrams of types

```agda
module _
  {l1 l2 : Level}
  (A : globular-diagram l1)
  (B : globular-diagram l2)
  where

  coherence-htpy-hom-globular-diagram :
    (f g : hom-globular-diagram A B) →
    ((n : ℕ) →
      map-hom-globular-diagram A B f n ~
      map-hom-globular-diagram A B g n) →
    UU (l1 ⊔ l2)
  coherence-htpy-hom-globular-diagram f g H =
    ( coherence-htpy-hom-inverse-sequential-diagram
      ( source-diagram-globular-diagram A)
      ( source-diagram-globular-diagram B)
      ( hom-source-diagram-globular-diagram A B f)
      ( hom-source-diagram-globular-diagram A B g)
      ( H)) ×
    ( coherence-htpy-hom-inverse-sequential-diagram
      ( target-diagram-globular-diagram A)
      ( target-diagram-globular-diagram B)
      ( hom-target-diagram-globular-diagram A B f)
      ( hom-target-diagram-globular-diagram A B g)
      ( H))

  htpy-hom-globular-diagram :
    (f g : hom-globular-diagram A B) → UU (l1 ⊔ l2)
  htpy-hom-globular-diagram f g =
    Σ ( (n : ℕ) →
        map-hom-globular-diagram A B f n ~
        map-hom-globular-diagram A B g n)
      ( coherence-htpy-hom-globular-diagram f g)

  refl-htpy-hom-globular-diagram :
    (f : hom-globular-diagram A B) → htpy-hom-globular-diagram f f
  pr1 (refl-htpy-hom-globular-diagram f) n = refl-htpy
  pr1 (pr2 (refl-htpy-hom-globular-diagram f)) n = right-unit-htpy
  pr2 (pr2 (refl-htpy-hom-globular-diagram f)) n = right-unit-htpy

  htpy-eq-hom-globular-diagram :
    (f g : hom-globular-diagram A B) →
    f ＝ g →
    htpy-hom-globular-diagram f g
  htpy-eq-hom-globular-diagram f .f refl =
    refl-htpy-hom-globular-diagram f

  is-torsorial-htpy-hom-globular-diagram :
    (f : hom-globular-diagram A B) →
    is-torsorial (htpy-hom-globular-diagram f)
  is-torsorial-htpy-hom-globular-diagram f =
    is-torsorial-Eq-structure
      ( is-torsorial-binary-htpy (map-hom-globular-diagram A B f))
      ( map-hom-globular-diagram A B f ,
        refl-binary-htpy (map-hom-globular-diagram A B f))
      ( is-torsorial-Eq-structure
        ( is-torsorial-binary-htpy
          ( λ n →
            naturality-source-map-hom-globular-diagram A B f n ∙h refl-htpy))
        ( ( naturality-source-map-hom-globular-diagram A B f) ,
          ( λ _ → right-unit-htpy))
        ( is-torsorial-binary-htpy
          ( λ n →
            naturality-target-map-hom-globular-diagram A B f n ∙h refl-htpy)))

  is-equiv-htpy-eq-hom-globular-diagram :
    (f g : hom-globular-diagram A B) →
    is-equiv (htpy-eq-hom-globular-diagram f g)
  is-equiv-htpy-eq-hom-globular-diagram f =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-globular-diagram f)
      ( htpy-eq-hom-globular-diagram f)

  extensionality-hom-globular-diagram :
    (f g : hom-globular-diagram A B) →
    (f ＝ g) ≃ htpy-hom-globular-diagram f g
  pr1 (extensionality-hom-globular-diagram f g) =
    htpy-eq-hom-globular-diagram f g
  pr2 (extensionality-hom-globular-diagram f g) =
    is-equiv-htpy-eq-hom-globular-diagram f g

  eq-htpy-hom-globular-diagram :
    (f g : hom-globular-diagram A B) →
    htpy-hom-globular-diagram f g → f ＝ g
  eq-htpy-hom-globular-diagram f g =
    map-inv-equiv (extensionality-hom-globular-diagram f g)
```
