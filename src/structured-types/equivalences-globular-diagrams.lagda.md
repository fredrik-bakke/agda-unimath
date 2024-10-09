# Equivalences of globular diagrams of types

```agda
module structured-types.equivalences-globular-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.binary-homotopies
open import structured-types.globular-diagrams
open import structured-types.morphisms-globular-diagrams
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguaiton="of globular diagrams of types" Agda=equiv-globular-diagram}}
`A ≃ B` is a
[morphism of globular diagrams](structured-types.morphisms-globular-diagrams.md)
`f`

```text
    ---->      ---->    ---->   ---->    ---->
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
           |         |               |        |
           |         |       ⋯       |        |
           ∨         ∨               ∨        ∨
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
    ---->      ---->    ---->   ---->    ---->
```

where every vertical map is an [equivalence](foundation-core.equivalences.md).

## Definitions

```agda
equiv-globular-diagram :
  {l1 l2 : Level}
  (A : globular-diagram l1)
  (B : globular-diagram l2) →
  UU (l1 ⊔ l2)
equiv-globular-diagram A B =
  Σ ( (n : ℕ) →
      family-globular-diagram A n ≃
      family-globular-diagram B n)
    ( λ e → naturality-hom-globular-diagram A B (map-equiv ∘ e))

hom-equiv-globular-diagram :
  {l1 l2 : Level}
  (A : globular-diagram l1)
  (B : globular-diagram l2) →
  equiv-globular-diagram A B →
  hom-globular-diagram A B
pr1 (hom-equiv-globular-diagram A B e) n = pr1 (pr1 e n)
pr2 (hom-equiv-globular-diagram A B e) = pr2 e
```

## Properties

### The identity equivalence of globular diagrams

```agda
id-equiv-globular-diagram :
  {l : Level} (A : globular-diagram l) →
  equiv-globular-diagram A A
pr1 (id-equiv-globular-diagram A) n = id-equiv
pr1 (pr2 (id-equiv-globular-diagram A)) n = refl-htpy
pr2 (pr2 (id-equiv-globular-diagram A)) n = refl-htpy
```

### Characterizing equality of globular diagrams

```agda
is-torsorial-naturality-id-hom-globular-diagram :
  {l : Level} (A : globular-diagram l) →
  is-torsorial (naturality-hom-globular-diagram A A ?)
is-torsorial-naturality-id-hom-globular-diagram = ?

equiv-eq-globular-diagram :
  {l : Level} (A B : globular-diagram l) →
  A ＝ B → equiv-globular-diagram A B
equiv-eq-globular-diagram A .A refl =
  id-equiv-globular-diagram A

is-torsorial-equiv-globular-diagram :
  {l : Level} (A : globular-diagram l) →
  is-torsorial (λ (B : globular-diagram l) → equiv-globular-diagram A B)
is-torsorial-equiv-globular-diagram A =
  is-torsorial-Eq-structure
    ( is-torsorial-Eq-Π
      ( λ n → is-torsorial-equiv (family-globular-diagram A n)))
    ( family-globular-diagram A , λ n → id-equiv)
    ( {!   !})


  -- is-torsorial-Eq-structure
  --   ( is-torsorial-Eq-Π
  --     ( λ n → is-torsorial-equiv (family-globular-diagram A n)))
  --   ( family-globular-diagram A , λ n → id-equiv)
  --   ( is-torsorial-Eq-structure
  --     ( is-torsorial-binary-htpy (source-map-globular-diagram A))
  --     ( source-map-globular-diagram A , λ _ → refl-htpy)
  --     ( {!  is-torsorial-Eq-Π ? !}))

-- is-equiv-equiv-eq-globular-diagram :
--   {l : Level} (A B : globular-diagram l) →
--   is-equiv (equiv-eq-globular-diagram A B)
-- is-equiv-equiv-eq-globular-diagram A =
--   fundamental-theorem-id
--     ( is-torsorial-equiv-globular-diagram A)
--     ( equiv-eq-globular-diagram A)

-- eq-equiv-globular-diagram :
--   {l : Level} {A B : globular-diagram l} →
--   equiv-globular-diagram A B → A ＝ B
-- eq-equiv-globular-diagram {A = A} {B} =
--   map-inv-is-equiv (is-equiv-equiv-eq-globular-diagram A B)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
