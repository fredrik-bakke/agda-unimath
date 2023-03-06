# 2-identifications

<details><summary>Imports</summary>
```agda
module foundation.2-identifications where
open import foundation.identity-types
open import foundation.universe-levels
```
</details>

## Idea

A **2-identification** is an identification of identifications. I.e.
Given a type `A` with terms `x y : A` and identifications `p q : x ＝ y`,
then a 2-identification is an identification `r : p ＝ q`.

```md
       p
    =======
  x    r    y
    =======
       q
```

## Operations

### Horizontal concatenation of 2-identifications

```md
       p         p'
    =======   =======
  x    r    y    r'   z
    =======   =======
       q         q'
```

```agda
2-identification-comp-horizontal :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {p' q' : y ＝ z} →
  p ＝ q → p' ＝ q' → (p ∙ p') ＝ (q ∙ q')
2-identification-comp-horizontal refl refl = refl
```

### Vertical concatenation of 2-identifications

```md
       p
    =======  
  //   s   \\
  x == q == y
  \\   t   //
    =======
       r
```

```agda
2-identification-comp-vertical :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} →
  p ＝ q → q ＝ r → p ＝ r
2-identification-comp-vertical = _∙_
```

### Left whiskering of 2-identifications

```md
                 p
       r      =======
  x ======= y    s    z
              =======
                 q
```

```agda
2-identification-left-whisk : 
  {l : Level} {A : UU l} {x y z : A} {p q : y ＝ z}
  (r : x ＝ y) → p ＝ q → (r ∙ p) ＝ (r ∙ q)
2-identification-left-whisk refl s = s
```

### Right whiskering of 2-identifications

```md
       p
    =======      r
  x    s    y ======= z
    =======
       q
```

```agda
2-identification-right-whisk : 
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} →
  p ＝ q → (r : y ＝ z) → (p ∙ r) ＝ (q ∙ r)
2-identification-right-whisk refl r = refl
```