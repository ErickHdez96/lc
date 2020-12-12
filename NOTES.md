```
U+22A2 = ⊢
U+2209 = ∉

U+21A6 = ↦

U+1D62 = ᵢ
U+2C7C = ⱼ
U+2096 = ₖ

U+2081 = ₁
U+2082 = ₂

U+00B9 = ¹
U+00B2 = ²
U+00B3 = ³

U+2070 = ⁰
U+2071 = ⁱ (superscript i)

<C-k>1' = ′ (prime)
<C-k>l* = λ
<C-k>(- = ∈
<C-k>G* = Γ
<C-k>/0 = ∅
<C-k>1s = ₁
<C-k>1S = ¹
```

```
   Γ,x:T₁ ⊢ t₂ : T₂
----------------------          T-Abs
Γ ⊢ λx:T₁.t₂ : T₁ → T₂

(∅) ⊢ t : T

The closed term t has type T under the empty set of assumptions

x : T ∈ Γ
---------                       T-Var
Γ ⊢ x : T

The type assumed for x in Γ is T.

Γ ⊢ t₁ : T₁₁ → T₁₂      Γ ⊢ t₂ : T₁₁
------------------------------------    T-App
          Γ ⊢ t₁ t₂ : T₁₂
```

## Syntactic forms

```
t ::=                   terms:
    x                           variable
    λx:T.t                      abstraction
    t t                         application
    true                        constant true
    false                       constant false
    if t then t else t          conditional
    0                           constant 0
    succ t                      successor
    pred t                      predecessor
    iszero t                    zero test
    unit                        constant unit
    t as T                      ascription
    let x = t in t              let binding
    { tᵢ (i∈1..n) }             tuple
    t.i                         projection

v ::=                   values:
    λx:T.t                      abstraction value
    true                        true value
    false                       false value
    nv                          numeric value
    unit                        constant unit
    { vᵢ (i∈1..n) }             tuple value

nv ::=                  numeric values:
    0                           zero value
    succ nv                     successor value


T ::=                   types:
    T → T                       type of functions
    Bool                        type of booleans
    Nat                         type of natural numbers
    A                           base type
    Unit                        unit type
    { Tᵢ (i∈1..n) }             tuple type

Γ ::=                   contexts:
    ∅                           empty context
    Γ,x:T                       term variable binding
```

## Evaluation

`t → t′`

```
    t₁ → t′₁
--------------                          E-App1
t₁ t₂ → t′₁ t₂

    t₂ → t′₂
--------------                          E-App2
v₁ t₂ → v₁ t′₂

(λx:T₁₁.t₁₂)v₂ → [x ↦ v₂]t₁₂            E-AppAbs

     t₁ → t′₁
------------------                      E-Succ
succ t₁ → succ t′₁

pred 0 → 0                              E-PredZero

pred (succ nv₁) → nv₁                   E-PredSucc

     t₁ → t′₁
------------------                      E-Pred
pred t₁ → pred t′₁

iszero 0 → true                         E-IsZeroZero

iszero (succ nv₁) → false               E-IsZeroSucc

       t₁ → t′₁
----------------------                  E-IsZero
iszero t₁ → iszero t′₁

v₁ as T → v₁                            E-Ascribe

     t₁ → t′₁
------------------                      E-Ascribe₁
t₁ as T → t′₁ as T

let x = v₁ in t₂ → [x ↦ v₁]t₂           E-LetV

              t1 → t′₁
------------------------------------    E-Let
let x = t₁ in t₂ → let x = t′₁ in t₂

{ vᵢ (i∈1..n) }.j → vⱼ                  E-ProjTuple

  t₁ → t′₁
------------                            E-Proj
t₁.i → t′₁.i

                tⱼ → t′ⱼ
--------------------------------------  E-Tuple (Tuples' elements are evaluated from left to right)
{ vᵢ (i∈1..j-1), tⱼ, tₖ (k∈j+1..n) } →
{ vᵢ (i∈1..j-1), t′ⱼ, tₖ (k∈j+1..n) }
```

## Typing

`Γ ⊢ t : T`

```
 x:T ∈ Γ
---------                               T-Var
Γ ⊢ x : T

   Γ,x:T₁ ⊢ t₂:T₂
--------------------                    T-Abs
Γ ⊢ λx:T₁.t₂ : T₁→T₂

Γ ⊢ t₁ : T₁₁ → T₁₂   Γ ⊢ t₂ : T₁₁
------------------------------------    T-App
         Γ ⊢ t₁ t₂ : T₁₂

true : Bool                             T-True

false : Bool                            T-False

t₁ : Bool    t₂ : T    t₃ : T
-----------------------------           T-If
  if t₁ then t₂ else t₃ : T

0 : Nat                                 T-Zero

   t₁ : Nat
-------------                           T-Succ
succ t₁ : Nat

  t₁ : Nat
-------------                           T-Pred
pred t₁ : Nat

    t₁ : Nat
----------------                        T-IsZero
iszero t₁ : Bool

Γ ⊢ unit: Unit                          T-Unit

  Γ ⊢ t₁ : T
---------------                         T-Ascribe
Γ ⊢ t₁ as T : T

Γ ⊢ t₁ : T₁     Γ,x:T₁ ⊢ t₂ : T₂
--------------------------------        T-Let
    Γ ⊢ let x = t₁ in t₂ : T₂

   for each i      Γ ⊢ tᵢ : Tᵢ
---------------------------------       T-Tuple
Γ ⊢ {tᵢ (i∈1..n)} : {Tᵢ (i∈1..n)}

Γ ⊢ t₁ : {Tᵢ (i∈1..n)}
----------------------                  T-Proj
     Γ ⊢ t₁.j : Tⱼ
```

## Derived forms

```
       def
t₁;t₂   =       (λx:Unit.t₂)t₁
                where x ∉ FV(t₂)
```

```
Logic                           Programming
------------------------------------------------------------------
propositions                    types
proposition P ⊃ Q               type P → Q
proposition P ∧ Q               type P x Q
proof of proposition P          term t of type P
proposition P is provable       type P is inhabited (by some term)
```
