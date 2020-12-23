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
    { lᵢ=tᵢ (i∈1..n) }          record
    t.l                         projection
    let p = t in t              pattern binding
    <l=t> as T                  tagging
    case t of
      <lᵢ=xᵢ>=>tᵢ (i∈1..n)      case
    fix t                       fixed point of t
    nil[T]                      empty list
    cons[T] t t                 list constructor
    isnil[T] t                  test for empty list
    head[T] t                   head of a list
    tail[T] t                   tail of a list

v ::=                   values:
    λx:T.t                      abstraction value
    true                        true value
    false                       false value
    nv                          numeric value
    unit                        constant unit
    { lᵢ=vᵢ (i∈1..n) }          record value
    nil[T]                      empty list
    cons[T] v v                 list constructor

nv ::=                  numeric values:
    0                           zero value
    succ nv                     successor value

p ::=                   patterns:
    x                           variable pattern
    { lᵢ=pᵢ (i∈1..n) }          record pattern

T ::=                   types:
    T → T                       type of functions
    Bool                        type of booleans
    Nat                         type of natural numbers
    A                           base type
    Unit                        unit type
    { lᵢ:Tᵢ (i∈1..n) }          type of records
    <lᵢ:Tᵢ (i∈1..n)>            type of variants
    List T                      type of lists

Γ ::=                   contexts:
    ∅                           empty context
    Γ,x:T                       term variable binding
```

## Matching rules

```
match(x, v) = [x ↦ v]                   M-Var

for each i      match(pᵢ, vᵢ) = σᵢ
----------------------------------      M-Rcd
match({ lᵢ=pᵢ (i∈1..n) }, { lᵢ=vᵢ (i∈1..n) }
        =σ₁ ∘ ··· ∘ σₙ
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

let p = v₁ in t₂ → match(p, v₁)t₂       E-LetV

              t1 → t′₁
------------------------------------    E-Let
let p = t₁ in t₂ → let p = t′₁ in t₂

{ lᵢ=vᵢ (i∈1..n) }.lⱼ → vⱼ              E-ProjRcd

  t₁ → t′₁
------------                            E-Proj
t₁.i → t′₁.i

                tⱼ → t′ⱼ
--------------------------------------  E-Rcd
{ lᵢ=vᵢ (i∈1..j-1) ,lⱼ=tⱼ  ,lₖ=tₖ (k∈j+1..n) } →
{ lᵢ=vᵢ (i∈1..j-1), lⱼ=t′ⱼ ,lₖ=tₖ (k∈j+1..n) }

case (<lj=vj> as T) of
  <lᵢ=xᵢ> ⇒ tᵢ (i∈1..n) → [xj ↦ vj] tj  E-CaseVariant

            t₀ → t′₀
-----------------------------------     E-Case
case t₀ of <lᵢ=xᵢ> ⇒ tᵢ (i∈1..n)
→ case t′₀ of <lᵢ=xᵢ> ⇒ tᵢ (i∈1..n)

          tᵢ → t′ᵢ
----------------------------            E-Variant
<lᵢ=tᵢ> as T → <lᵢ=t′ᵢ> as T

fix (λx:T₁.t₂) →
[x ↦ (fix (λx:T₁.t₂))]t₂                E-FixBeta

    t₁ → t′₁
----------------                        E-Fix
fix t₁ → fix t′₁

           t₁ → t′₁
------------------------------          E-Cons1
cons[T] t₁ t₂ → cons[T] t′₁ t₂

           t₂ → t′₂
------------------------------          E-Cons2
cons[T] t₁ t₂ → cons[T] t₁ t′₂

isnil[S] (nil[T]) → true                E-IsnilNil

isnil[S] (cons[T] v₁ v₂) → false        E-IsnilCons

         t₁ → t′₁
--------------------------              E-Isnil
isnil[T] t₁ → isnil[T] t′₁

head[S] (cons[T] v₁ v₂) → v₁            E-HeadCons

        t₁ → t′₁
------------------------                E-Head
head[T] t₁ → head[T] t′₁

tail[S] (cons[T] v₁ v₂) → v₂            E-TailCons

        t₁ → t′₁
------------------------                E-Tail
tail[T] t₁ → tail[T] t′₁
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
--------------------------------------- T-Rcd
Γ ⊢ {lᵢ=tᵢ (i∈1..n)} : {lᵢ:Tᵢ (i∈1..n)}

Γ ⊢ t₁ : {lᵢ:Tᵢ (i∈1..n)}
-------------------------               T-Proj
    Γ ⊢ t₁.lⱼ : Tⱼ

          Γ ⊢ tj : Tj
-------------------------------         T-Variant
Γ ⊢ <lj=tj> as <lᵢ:Tᵢ (i∈1..n)>
  :<lᵢ:Tᵢ(i∈1..n)>

    Γ ⊢ t₀ : <lᵢ:Tᵢ (i∈1..n)>
   for each i Γ,xᵢ:Tᵢ ⊢ tᵢ : T
--------------------------------------  T-Variant
Γ⊢case t₀ of <lᵢ=tᵢ> ⇒ tᵢ (i∈1..n) : T

Γ ⊢ t₁ : T₁ → T₁
----------------                        T-Fix
 Γ ⊢ fix t₁ : T₁

Γ ⊢ nil [T₁] : List T₁                  T-Nil

Γ ⊢ t₁ : T₁     Γ ⊢ t₂ : List T₁
--------------------------------        T-Cons
  Γ ⊢ cons[T₁] t₁ t₂ : List T₁

    Γ ⊢ t₁ : List T₁₁
------------------------                T-Isnil
Γ ⊢ isnil[T₁₁] t₁ : Bool

   Γ ⊢ t₂ : List T₁₁
----------------------                  T-Head
Γ ⊢ head[T₁₁] t₁ : T₁₁

   Γ ⊢ t₂ : List T₁₁
----------------------                  T-Tail
Γ ⊢ tail[T₁₁] t₁ : T₁₁
```

## Derived forms

```
       def
t₁;t₂   =       (λx:Unit.t₂)t₁
                where x ∉ FV(t₂)


                        def
letrec x : T₁ = t₂ in t₂ = 
  let x = fix (λx:T₁.t₁) in t₂
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

```
U+22A2 = ⊢
U+2209 = ∉

U+21A6 = ↦
U+2218 = ∘
U+00B7 = ·

U+1D62 = ᵢ
U+2C7C = ⱼ
U+2096 = ₖ
U+2099 = ₙ

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
<C-k>s* = σ
<C-k>1s = ₁
<C-k>1S = ¹
<C-k>=> = ⇒
```
