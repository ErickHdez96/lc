```
U+22A2 = ⊢

U+21A6 = ↦

U+2081 = ₁
U+2082 = ₂

U+00B9 = ¹
U+00B2 = ²
U+00B3 = ³

U+2070 = ⁰
U+2071 = ⁱ

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


Syntax
t::=            terms:
    x           variable
    λx:T.t      abstraction
    t t         application

v ::=           values:
    λx:T.t      abstraction value


T ::=           types:
    T → T       type of functions


Γ ::=           contexts:
    ∅           empty context
    Γ,x:T       term variable binding


Evaluation

    t₁ → t′₁
--------------                  E-App1
t₁ t₂ → t′₁ t₂

    t₂ → t′₂
--------------                  E-App2
v₁ t₂ → v₁ t′₂

(λx:T₁₁.t₁₂)v₂ → [x ↦ v₂]t₁₂    E-AppAbs

Typing                          Γ ⊢ t : T

 x:T ∈ Γ
---------                       T-Var
Γ ⊢ x : T

   Γ,x:T₁ ⊢ t₂:T₂
--------------------            T-Abs
Γ ⊢ λx:T₁.t₂ : T₁→T₂

Γ ⊢ t₁ : T₁₁ → T₁₂   Γ ⊢ t₂ : T₁₁
------------------------------------    T-App
         Γ ⊢ t₁ t₂ : T₁₂

Logic                           Programming
------------------------------------------------------------------
propositions                    types
proposition P ⊃ Q               type P → Q
proposition P ∧ Q               type P x Q
proof of proposition P          term t of type P
proposition P is provable       type P is inhabited (by some term)
```
