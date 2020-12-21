# Lambda Calculus evaluator

Based on Types and Programming Languages.

## Running

```bash
$ git clone https://github.com/ErickHdez96/lc.git
$ cd lc
$ cargo run
```

## Types

Currently the supported types are:

* Bool (true, false)
* Nat (0, succ Nat)
* Unit (unit)
* Base type (Any name)
* Abstractions (Type → Type)
* Records ({label:Type}, {Type,Type})

## Integrated functions

* pred

```
>> pred 0
0 : Nat

>> pred 1
0 : Nat

>> pred 2
suc 0 : Nat

>> pred 3
succ suc 0 : Nat
```

* succ

```
>> succ 0
succ 0 : Nat

>> succ pred 0
succ 0 : Nat

>> succ pred 1
succ 0 : Nat
```

* iszero

```
>> iszero 0
true : Bool

>> iszero 1
false : Bool

>> iszero pred succ 0
true : Bool

>> iszero succ pred 0
false : Bool
```

## Conditionals

`if t₁ then t₂ else t₃`

```
>> if true then 0 else 2
0 : Nat

>> if iszero 0 then 1 else 2
succ 0 : Nat

>> if and true true then succ 1 else 0
succ succ 0 : Nat
```

## Let bindings

`let x = t in t`

```
>> let x = true in x
true : Bool

>> let not = λb:Bool.if b then false else true in not true
false : Bool
```

## Records (and Tuples)

```
>> {true}
{true} : {Bool}

>> {true}.1
true : Bool

>> { isvalid=true, invalid=false }.isvalid
true : Bool

>> { first=0, true}
{first=0, true} : {first:Nat, Bool}
```

## Examples

```
>> \x:Bool.x
λx:Bool.x : Bool → Bool

>> \x:A.x
λx:A.x : A → A

>> and true true
true : Bool

>> or false false
false : Bool

>> not true
false : Bool

>> not false
true : Bool

>> if iszero pred 1 then true else false
true: Bool

>> \f:Bool -> Bool.\x:Bool.f x
λf:Bool → Bool.λx:Bool.f x : (Bool → Bool) → Bool → Bool

>> (\f:Bool -> Bool.\x:Bool.f x) not
λx:Bool.(λb:Bool.if b then false else true) x : Bool → Bool

>> (\f:Bool -> Bool.\x:Bool.f x) not true
false : Bool
```

## TODO

* Add better error messages
* General Recursion
* Lists
