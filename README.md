# Lambda Calculus evaluator

Based on Types and Programming Languages.

## Running

```bash
$ git clone https://github.com/ErickHdez96/lc.git
$ cd lc
$ cargo run
```

## Examples

```
>> λx.x
λx.x

>> and true true
λt.λf.t

>> or false false
λt.λf.f

>> not true
λt.λf.f

>> not false
λt.λf.t
```

## TODO

* Allow user defined variables.
