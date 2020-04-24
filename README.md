Coinduction (dev) plugin for Coq 8.10

Installation
------------

Run `make` followed by `make install`.

Usage
-----

To load the plugin:

```coq
From Coinduction Require Import Coinduction.
```

Available commands:

command                          | description
-------------------------------- | -----------------------------------------------
`CoInduction`                    |  Starts a coinductive proof of a lemma.
`peek t`                         |  Forces a cofixpoint reduction in `t`.
`peek_eq`                        |  A tactic to automatically prove lemmas about unfoldings of cofixpoint definitions.
`Declare_peek I`                 |  This command must be invoked before using the `peek` and `peek_eq` tactics with terms having the coinductive type I.

Some examples are given in the [`examples`](examples) directory. For
examples with the `peek` and `peek_eq` tactics see
[`examples/practical.v`](examples/practical.v).

To compile the examples you need to install
[CoqHammer](https://github.com/lukaszcz/coqhammer) reconstruction
tactics.

Because CoqHammer tactics sometimes perform unnecessary forward
reasoning followed by case analysis, they occasionally produce proofs
that do not satify the "weak case restriction", which makes our
translation fail. To reduce the probability of this happening, use the
"c-variants" of the tactics: `cauto`, `csimpl` and `ccrush`. See
[`examples/tutorial.v`](examples/tutorial.v).

Papers
------

Łukasz Czajka,
[First-order guarded coinduction in Coq](https://www.mimuw.edu.pl/~lukaszcz/focoind.pdf),
ITP 2019
