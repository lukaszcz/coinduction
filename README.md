Coinduction (dev) plugin for Coq 8.9

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
`ccrush`                         |  A general-purpose automated crush-like tactic.
`csolve on t`                    |  Performs case analysis on `t` followed by automated proof search.
`peek t`                         |  Forces a cofixpoint reduction in `t`.
`peek_eq`                        |  A tactic to automatically prove lemmas about unfoldings of cofixpoint definitions.
`Declare_peek I`                 |  This command must be invoked before using the `peek` and `peek_eq` tactics with terms having the coinductive type I.

Some examples are given in the [`examples`](examples) directory. For
examples with the `peek` and `peek_eq` tactics see
[`examples/practical.v`](examples/practical.v).
