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

Some examples are given in the [`examples`](examples) directory.
