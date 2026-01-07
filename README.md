## erasure-impl

Toy implementation of type theory with erasure.

For type formers we only have mode-aware Π and U.
The notation is:
```haskell
(0 x : A) -> B -- erased Π
(x : A) -> B   -- runtime Π
```

To keep this self-contained and understandable, I have based it on András
Kovács' `elaboration-zoo` which is reasonably well-known
[`elaboration-zoo/04-implicit-args`](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/04-implicit-args)