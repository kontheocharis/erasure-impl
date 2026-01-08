# Pattern unification with erasure

Pattern unification is about solving a certain subset of higher-order
unification problems, that allow us to implement implicit arguments and other
elaborationf eatures. How does pattern unification generalise when we are
dealing with a language that has phase distinctions, like erasure?

We assume basic working knowledge of CwF-style type theory.

## Review of pattern unification

In standard dependent type theory, a pattern unification problem has the form:

```
Γ ⊢ ?m[σ] ≡ t
```

where `Γ, Δ : Con`, `σ : Sub Γ Δ`, `t : Tm Γ A[σ]`, and `?m : Tm Δ A` is the
(neutral) hole we want to solve for. We can think of `Δ` as the context in which
the metavariable is created, and `Γ` as the context in which a solution is being
attempted.

For a solution to exist, we must have the following additional conditions:

1. `σ` is a linear renaming: it consists only of distinct variables in
  `Γ`. In other words, it is a `σ : LinRen Γ Δ ⊆ Ren Γ Δ ⊆ Sub Γ Δ`. We can
  alternatively characterise linear renamings as those renamings which are
  epimorphisms: those for which `u[σ] = v[σ]` implies `u = v`. Additionally, it
  is possible to *invert* such renamings: we have `σ⁻¹ : PRen Δ Γ` which has a
  partial substitution action on terms in Γ: specifically, it is defined on
  those terms in `Γ` which only use variables present in `σ`.
2. `t` only contains variables from `σ`. This means that `t[σ⁻¹]` is defined.
3. `t` does not contain `?m`.

If these conditions are met, then we can peform the following operation on the
problem:

```
Γ ⊢ ?m[σ] ≡ t

(apply σ⁻¹ to both sides)
⟹ Δ ⊢ ?m[σ][σ⁻¹] ≡ t[σ⁻¹]   

(LHS reduces to ?m so is defined, RHS is defined by requirement 2)
⟹ Δ ⊢ ?m ≡ t[σ⁻¹] 
```

The above is thus a solution for `Δ`. It is in fact the unique solution.

In a practical setting, we represent `?m[σ]` as a metavariable applied to an
argument spine: `?m σ`. We then represent the solution as a closed iterated
function type: `?m = Δ ⇒ t[σ⁻¹]`

There are further things we can do to 'pre-process' the problem, primarily to
*prune* metavariable spines ocurring inside `t`, so that those variables don't
need to appear in `σ` for a solution to be valid. This is orthogonal to the
rest of this document.

## Adding erasure

What happens when we add erasure to the language? There are two main things:

1. We now have both runtime terms `Tm ω` and erased terms `Tm 0`.
2. There is an additional proof-irrelevant sort `# ∈ Γ` with context extension
    `Γ ▷ #` whose (decidable) presence determines whether we can coerce `Tm 0`
    to `Tm ω`; we can always coerce `Tm ω` to `Tm 0`. More specifically, we have
    the definitional isomorphism
    ```
    (↑, ↓) : Tm ω (Γ ▷ #) A ≃ Tm 0 Γ A
    ```
    of mode shifts.
    
Point 1 is not of consequence. Up to definitional equality, every erased term is
of the form `↓ b : Tm 0 Γ A` for some runtime term `b : Tm ω (Γ ▷ #) A`. For
this reason, we only need metas in `Tm ω`.

A pattern unification problem now looks the same as before

```
Γ ⊢ ?m[σ] ≡ t
```

where `Γ, Δ : Con`, `σ : Sub Γ Δ`, `t : Tm ω Γ A[σ]`, and `?m : Tm ω Δ A` is the
(neutral) hole we want to solve for.

For a solution, we must have the following conditions which are slightly
different than before:

1. `σ` is a linear renaming *up to mode shifts*: it consists only of distinct
  variables in `Γ` potentially wrapped in `↑` or `↓`. These renamings are still
  epimorphisms, but it only sometimes possible to invert them;
2. If `# ∈ Γ` and `# ∉ Δ`, then `σ` must not contain any `↓`, because those
  cannot be inverted. -- Actually this rule is wrong; @@FIXME: it should be that no solution
  is allowed under such circumstances unless the RHS doesn't use `#`/can be strengthened...
  this is more annoying!
2. `t` only contains variables from `σ`. This along with conditions 1 and 2
   mean that `t[σ⁻¹]` is defined.
3. `t` does not contain `?m`.

The `# ∈ Γ` sort is proof-irrelevant, meaning for any two witnesses `p, q : # ∈
Γ` , we have `p ≡ q`. Therefore, in implementation:

- We (only) need a flag on contexts that records if `#` is present (to decide `#
  ∈ Γ`, but also for typechecking)
- We also need a flag on metavariable contexts for the same reason (to decide `# ∈ Δ`)

Besides that, the implementation depends on if we choose to include the mode
shifts as part of the syntax in the compiler. We implement both approaches
in this repository.

### If mode shifts are part of the compiler syntax (`explicit`)

We can decide condition 2 just by looking at whether there are any `↑`/`↓`
wrappers in the spine `σ`. We don't need to know the mode of any variable for
unification, only for typechecking. Regardless, we keep track of the declared
modes of variables in the syntax itself. This is technically not necessary but
allows us to have a few more asserts to ensure the behaviour of mode shifting is 
correct.

### If mode shifts aren't part of the compiler syntax (`implicit`)

We must record the *modes* of all bindings for each metavariable context. We can
then compare them to the modes of the variables in the spine `σ` to check
condition 2. One way to achieve this is to have access to the context's mode
bindings during unification. Alternatively, we can choose to remember variable
modes in the syntax itself. We choose the latter.
