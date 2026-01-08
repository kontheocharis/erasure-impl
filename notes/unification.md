# Unification with phases

Pattern unification is about solving a certain subset of higher-order
unification problems, that allow us to implement implicit arguments and other
elaborationf eatures. How does pattern unification generalise when we are
dealing with a language that has phase distinctions, like erasure?

We assume working knowledge of CwFs/algebraic type theory.

## Review of pattern unification

In standard dependent type theory, a pattern unification problem has the form:

```
Γ ⊢ ?m[σ] ≡ t
```

where `Γ, Δ : Con`, `σ : Sub Γ Δ`, `t : Tm Γ A[σ]`, and `?m : Tm Δ A` is the
(neutral) hole we want to solve for. This is subject to the additional
conditions:

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
need to appear in `σ` for a solution to be valid. We won't worry about this
because it is somewhat orthogonal to our goals.

## Pattern unification with erasure

What happens when we add erasure to the theory? There are two main things:

1. We now have both runtime terms `Tm ω` and erased terms `Tm 0`.
  We use `Γ ▷[i] A` for context extension of `Tm i`.
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
(neutral) hole we want to solve for. This is subject to additional
conditions which are slightly different than before:

1. `σ` is a linear renaming *up to mode shifts*: it consists only of distinct
  variables in `Γ` potentially wrapped in `↑` or `↓`. These renamings are still
  epimorphisms, but it only sometimes possible to invert them;
2. If `# ∈ Γ` and `# ∉ Δ`, then `σ` must not contain any `↓`, because those
  cannot be inverted.
2. `t` only contains variables from `σ`. This along with conditions 1 and 2
   mean that `t[σ⁻¹]` is defined.
3. `t` does not contain `?m`.




The `# ∈ Γ` sort is proof-irrelevant, meaning for any two witnesses `p, q : # ∈
Γ` , we have `p ≡ q`. Because of this, in implementation we only need a flag on
contexts that records if `#` is present, rather than mixing it with all the
other context entires.

  