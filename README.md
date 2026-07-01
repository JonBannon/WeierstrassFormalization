# WeierstrassFormalization

A Lean 4 / Mathlib formalization of *Integer Coefficients Power Series with
Prescribed Zero Sets* (Jon Bannon, David Feldman), proving that a discrete
effective divisor on the open unit disk is the zero divisor of a
holomorphic function with integer Taylor coefficients if and only if it is
invariant under complex conjugation (`thm:main`), via an intermediate
realization with Gaussian-integer coefficients (`prop:Zi`).

The whole development is complete: no `sorry`, no axioms beyond Mathlib's
standard three (`propext`, `Classical.choice`, `Quot.sound`).

## Documentation

* **[Blueprint](blueprint/src/content.tex)** — an expository account of
  every definition and theorem, each tagged with the Lean declaration that
  formalizes it and (once the site is deployed, see below) rendered as a
  browsable web page with a dependency graph.
* **API documentation** is generated from the Lean source's module and
  declaration doc-strings via `doc-gen4`.

Both are built automatically by CI (`.github/workflows/lean_action_ci.yml`,
via [`docgen-action`](https://github.com/leanprover-community/docgen-action)
with `blueprint: true`) and deployed to GitHub Pages on every push to the
default branch, once Pages is enabled (see below). Locally:

```sh
# Build and check the Lean project
lake build

# Verify every `\lean{...}` declaration cited in the blueprint really
# exists (the same check CI runs)
lake exe checkdecls blueprint/lean_decls

# Build the blueprint (requires Python and a TeX distribution with
# `latexmk`; install the tool with `pip install leanblueprint`)
leanblueprint pdf   # -> blueprint/print/print.pdf
leanblueprint web   # -> blueprint/web/index.html
```

## Project layout

| File | Contents |
|---|---|
| `WeierstrassFormalization/Basic.lean` | `𝔻`, `HolomorphicOn`, `taylorCoeff` |
| `WeierstrassFormalization/Divisor.lean` | `EffectiveDivisor`, `ConjInvariant`, `IsZeroDivisorOf` |
| `WeierstrassFormalization/ElementaryFactor.lean` | The modified elementary factor `E_n(w;c)` (Lemma `lem:structure`) |
| `WeierstrassFormalization/AffineControl.lean` | Affine coefficient control (Lemma `lem:affine`, Remark `rem:triangular`) |
| `WeierstrassFormalization/WeierstrassProduct.lean` | The Weierstrass-product construction underlying Theorem `prop:Zi` |
| `WeierstrassFormalization/GaussianRealization.lean` | Theorem `prop:Zi` (Gaussian-integer realization) |
| `WeierstrassFormalization/ComplexConjugation.lean` | Shared double-conjugation lemmas |
| `WeierstrassFormalization/ConjugatePairing.lean` | The conjugate-pairing construction for the sufficiency half of `thm:main` |
| `WeierstrassFormalization/MainTheorem.lean` | Theorem `thm:main` |

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
