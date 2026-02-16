# formal-structures

Formalizing algebraic structures, category theory, type theory, and their connections to machine learning — in Lean 4.

## Goals

This project is a structured study of the mathematical foundations underlying modern mathematics and machine learning, formalized in Lean 4 with Mathlib.

The driving questions:

- **What are algebraic structures, compositionally?** Groups, rings, fields, modules, vector spaces — understood as configurations of sorts, operations, and compatibility axioms.
- **How does category theory unify them?** Functors, natural transformations, adjunctions, monads, universal properties.
- **What is the algebra of logic?** Boolean algebras, Heyting algebras, lattices, and the algebraization of classical and intuitionistic logic.
- **What is type theory, formally?** Dependent types, propositions-as-types, universes, and how sorts and types relate.
- **What algebraic structures underlie ML?** Why ML lives in vector spaces, what it means to go beyond (Riemannian manifolds, Lie groups, sheaves, coalgebras), and open problems like the type of learned representations and compositional generalization as functoriality.

## Study Plan

### Phase 1: Algebra Refresher (via formalization)
- Groups, homomorphisms, isomorphism theorems
- Rings, fields, modules, vector spaces as multi-sorted structures
- Universal algebra: signatures, equational theories, varieties

### Phase 2: Category Theory
- Categories, functors, natural transformations
- Universal properties, limits, colimits
- Adjunctions and monads
- Yoneda lemma
- Following Riehl's *Category Theory in Context*

### Phase 3: Order and Logic
- Posets, lattices, distributive lattices
- Boolean algebras ↔ classical logic
- Heyting algebras ↔ intuitionistic logic
- The Lindenbaum–Tarski construction

### Phase 4: Type Theory
- Dependent types in practice (Lean itself)
- Curry-Howard correspondence
- Universes and the type-theoretic hierarchy
- HoTT: identity types, univalence (first chapters of the HoTT book)

### Phase 5: Toward ML Foundations
- Formalizing vector spaces and linear maps
- Bilinear forms and attention as a learned bilinear form
- Group representations and equivariance
- Exploring: What is the "true type" of a learned representation in ℝᵈ?
- Exploring: Compositional generalization as functoriality
- Exploring: Coalgebraic perspective on ML models

## Resources

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) — primary interactive tutorial
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) — language reference
- Riehl, *Category Theory in Context* — category theory textbook
- Aluffi, *Algebra: Chapter 0* — algebra through categorical lens
- HoTT Book — homotopy type theory
- [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Loogle](https://loogle.lean-lang.org/) — search Mathlib by type signature
- [Moogle](https://www.moogle.ai/) — search Mathlib by natural language

## Setup

```bash
# Clone
git clone https://github.com/takschdube/formal-structures.git
cd formal-structures

# Download pre-built Mathlib (essential — do not skip)
lake exe cache get

# Build
lake build

# Open in VS Code with Lean 4 extension
code .
```

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).