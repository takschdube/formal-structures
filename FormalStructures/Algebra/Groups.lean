/-
# Groups — The Anatomy of a Single-Sorted Algebraic Structure

A group is the simplest non-trivial example of a **single-sorted algebraic structure**:
  - **One sort** (one carrier type `G`)
  - **Operations**: a binary operation `mul : G → G → G`, a unary operation `inv : G → G`,
    and a nullary operation (constant) `e : G`
  - **Axioms**: associativity, identity, inverses

Notice how "closure" isn't listed as a separate axiom — it's encoded in the *types*.
The signature `mul : G → G → G` guarantees that multiplying two elements of `G`
produces an element of `G`. This is one of the advantages of working in type theory
rather than set theory: closure is a *typing judgment*, not a proposition to prove.

## From the universal algebra perspective

A group is an algebra with:
  - Signature σ = {(mul, 2), (inv, 1), (e, 0)}  — operation names with arities
  - Equational theory:
      ∀ a b c, mul(mul(a, b), c) = mul(a, mul(b, c))   -- associativity
      ∀ a, mul(e, a) = a                                 -- left identity
      ∀ a, mul(inv(a), a) = e                            -- left inverse

We'll revisit this decomposition when we get to UniversalAlgebra/.
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

/-!
## Our own group definition ("from scratch")

We define `MyGroup` as a class so we can see exactly what goes into the definition.
Compare this with Mathlib's `Group`, which builds on a hierarchy:
  `Mul → Semigroup → Monoid → Group`

Our version is flat — all axioms in one place — which is closer to how you'd
write it in an algebra textbook.
-/

/-- A group structure on a type `G`.

This bundles a binary operation, identity element, and inverse function,
together with the group axioms. We use `mul` rather than `*` notation
to make the structure explicit. -/
class MyGroup (G : Type*) where
  /-- The binary operation (the "multiplication") -/
  mul : G → G → G
  /-- The identity element (the nullary operation) -/
  e : G
  /-- The inverse function (the unary operation) -/
  inv : G → G
  /-- Associativity: mul is associative -/
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  /-- Left identity: `e` is a left identity for `mul` -/
  mul_left_id : ∀ a : G, mul e a = a
  /-- Left inverse: `inv a` is a left inverse of `a` -/
  mul_left_inv : ∀ a : G, mul (inv a) a = e

namespace MyGroup

variable {G : Type*} [MyGroup G]

/-!
## Theorem: The identity element is unique

This is typically the first theorem you prove about groups.

**Mathematical statement**: If `e'` is any left identity (i.e., `e' * a = a` for all `a`),
then `e' = e`.

**Proof idea**: Evaluate `e' * e` in two ways:
  - `e' * e = e`  (because `e'` is a left identity, applied to `a := e`)
  - `e' * e = e'` (this needs right identity, which we derive from left identity + left inverse)

So we first need to show that `e` is also a *right* identity and that left inverses
are also right inverses. This is a nice exercise in how minimal axioms bootstrap
the full structure.
-/

/-- Right inverse: `mul a (inv a) = e`.

We only assumed *left* inverse, but it follows from left identity + left inverse +
associativity. This is a classic algebraic bootstrap. -/
theorem mul_right_inv (a : G) : mul a (inv a) = e := by
  -- The idea: show inv(inv a) * inv a = e, then use that to manipulate a * inv a
  -- Key identity: a = inv(inv a) * (inv a * a) ... wait, let's be more careful.
  -- We compute:  a * inv a = e * (a * inv a)                     [left id]
  --            = (inv(inv a) * inv a) * (a * inv a)               [left inv]
  --            = inv(inv a) * (inv a * (a * inv a))               [assoc]
  --            = inv(inv a) * ((inv a * a) * inv a)               [assoc]
  --            = inv(inv a) * (e * inv a)                         [left inv]
  --            = inv(inv a) * inv a                               [left id]
  --            = e                                                [left inv]
  have h1 : mul (inv (inv a)) (inv a) = e := mul_left_inv (inv a)
  calc mul a (inv a)
      = mul e (mul a (inv a)) := by rw [mul_left_id]
    _ = mul (mul (inv (inv a)) (inv a)) (mul a (inv a)) := by rw [h1]
    _ = mul (inv (inv a)) (mul (inv a) (mul a (inv a))) := by rw [mul_assoc]
    _ = mul (inv (inv a)) (mul (mul (inv a) a) (inv a)) := by rw [mul_assoc]
    _ = mul (inv (inv a)) (mul e (inv a)) := by rw [mul_left_inv]
    _ = mul (inv (inv a)) (inv a) := by rw [mul_left_id]
    _ = e := by rw [h1]

/-- Right identity: `mul a e = a`.

Follows from right inverse (just proved) and left identity. -/
theorem mul_right_id (a : G) : mul a e = a := by
  calc mul a e
      = mul a (mul (inv a) a) := by rw [mul_left_inv]
    _ = mul (mul a (inv a)) a := by rw [mul_assoc]
    _ = mul e a := by rw [mul_right_inv]
    _ = a := by rw [mul_left_id]

/-- **Uniqueness of the identity element.**

If `e'` is any element satisfying `∀ a, mul e' a = a` (i.e., it acts as a
left identity), then `e' = e`.

This is important from the universal algebra perspective: the identity is
*determined* by the axioms. It's not extra data you're free to choose — once
you fix the operation `mul`, there's at most one identity. -/
theorem identity_unique (e' : G) (h : ∀ a : G, mul e' a = a) : e' = e := by
  -- Evaluate e' * e using both properties:
  -- From h:      e' * e = e      (e' is a left identity)
  -- From right_id: e' * e = e'   (e is a right identity)
  have h1 : mul e' e = e := h e
  have h2 : mul e' e = e' := mul_right_id e'
  -- Therefore e' = e
  exact h2.symm.trans h1

/-!
## What Mathlib does differently

Mathlib's `Group` doesn't look like our flat definition. It uses a *hierarchy*:

  `Mul G` → `Semigroup G` → `Monoid G` → `Group G`

Each level adds one piece:
  - `Mul`: just the operation `*`
  - `Semigroup`: `*` + associativity
  - `Monoid`: `Semigroup` + identity element `1` + identity axioms
  - `Group`: `Monoid` + inverses

This is a **design pattern** driven by Lean's typeclass system. It means:
  - A theorem about `Semigroup` automatically applies to groups, rings, etc.
  - You get "free" inheritance of all `Monoid` lemmas when working with groups
  - It mirrors the mathematical inclusion: every group IS a monoid IS a semigroup

We'll see this pattern a lot — Mathlib structures are *decomposed* along the
substructure lattice, while textbook definitions are *flat*.
-/

/-- Example: ℤ is a group under addition.

This is just to demonstrate instantiating our definition.
Of course, Mathlib already knows `AddGroup ℤ` — this is pedagogical. -/
instance : MyGroup ℤ where
  mul := (· + ·)
  e := 0
  inv := (- ·)
  mul_assoc := Int.add_assoc
  mul_left_id := Int.zero_add
  mul_left_inv := neg_add_cancel

-- Quick sanity check: our theorems work on a concrete group
#check @identity_unique ℤ _
-- `identity_unique : ∀ (e' : ℤ), (∀ (a : ℤ), e' + a = a) → e' = 0`

end MyGroup
