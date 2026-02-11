import Veil
-- This makes the Veil DSL available in this file, and imports
-- the Veil standard library (`Veil.Std`), which contains a number of
-- useful first-order-logic axiomatisations of common structures.

/-! # Leader Election in a Ring

This file specifies a very simple distributed protocol in Veil, showcasing the
framework's main features.

The protocol is leader election in a ring. It works as follows:

- There are a finite number of nodes, each of which has a unique identifier.
- The nodes are arranged in a ring topology, where each node has a unique
  successor and predecessor. Nodes can only send messages to their immediate
  successor. (That is, the ring is unidirectional.)
- The goal is for one node to be elected as leader.
- Every node sends a message containing its identifier to its successor.
- When a node receives a message, it only forwards it along the ring if the
  contained identifier is GREATER than its own.
- A node becomes the leader if it receives its own identifier from its
  predecessor.

The protocol works because only the node with the highest identifier can
circulate its message around the entire ring. Each node forwards messages
containing higher identifiers than its own. Since identifiers are unique, the
maximum identifier will eventually return to its originating node, which becomes
the leader. All other identifiers get blocked by nodes with higher identifiers
during their traversal.

Concretely, the protocol has the following _safety_ property: at most one node
can be elected as leader.

In the remainder of this file, we will specify the protocol in Veil, and prove
its correctness automatically using SMT.
-/

/- This defines a new Veil module named `Ring`. In Lean terms, `Ring` is a
`namespace`. -/
veil module Ring

/- This defines a new (uninterpreted) type `node`, to represent node IDs. The
`type` command in Veil defines a Lean type that is sound to use as an SMT sort,
i.e. one that comes with an instance of the `Inhabited` typeclass. -/
type node

/- This instantiates the `TotalOrder` class for `node`. You can right-click and
'Go to definition' (F12) to see the axioms this introduces.

Concretely, it defines an (immutable) relation `tot.le` between nodes, and
provides the standard reflexivity, transitivity, antisymmetry, and totality
axioms for it. -/
instantiate tot : TotalOrder node

/- This instantiates the `Between` class for `node`. It encodes the fact that
the `node`s form a (unidirectional) ring topology.

It defines an (immutable) relation `btwn.btw (x y z : node)` between nodes, read
as "y is between x and z".

    .---.---.
   /         \
  w           z
  |           |      ring goes counter-clockwise (i.e. w -> x -> y -> z -> w)
  x           .
   \         /
    .---.---y

The relation `btw x y z` means that `y` lies between `x` and `z` when traversing
the ring counter-clockwise, as shown in the diagram above.

The axioms are as follows:
- [btw_ring] `∀ x y z, btw x y z → btw y z x`
- [btw_trans] `∀ w x y z, btw w x y → btw w y z → btw w x z`
- [btw_side] `∀ w x y, btw w x y → ¬ btw w y x`
  - this encodes the fact that the ring is unidirectional: it is NOT the case
    that `y` is between `w` and `x` since that would entail going
    clockwise, which is not allowed
- [btw_total] `∀ w x y, btw w x y ∨ btw w y x ∨ w = x ∨ w = y ∨ x = y`
-/
instantiate btwn : Between node

/- We open the `Between` and `TotalOrder` namespaces, so that we can use the
`le` and `btw` relations without prefixing them with `tot` and `btwn`. -/
open Between TotalOrder

/-
We model the state of this protocol as follows, with two (FOL) relations:
- `leader : node → Prop` tracks which nodes believe they are the leader
  `leader n = True` means node `n` believes it is the leader.

   The safety property is that at most one node can be elected as leader, i.e.
   `∀ n1 n2, leader n1 ∧ leader n2 → n1 = n2`. We will specify this later.

- `pending : node → node → Prop` tracks messages in transit, where `pending s d`
  means there is a message containing node `s`'s ID that has been sent to node
  `d`. Note that, for simplicity, we do not model the sender of the message
  (e.g. by defining the relation as
  `pending (src : node) (id : node) (dest : node)`), but only its _original_
  sender (which matches the ID within the message). There is no need to track
  the full path a message has taken through the ring.
-/

/- `leader n = True` means node `n` believes it is the leader.

  NOTE: make sure you use `Prop` (`True` / `False`) in Veil rather than `bool`
  (`true` / `false`). You might see very confusing error messages if you use the
  latter. We are working on making this more user-friendly. -/
relation leader : node → Bool
-- alternative syntax: `relation leader (n : node)`

-- `pending id dest = True` means there is a message containing node `id`'s ID
-- that has been sent to (and can be received by) node `dest`
relation pending : node → node → Bool

/- This declares an inductive datatype `Ring.State` that encodes the state of
the Ring transition system / protocol. -/
#gen_state

/- We can inspect the generated datatype. This is a regular Lean definition
(rather than a deeply-embedded object), so you can use it in any context you
want within Lean. It *corresponds* to the following `structure` definition:

```lean
structure State (node : Type) where
  leader : node -> Prop
  pending : node -> node -> Prop
```

In reality, it is more complicated, and looks like this:

```lean
structure Ring.State (χ : State.Label → Type) where
  Ring.State.leader : χ State.Label.leader
  Ring.State.pending : χ State.Label.pending
```

I.e., the actual types of the fields are parameterised by a type family `χ`
from `State.Label`s (names of fields) to `Type`s. Veil supports different state
representations to enable both efficient symbolic execution and efficient
concrete execution (for `#model_check`, as you will see later).
 -/
#print State

/- Veil's model of a specification is a state transition system. Having just
defined the type of states, we now define the initial state.

Formally, every Veil transition system has an indeterminate (nondeterministic)
_initial state_, which is immediately modified by an _action_ specified in the
`after_init` block.

In practice, you can think of `after_init` as directly specifying the initial
state, however. Indeed, in Veil, it defines the `initialState?` property, which
is a definition of type `State → Prop`.
-/
after_init {
  /- In assignments (and `safety` property and `invariant` clause declarations),
  capital letters are universally quantified. This a convention we adopt from
  Ivy. For instance, `leader N := False` means that for all nodes `n`,
  `leader n = False`. -/
  leader N := false
  /- `∀ m n, pending m n := False`
    or equivalently: `pending := fun M N => False` -/
  pending M N := false
}

/-
_Actions_ in Veil are imperative code fragments that modify the state. Veil
"compiles" actions to two-state transition relations (i.e. definitions of type
`State → State → Prop`).

Here we define an action `send`, with parameters `n` and `next` of type `node`,
that specifies what node `n` does when it initiates the protocol, i.e. it sends
a message containing its own ID to its successor (`next`).
-/
action send (n next : node) {
  /- A `require` statement specifies a condition that must be satisfied for the
  action to take effect / trigger. Here we encode that `next` is indeed the
  successor of `n` in the ring. -/
  require n ≠ next ∧ ∀ Z, ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

/- Instead of "inlining" the condition for a node `next` to be the successor of
`n` in all our actions, we can define a `ghost` `relation`, i.e. a derived
relation defined in terms of the "real" state. (In this case, `isNext` does not
in fact depend on the state, but it could.) -/
ghost relation isNext (n : node) (next : node) :=
  ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)

#print isNext

/- `n` receives a message containing `sender`, and potentially forwards it to `next`. -/
action recv (sender n next : node) {
  require isNext n next
  require pending sender n

  /- We can use non-deterministic assignment to model that the message may or
  may not be removed (i.e. it can potentially be received many times). -/
  let isPresent ← pick Bool
  pending sender n := isPresent

  /-
    Non-deterministic assignment is more general also lets us express things like
    `pending ID N := *` (the entirety of the `pending` relation is now
    indeterminate), i.e.:
    ```lean
    let newPending ← pick (node → node → Bool)
    pending := newPending
    ```
    -/

  if (sender = n) then
    leader n := true
  else
    if (le n sender) then
      pending sender next := true
}

/- This is the safety property we want to establish. `L1` and `L2` are
implicitly universally quantified, i.e. this means:
`∀ (L1 L2 : node), leader L1 ∧ leader L2 → L1 = L2` -/
safety [single_leader] leader N ∧ leader M → N = M

/- These invariant clauses together with the safety property above form an
inductive invariant. COMMENT THEM OUT to see how Veil can be used to manually
discover invariants, guided by counterexamples to induction. -/
invariant [leader_greatest] leader L → le N L
invariant [self_msg_greatest] pending L L → le N L
invariant [drop_smaller] pending S D ∧ btw S N D → le N S

/- Before we can operate on the specification in any way (e.g. check it), we
must run the `#gen_spec` command. -/
#gen_spec

/- We also support bounded model checking to validate the protocol. We use this
especially to validate that our protocol specifications are non-vacuous, i.e.
they do actually admit interesting executions.

We have two forms of bounded model checking:

  - Explicit-state model checking (like TLC), using `#model_check`. For this,
  you need to provide concrete finite instantiations of the types used in the
  specification. Here, we instantiate `node` as `Fin 4`, i.e. the finite type
  with 4 elements: `{0, 1, 2, 3}`. This then *executes* the protocol, i.e.
  enumerates all possible concrete traces of the protocol with 4 nodes, trying
  to find an execution that violates the safety property or any of the
  invariants (or has a failing `assert`).

  - Symbolic model checking (like mypyvy), using `sat trace` or `unsat trace`,
  explained below. This invokes an SMT solver to search for traces of a certain
  shape.
-/

#model_check { node := Fin 4 }

/- A trace specification consists of:
- `sat`/`unsat` -- is the trace satisfiable?
- `[an_optional_name]` -- the name of the trace; can be omitted
- `{ ... }` -- the trace specification, consisting of:
  - a sequence of actions, either explicitly listed or using `any action` or
    `any N actions`
  - `assert` statements to be checked against the state at that point in the
    trace

TIP: you can write `by` after the trace specification to Lean goal we are
trying to prove is either satisfiable or unsatisfiable. This is quite verbose
to enable Veil to reconstruct a trace it can display to you.
-/

/- This checks that there exists an initial state. -/
sat trace [initial_state] {}

sat trace {
  any 3 actions
  assert (∃ l, leader l)
}

unsat trace [cannot_receive_without_send] {
  recv
}

unsat trace {
  any 5 actions
  assert (∃ n₁ n₂, n₁ ≠ n₂ ∧ leader n₁ ∧ leader n₂)
}

/- TIP: Press the pause (⏸) button in the Lean Infoview to "lock" the
counter-example, so you can look at it while you type the `invariant` clause you
want to add above. Then press play (▶) button to re-check the spec with the
newly added invariant. -/

/-

If you COMMENT OUT the `invariant` clauses above, you will see the following
output. This shows that the `single_leader` invariant is not preserved by the
`recv` action, i.e.

The following set of actions must preserve the invariant and successfully terminate:
  recv
    single_leader ... ❌
      Counterexample (WP):
        Pre-state:
          leader = [1]
          pending = [[0, 0], [0, 1], [1, 0], [1, 1]]
        Action: recv(n=0, next=1, sender=0)
      Counterexample (TR):
        Pre-state:
          leader = [0]
          pending = [[0, 0], [0, 1], [1, 0], [1, 1]]
        Action: recv(n=1, next=0, sender=1)
        Post-state:
          leader = [0, 1]
          pending = [[0, 0], [0, 1], [1, 0], [1, 1]]
  send
    single_leader ... ✅

(We recommend you use the infoview widget, which is much easier to read than
the textual output.)

This is a counterexample to induction (CTI). It shows a pre-state (`st`) that
satisfies the inductive invariant, and a post-state (`st'`) which is reached
from `st` by the `recv` action, but with `st'` not satisfying the
`single_leader` property.

The pre-state `st` is not in fact reachable in valid executions of the protocol,
since here `node` is a leader, but it is not the node with the highest ID
(`tot.le(node1, node0`, i.e. `node1 ≤ node0`). This cannot be the case. To
eliminate this CTI, we add the following clause to our invariant:

```lean
invariant [leader_greatest] leader L → le N L
```

We can repeat this process until we eliminate all CTIs and thus find an
inductive invariant that establishes the safety of the system.
-/

#check_invariants

/- TIP: you can run Cmd+Click (weakest-precondition style VCs) or
Cmd+Shift+Click (TR-style VCs) to see the theorem statements that couldn't be
proven. In this case: -/
theorem recv_single_leader (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] [tot : TotalOrder node] [btwn : Between node] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f)
          (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory node) ρ]
    [recv_dec_0 :
      (n next : node) →
        Decidable
          (∀ (Z : node),
            And (Not (@Eq.{1} node n next)) (And (@Ne.{1} node Z n) (@Ne.{1} node Z next) → @btw node btwn n next Z))]
    [recv_dec_1 : (sender n : node) → Decidable (@le node tot n sender)] :
    ∀ (sender : node) (n : node) (next : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@recv.ext ρ σ node node_dec_eq node_inhabited tot btwn χ χ_rep χ_rep_lawful σ_sub ρ_sub recv_dec_0 recv_dec_1
          sender n next)
        (@Assumptions ρ node node_dec_eq node_inhabited tot btwn ρ_sub)
        (@Invariants ρ σ node node_dec_eq node_inhabited tot btwn χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@single_leader ρ σ node node_dec_eq node_inhabited tot btwn χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  sorry

end Ring
