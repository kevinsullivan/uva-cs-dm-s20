/-
An axiom is an assumed proof of a
given proposition. For example, we
accept as an *axiom* that there is
a proof that equality is reflexive.
refl : ∀ {α : Type} (a : α), a = a.

Natural deduction is a system of
reasoning rules for deducing proofs
of more complex propositions from
axioms. 

What we are doing in class now is
to implement (or at least to see
how an implementation is given in
the Lean libraries) of the syntax 
of predicate logic and the rules
of natural deduction.

For example, we implement the usual
and connective of predicate logic as
a polymorphic proposition : one with
two propositions as type arguments
(remember, propositions are types in
the logic of Lean).

inductive and (P Q : Prop) : Prop

The single intro constructor of this
polymorphic proposition provides the
axiom that explains how to deduce a
proof of P ∧ Q: apply "intro" to two
arguments, one a proof of P and one 
a proof of Q.

While the introduction axioms of natural
deduction explain how to construct (or
deduce) proofs of more complex propositions,
elimination rules tell us how we can "take 
apart" proofs to access the elements from
which they were constructed. These elements
are often proofs themselves.

For example, a proof of P ∧ Q is "built"
from a proof of P and a proof of Q, and
the "and elimination rules" give us ways
to extract these "smaller" proofs from a
larger proof of P ∧ Q. In this way, these
elimination rules extend our ability to
deduce consequences: e.g., P ∧ Q → P.

Each form of proposition has its own
introduction and elimination rules. The
syntax of the predicate logic of everyday mathematics defines propositions formed
using the following connectives and
quantifiers. It is your taks to learn
the introduction and elimination rules
for each one, and to be able to use them
in constructing and using proofs, both
formal and expressed in natural language.

∀ 
→ 
∧ 
↔
= 
¬ 
∨ 
∃

In the rest of this document, we succinctly
summarize these rules. We give examples of 
how to use such rule. We give each example 
in three forms: as a proof term, as a proof 
script, and as a natural language proof.
-/

/-
We start by assuming (as axioms) that P
and Q are arbitrary propositions. This
allows us not to have to introduce them
as assumptions in each of the examples.

For example, instead of writing

∀ (P Q : Prop), P ∧ Q → P, we can now
just write P ∧ Q → P, because P and Q
are already assumed to be propositions
(terms of type Prop in Lean).
-/

axioms P Q : Prop

/-
With this presentation easing trick out
of the way, we now proceed to discuss each
connective and quantifier and its rules of
inference (introduction, elimination rules).
-/

/- *** FORALL *** -/

/-
Here's the form of a universal generalization.
It asserts that if one is given any proof of P,
then there is a proof of Q. 
-/
def univeral_generalization := ∀ (p : P), Q

/-
To prove a proposition of this form, we first
*assume* that we're given an arbitarary but
specific proof of (value of type) P, and in
that context, our remaining goal is to build
a proof of Q. Here we don't know in detail
what proposition Q is, so we can't complete
the proof; but nevertheless, as far as it
goes, the proof fully illustrates how one
uses the "forall introduction" rule.
-/
example : univeral_generalization :=
λ p,
_

/-
As a proof script.
-/
example : univeral_generalization :=
begin
unfold univeral_generalization, 
/-
The unfold tactic replaces an identifier
with the value to which it's bound. In this
case, it helps us to see more clearly what
is to be proved. Surprisingly, what is to 
be proved is an implication: P → Q. A key
insight is that P → Q is just a shorthand
for ∀ (p : P), Q! What is to be shown is
that *if* one is given *any* proof of P,
then one can always construct a proof of
Q. Now one proceeds to use the introduction
rule for →: assume that one is given a
proof of P, and the remaining goal is to
show Q.
-/
assume (p : P),
/-
The show tactic simply documents in a
proof script what remains to be done:
in this case, to produce a proof (we
can give it a name, here q) of Q.
-/
show (q : Q),
/-
And once again, we can make no further
progress, so we just leave the proof
unfinished. Note: no use can be made
of an unfinished proof; if we finish
a proof with "sorry", we're telling 
Lean to accept the proposition as true
without proof, i.e., as an axiom. We
do not wish to do that here, so we just
leave the proof unfinished.
-/
_,
end

/-
As a final comment, we emphasize that
the proceeding example shows how we 
can approach the construction of a proof
in a step by step way

(1) Ask what is the syntactic form of
proposition to be proved. Here the
answer is "it's a ∀ proposition, i.e.,
a universal generalization. 
(2) Ask what introduction "rules" can be
used to construct such a proof. For ∀ 
there is only one: ∀ introduction.
(3) Apply the rule. In this case, what
that means is that we need to show that
if we assume we're given any proof of 
P, we can always create a proof of Q.
We do this by defining a function with
one argument, an *assumed* proof of P. 
What remains to be proved is that, in
this context, a term of type Q, that
is, a proof of Q, can be produced. 
In developing proofs incrementally,
we often leave a "hole" for such a
term. This hole represents "the rest"
of what needs to be given to have a
complete proof: here what's left to
prove is Q.
-/

/-
Finally, here's a natural language proof.

-/


/- *** ∀ elimination *** -/

/-
If we know that *any* ball is blue, and
we know that b is a specific ball, then
we know that b is blue.
-/

Moreover, a proof of ∀ (p : P), Q
is effectively, and can be applied
as a function to any proof of P to 
construct a proof of Q. 
-/


example : 
    
    (∀ (p : P), Q) → P → Q
    :=
λ (a : (∀ (p : P), Q)),
    λ (p : P),
        _


example : (∀ (p : P), Q) → P → Q :=
begin
    assume (f : ∀ (p : P), Q),
    assume p,
    exact f p
end

/-
In English. If P and Q are arbitrary
propositions, (∀ (p : P), Q) → P → Q. 
To prove it, assume there are proofs 
of both (∀ (p : P), Q) and of P. Apply
the former to the latter to derive a
proof of Q.

-/

/-  *** → introduction ***

Arrow introduction is identical to
∀ introduction: assume the premise.
Then what remains to be proved, in
that context, is the conclusion. → 
introduction *is* ∀ introduction:
assume that values of specified
argument/premise types are given. 
-/

example : P → Q :=
    λ (p : P),      -- assume P
        _           -- show Q


example : P → Q :=
begin
assume (p : P),     -- assume P
_                   -- show Q
end

/-
In English, given propositions P and
Q, show P → Q. To start we assume P.
In this context we produce a proof of
Q. [There are not enough details about
either P or Q to complete the proof, 
but the step taken (assume P then 
show Q) illustrates → introduction].
-/

/-
   *** →  elimination ***

Arrow elimination is application:
Given a proof of P → Q (which we
can treat as a function of this 
type, that converts proofs of P
into proofs of Q), we can *use* 
the proof of P → Q  by *applying*
it to to any proof of P. The result
is a proof of Q. 

In the following exmples, we just
replace the ∀ notation from the two
preceding examples of ∀ elimination
with → notation. Compare the examples
carefully.
-/


example : 
    (P → Q) → 
    P → 
    Q :=
λ (f : ∀ (p : P), Q), -- proof of ∀ 
    λ (p : P),        -- proof of P
        _        -- ∀ elimination


example : (P → Q) → P → Q :=
begin
    assume (f : ∀ (p : P), Q),
    assume p,
    exact (f p)
end

/-
In English. Assume P and Q are arbitrary
propositions and whow (P → Q) → P → Q. 

Proof: Assume P → Q and assume P. Deduce 
Q by applying P → Q to P to obtain Q. QED.
-/



/- *** ∧ introduction ***

The ∧ connective is defined as an inductive
logical type that is polymorphic, taking two 
propositions (call them P and Q) as arguments
yielding the proposition, P ∧ Q. It provides
one proof constructor, in Lean called intro
(and.intro), of type P → Q → P ∧ Q. Given a
proof, p, of P, and a proof, q, of Q, it
constructs the term (and.intro p q), which
is accepted as being of type P ∧ Q, and so
to be a proof of this proposition.
-/


example : P → Q → P ∧ Q :=
λ (p : P),
    λ (q : Q),
        and.intro p q


example : P → Q → P ∧ Q :=
begin
    assume (p : P) (q : Q),
    exact (and.intro p q),
end

/-
In Enslish. Assume P and Q are arbitrary
propositions and show that P → Q → P ∧ Q.

Proof: Assuming P and Q are true and apply
and introduction to deduce P ∧ Q.
-/

/- *** ∧ elimination ***

One should note that the definition
of the logical connective, and, is
the analog, for logical types, of the
product type (Prod, in lean) of pairs
of values of the given types (proofs
of) P and Q.

The elimination rules for ∧ are then
just the analogs of the "projection"
functions for a given pair, by which
its component values can be extracted.
-/


example : (P ∧ Q) → P :=
λ (h : P ∧ Q),  -- given proof of P∧Q
    and.elim_left h -- return Q proof 


example : (P ∧ Q) → P :=
begin
    assume h,
    exact h.left
end

/-
In English. Assume P and Q are arbitrary
propostions and show (P ∧ Q) → P. 

Proof: This is done by the applying the
left elimination rule of natural deduction 
to (P ∧ Q). QED.
-/

/- *** = introduction ***

= is a polymorphic binary relation, on 
objects of any type. It is formalized in
Lean as the inductive type, eq, which
takes on type argument, implicitly.

The rule for constructing a proof of 
an equality proposition is that for
any value, a, of any type, α, a = a.
This is the introduction rule for =.
It is a universal generalization. To
obtain a proof of equality for any
specific values, one *applies* it to
one of those values. As long as the
two values really are equal, such a
proof is a proof that they are equal.
-/

example : 1 + 3 = 5 - 1 := eq.refl 4

/-
In English: We start by simplifying 
each side of the equality proposition.
The result is 4 = 4. This is true by
application of the reflexive property
of equality to the specific value, 4.
-/

/- *** = elimination ***

We have not yet discussed = elimination.

If one has values a and b of a type, T,
and proofs of (1) a = b, and of (2) 
"L a", where L is any predicate, of 
type P → Prop, then one uses equality
elimination to deduce "L b" from "L a". 

As an example, if Bill likes coffee 
(LC Bill), and if Bill = Bob, then Bob 
likes coffee (LC Bob).
-/


axiom L : P → Prop  -- assume predicate L

example : ∀ (a b : P), a = b → (L a → L b) := 
λ (a0 b0 : P),
λ (ab : a0 = b0),
λ (l : L a0),
(eq.subst ab l)

/-
    λ a b,  -- assume a and b are values of P
    λ heq,  -- assume a proof of a = b
    λ la,   -- assume a proof of (L a)
    (eq.subst heq la) -- deduce proof of (L b)
-/

/-
The comments give a concise English language
proof. Citing the substitution rule for equality
on the last line would make the proof clearer.
-/

example : ∀ (a b : P), a = b → (L a → L b) := 
begin
    assume a b,
    assume heq,
    assume la,
    rewrite <- heq,  -- change b to a in goal
    exact la,
end

/-
The eq.subst rule allows one to substitute
equals for equals in propositions without
changing their meaning. So, again, if Bill
likes coffee (LC Bill), and if Bill = Bob,
then it must be Bob likes coffee (LC Bob).
-/

/- *** Putting it all together ***

Proofs are constructed by composing these
introduction and elimination rules. Often
one needs both kinds of rules to complete 
a proof. As an example, consider proving
P ∧ Q → Q ∧ P. To do so, we assume that
P ∧ Q is true. From that assumption we
deduce that P is true and Q is true. We
then apply the rule of and introduction
to the derived proofs of Q and P, in that
order, to complete the overall proof. 
We thus show that *if* P ∧ Q is true, 
for any propositions P, Q, then Q ∧ P 
is true. The proof uses the introduction
rule for →, the left and right elimination
rules for ∧, and the introduction rule for 
∧ to put it all together. Here are formal
versions, first as a proof term and then
using a tactic script to build that proof
term. 
-/


example : P ∧ Q → Q ∧ P :=
λ (pq : P ∧ Q),     -- assume proof P ∧ Q
    and.intro       -- apply and.intro to 
        pq.right    -- proof of Q
        pq.left     -- proof of P


example : P ∧ Q → Q ∧ P :=
begin
    assume pq,
    apply and.intro,    -- introduction
    exact pq.right,     -- elimination
    exact pq.left,      -- elimination
end

/-
In English: Let P and Q be arbitrary
propositions [∀ intro]. Show that 
P ∧ Q → Q ∧ P. To do so, assume P ∧ Q
[→ intro]. From this assumption, 
deduce P and Q,respectively [∧ elim].
Finally, deduce Q ∧ P [∧ intro].
-/

/-
Here's a slightly more complex example,
in which a proof of (Q → R) is *applied*
to an argument (a proof of Q) to obtain
a proof of R. Proof construction is pure
functional programming!
-/

example : (P ∧ Q) ∧ (Q → R) → R :=
    λ h,                -- assume premise
        h.right         -- apply func : Q → R
        h.left.right    -- to proof of Q
                        -- to get proof of R

-- As a tactic script
example : (P ∧ Q) ∧ (Q → R) → R :=
begin
assume h : (P ∧ Q) ∧ (Q → R),
exact (h.right) (h.left.right),
end

-- Same, named intermediate results
example : (P ∧ Q) ∧ (Q → R) → R :=
begin
assume h : (P ∧ Q) ∧ (Q → R),
have qr : Q → R := h.right,
have q : Q := h.left.right,
exact (qr q),
end

-- Same, with type inference
example : (P ∧ Q) ∧ (Q → R) → R :=
begin
assume h,
have qr := h.right,
have q := h.left.right,
exact (qr q),
end

/-
In English: Suppose P and Q are
propositions. Show that (P ∧ Q) ∧ 
(Q → R) → R. To start, suppose 
(P ∧ Q) ∧ (Q → R) [→ intro]. Deduce 
Q from the left conjunct and Q → R 
from the right [and elim]. Apply 
the latter to the former [→ elim] 
to deduce R. QED.
-/

/-
A good practice for the exam would be
to prove, in Lean, each of the inference
rules that we validated in propositional
logic. You are prepared to this for the
rules that do NOT involve exists or not.
For ↔, use iff.intro and iff.elim_left
and iff.elim_right as if they were the
rules for and intro and elimination but
with proofs of implications as arguments.
-/

#check @iff.intro
#check @iff.elim_left
#check @iff.elim_right



/-
What does it mean, ¬ P?
-/

/-
Meet "false".
-/

def f : false := _

def weird (f : false) : 0 = 1 :=
    false.elim f

example : false → 0 = 1 := 
λ f, false.elim f

example : ¬ P := 
λ (p : P), _

example : P → ¬ P → false :=
λ (p : P), 
λ (np : ¬ P),
_

theorem proof_by_negation : ¬P :=
λ (p : P), _

/-

¬ P ==== P → 

-/