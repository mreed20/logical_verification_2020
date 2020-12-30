import .love02_backward_proofs_demo


/- # LoVe Exercise 2: Backward Proofs -/


set_option pp.beta true
set_option pp.generalized_field_notation false
set_option trace.simplify.rewrite true


namespace LoVe

namespace backward_proofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma I (a : Prop) :
  a → a :=
begin
  -- ha := "hypothesis a"
  intro ha,
  exact ha,
  -- alternatively: assumption
end

lemma K (a b : Prop) :
  a → b → b :=
begin
  intros ha hb,
  exact hb
  -- alternatively: apply I,
end

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
begin
  intros habc hb ha,
  apply habc,
  { exact ha },
  { exact hb },
end

lemma proj_1st (a : Prop) :
  a → a → a :=
begin
  intros ha ha',
  exact ha,
end

/- Please give a different answer than for `proj_1st`: -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
begin
  intros ha ha',
  exact ha',
end

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
begin
  intros _ ha hac _,
  apply hac,
  apply ha,
end

/- 1.2. Prove the contraposition rule using basic tactics. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
begin
  intros hab,
  -- Note: Rewriting using `rw not_def` makes it much easier
  -- to see which of the negated hypotheses (¬ b, ¬ a) can apply
  -- at each step in the proof.
  rw not_def,
  intro hnb,
  rw not_def,
  intro ha,
  apply hnb,
  apply hab,
  exact ha,
end

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap₂` in the lecture, might be
necessary. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
begin
  -- introduce the ↔ so that I can use `intro`
  apply iff.intro,
  { -- prove the implication from left to right
    intro hleft,
    apply and.intro,
    {
      intro hx,
      -- since we're going in reverse, elim will *introduce* a conjunction into our goal
      apply and.elim_left,
      -- `exact` will not work here, since hleft cannot be immediately
      -- matched with the goal (hleft is universally quantified, while the goal is not)
      apply hleft
    },
    {
      intro hx,
      apply and.elim_right,
      apply hleft,
    },
  },
  { -- prove the implication from right to left
    intro hpx,
    intro hx,
    apply and.intro,
    -- Apply and-elimination to the left side of the conjunction in the
    -- hypothesis, the result of which can be matched with the goal (p hx).
    -- This is a forward step in an otherwise backward proof.
    { apply (and.elim_left hpx) },
    { apply (and.elim_right hpx) }
  },
end


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

lemma mul_zero (n : ℕ) :
  mul 0 n = 0 :=
begin
  -- not really sure of the difference between induction' and induction
  induction' n,
  { refl },
  -- Using the definition of `mul` and `add`, simp can transform the goal to
  -- `add 0 (mul 0 n) = 0`. To complete the proof, we also need the inductive
  -- hypothesis of `mul 0 n = 0`, which will allow simp to further transform
  -- the goal to `add 0 0 = 0` and then `0 = 0`.
  { simp [mul, add, ih] }
end

lemma mul_succ (m n : ℕ) :
  mul (nat.succ m) n = add (mul m n) n :=
begin
  induction' n,
  { refl },
  { simp [mul, ih, add, add_succ, add_assoc] }
end

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction'` tactic. Choose the induction variable carefully. -/

lemma mul_comm (m n : ℕ) :
  mul m n = mul n m :=
begin
  induction' n,
  { simp [mul, mul_zero] },
  { simp [mul, mul_succ, add_comm, ih], }
end

lemma mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
begin
  -- Do induction on n since mul's base case is defined as `mul _ 0 = 0`.
  induction' n,
  -- This could be just `refl`, but `simp` makes it clear that only the
  -- definition of `mul` is required for simplification.
  { simp [mul] },
  -- I initially had trouble with this because I was using mul_comm in the
  -- simp set, which it turns out transforms the goal to somethiing that
  -- simp cannot make progress on. The key insight here is that we can
  -- apply the inductive hypothesis `ih` to treat multiplication as
  -- associative, which helps complete the proof (and avoids the need to
  -- transform all `mul`s to `add`s, which I'm not sure is possible, so
  -- we can use the lemma `add_assoc`).
  { simp [mul, mul_add, ih], }
end

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

lemma add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
begin
  rw mul_comm,
  rw mul_add,
end


/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def excluded_middle :=
∀a : Prop, a ∨ ¬ a

def peirce :=
∀a b : Prop, ((a → b) → a) → a

def double_negation :=
∀a : Prop, (¬¬ a) → a

/- For the proofs below, please avoid using lemmas from Lean's `classical`
namespace, because this would defeat the purpose of the exercise.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `or.elim` and `false.elim`. You can use
`rw excluded_middle` to unfold the definition of `excluded_middle`,
and similarly for `peirce`. -/

lemma peirce_of_em :
  excluded_middle → peirce :=
begin
  rw excluded_middle,
  rw peirce,
  intros him ha hb haba,
  -- apply haba,
  apply (or.elim (him ha) _ _),
  {
    intro ha,
    exact ha,
  },
  {
    intro haf,
    apply haba,
    intro ha,
    -- im pretty sure this is basically a proof by contradiction, right?
    apply false.elim,
    apply haf,
    apply ha,
  },
end

/- 3.2 (**optional**). Prove the following implication using tactics. -/

lemma dn_of_peirce :
  peirce → double_negation :=
sorry

/- We leave the missing implication for the homework: -/

namespace sorry_lemmas

lemma em_of_dn :
  double_negation → excluded_middle :=
sorry

end sorry_lemmas

end backward_proofs

end LoVe
