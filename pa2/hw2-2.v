
Require Import Znumtheory .
Require Import Zdiv .
Require Import ZArith .

Section SimpleChineseRemainder .

Open Scope Z_scope .

Definition modulo (a b n : Z) : Prop := (n | (a - b)) .
Notation "( a == b [ n ])" := (modulo a b n) .

Lemma modulo_tran : forall a b c n : Z, 
    (a == b [ n ]) -> (b == c [ n ]) -> (a == c [ n ]) .
Proof .
  intros a b c n Hab Hbc .
  red in Hab, Hbc |- * .
  cut (a - c = a - b + (b - c)) .
  - intros H .
    rewrite H .
    apply Zdivide_plus_r .
    + trivial .
    + trivial .
  - auto with * .
Qed .

Lemma modulo_plus_subst : forall a b c n : Z,
    (a == b [ n ]) -> (a + c == b + c [ n ]) .
Proof .
(* to be done *)
Abort .

Lemma modulo_mult_subst : forall a b c n : Z,
    (a == b [ n ]) -> (a * c == b * c [ n ]) .
Proof .
(* to be done *)
Abort .

Hypothesis m n : Z .
Hypothesis co_prime : rel_prime m n .

Theorem modulo_inv : forall m n : Z, rel_prime m n ->
                       exists x : Z, (m * x == 1 [ n ]) .
Proof .
(* to be done *)
Abort .

Theorem SimpleChineseRemainder : forall a b : Z,
  exists x : Z, (x == a [ m ]) /\ (x == b [ n ]) .
Proof .
(* to be done *)
Abort .

End SimpleChineseRemainder .

Check SimpleChineseRemainder .
