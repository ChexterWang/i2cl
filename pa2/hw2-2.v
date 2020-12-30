
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
  intros a b c n Hc .
  red in Hc |- * .
  cut (a + c - (b + c) = a - b) .
  - intros H .
    rewrite H .
    + trivial .
  - auto with * .
Qed .

Lemma modulo_mult_subst : forall a b c n : Z,
    (a == b [ n ]) -> (a * c == b * c [ n ]) .
Proof .
  intros a b c n H .
  red in H |- * .
  cut (a * c - b * c = c * (a - b)) .
  - intros H1 .
    rewrite H1 .
    + auto with * .
  - auto with * .
Qed .

Hypothesis m n : Z .
Hypothesis co_prime : rel_prime m n .

Theorem modulo_inv : forall m n : Z, rel_prime m n ->
                       exists x : Z, (m * x == 1 [ n ]) .
Proof .
  intros m0 n0 H .
  cut (Bezout m0 n0 1) .
  - intros H0 .
    elim H0 .
    intros u v H1 .
    exists u .
    red .
    red .
    exists (-v) .
    rewrite (Zmult_comm m0 u).
    rewrite <- (Zminus_plus_simpl_r (u * m0) 1 (v * n0)) .
    rewrite H1 .
    unfold Zminus .
    rewrite (Zopp_plus_distr 1 (v * n0)) .
    rewrite (Zplus_comm (-(1)) (-(v*n0))) .
    rewrite (Zplus_permute 1 (-(v*n0)) (-(1))) .
    rewrite (Zplus_opp_r 1) .
    rewrite (Zplus_0_r (- (v * n0))) .
    rewrite (Zopp_mult_distr_l v n0) .
    reflexivity .
  - apply (rel_prime_bezout m0 n0) .
    exact H .
Qed.

Theorem SimpleChineseRemainder : forall a b : Z,
  exists x : Z, (x == a [ m ]) /\ (x == b [ n ]) .
Proof .
  intros a0 b0 .
  destruct (modulo_inv m n co_prime) .
  unfold rel_prime in co_prime .
  apply (Zis_gcd_sym m n 1) in co_prime .
  fold (rel_prime n m) in co_prime .
  destruct (modulo_inv n m co_prime) .
  apply (modulo_mult_subst (m * x) 1 b0 n) in H .
  apply (modulo_mult_subst (n * x0) 1 a0 m) in H0 .
  rewrite (Zmult_1_l b0) in H .
  rewrite (Zmult_1_l a0) in H0 .
  exists (m * x * b0 + n * x0 * a0) .
  split .
  - apply (modulo_plus_subst (n * x0 * a0) a0 (m * x * b0) m) in H0 .
    rewrite (Zplus_comm (n * x0 * a0) (m * x * b0)) in H0 .
    cut (a0 + m * x * b0 == a0 [m]) .
    + intro H1 .
      apply (modulo_tran (m * x * b0 + n * x0 * a0) (a0 + m * x * b0) a0 m) in H0 .
      * exact H0 .
      * exact H1 .
    + red .
      unfold Zminus .
      rewrite (Zplus_comm (a0 + m * x * b0) (- a0)) .
      rewrite (Zplus_assoc (-a0) a0 (m * x * b0)) .
      rewrite (Zplus_opp_l a0) .
      rewrite (Zplus_0_l (m * x * b0)) .
      red .
      exists (x * b0) .
      rewrite <- (Zmult_assoc m x b0) .
      rewrite (Zmult_comm m (x * b0)) .
      reflexivity .
  - apply (modulo_plus_subst (m * x * b0) b0 (n * x0 * a0) n) in H .
    cut (b0 + n * x0 * a0 == b0 [n]) .
    + intro H1 .
      apply (modulo_tran (m * x * b0 + n * x0 * a0) (b0 + n * x0 * a0) b0 n) in H .
      * exact H .
      * exact H1 .
    + red .
      unfold Zminus .
      rewrite (Zplus_comm (b0 + n * x0 * a0) (- b0)) .
      rewrite (Zplus_assoc (-b0) b0 (n * x0 * a0)) .
      rewrite (Zplus_opp_l b0) .
      rewrite (Zplus_0_l (n * x0 * a0)) .
      red .
      exists (x0 * a0) .
      rewrite <- (Zmult_assoc n x0 a0) .
      rewrite (Zmult_comm n (x0 * a0)) .
      reflexivity .
Qed .

End SimpleChineseRemainder .

Check SimpleChineseRemainder .
