
Require Import Coq.Arith.Peano_dec.
Require Import Relations.

(* Boolean grammar B
   (we're not examining it structurally, so it suffices
    to just make it any decidable type for this) *)
Definition B : Type := nat.


(* -->_r relation (single step reduction) *)
Variable r_step : relation B.

(* Since we're not looking at the details of r_step,
   we just need to assume it is irreflexive (which it is
   as defined in the text) *)
Axiom r_progress : forall a b,
    r_step a b -> a <> b.

(* Lemma 2.4 book *)
Axiom r_diamond : forall a b c,
    r_step a b ->
    r_step a c ->
    b <> c ->
    (r_step b c
     \/ r_step c b
     \/ exists d, r_step b d /\ r_step c d).


(* reflexive, transitive clojure of -->_r *)
Inductive r_star : relation B :=
| rs_nil : forall a, r_star a a
| rs_cons : forall a b c, r_step a b ->
                     r_star b c ->
                     r_star a c.
Hint Constructors r_star.

Lemma rs_trans : forall a b c,
    r_star a b ->
    r_star b c ->
    r_star a c.
Proof.
  intros a b c Hab.
  generalize dependent c.
  induction Hab; eauto.
Qed.
    
Lemma semi_confluence : forall a b c,
    r_step a b ->
    r_star a c ->
    exists d, r_star b d /\ r_star c d.
Proof.           
  intros a b c Hab Hac.
  generalize dependent b.
  (* Proof by induction on 'r_star a c' *)
  induction Hac; intros.
  - (* a, b : B
       Hab : r_step a b
       ============================
       exists d : B, r_star b d /\ r_star a d *)
    exists b; eauto.
  - (* a, b, c : B
       H : r_step a b
       Hac : r_star b c
       IHHac : forall b0 : B,
             r_step b b0 -> exists d : B, r_star b0 d /\ r_star c d
       b0 : B
       Hab : r_step a b0
       ============================
       exists d : B, r_star b0 d /\ r_star c d *)
    (* case analysis on b = b0 or b <> b0 *)
    destruct (eq_nat_dec b b0) as [Heq | Hneq]; subst.
    (* case b = b0 *)
    exists c. split; auto.
    (* case b <> b0 *)
    + (*  a, b, c : B
          H : r_step a b
          Hac : r_star b c
          IHHac : forall b0 : B,
          r_step b b0 -> exists d : B, r_star b0 d /\ r_star c d
          b0 : B
          Hab : r_step a b0
          Hneq : b <> b0
          ============================
          exists d : B, r_star b0 d /\ r_star c d *)
      (* Now we use the diamond property since 'a' steps to b and b0 *)
      destruct (r_diamond _ _ _ H Hab Hneq)
        as [Hbb0 | [Hb0b | [d [Hbd Hb0d]]]].
      apply IHHac. assumption.
      exists c; eauto.
      destruct (IHHac _ Hbd) as [e [Hde Hce]].
      exists e; eauto.
Qed.

Lemma confluence : forall a b c,
    r_star a b ->
    r_star a c ->
    exists d, r_star b d /\ r_star c d.
Proof.
  intros a b c Hab Hbc.
  generalize dependent c.
  (* Proof by induction on 'r_star a b' *)
  induction Hab; intros.
  - (* Base Case: 
       a, c : nat
       Hbc : r_star a c
       ============================
       exists d : nat, r_star a d /\ r_star c d *)
    exists c; eauto.
    - (* Inductive Case: 
         H : r_step a b
         Hab : r_star b c  
         IHHab : forall c0 : nat,
         r_star b c0 -> exists d : nat, r_star c d /\ r_star c0 d
         c0 : nat
         Hbc : r_star a c0
         ============================
         exists d : nat, r_star c d /\ r_star c0 d *)
      (* Here we use semi_confluence to show there exists an 
         e s.t. 'r_star b e' and 'r_star c0 e' *)
      destruct (semi_confluence a b c0 H Hbc) as [e [Hbe Hc0e]].
      (* We can apply the inductive hypothesis to 'r_star b e' *)
      destruct (IHHab _ Hbe) as [f [Hf1 Hf2]].
      (* So we now know there is some f s.t.  r_star c f /\ r_star e
         f, and we can use transitivity to show r_star c0 f and thus
         'f' is the final B we're looking for *)
      exists f. split; auto.
      eapply rs_trans; eauto.    
Qed.    
