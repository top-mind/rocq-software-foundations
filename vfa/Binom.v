(** * Binom: Binomial Queues *)

(** Implementation and correctness proof of fast mergeable priority queues
   using binomial queues.

  Operation [empty] is constant time,  [insert], [delete_max], and [merge]
  are logN time.  (Well, except that comparisons on [nat] take linear time.
  Read the [Extract] chapter to see what can be done about that.) *)

(* ################################################################# *)
(** * Required Reading
  Binomial Queues {https://www.cs.princeton.edu/~appel/Binom.pdf}
  by Andrew W. Appel, 2016.

  Binomial Queues {https://www.cs.princeton.edu/~appel/BQ.pdf}
  Section 9.7 of _Algorithms 3rd Edition in Java, Parts 1-4:
    Fundamentals, Data Structures, Sorting, and Searching_,
  by Robert Sedgewick.  Addison-Wesley, 2002.
*)

(* ################################################################# *)
(** * The Program *)

From Stdlib Require Import Strings.String. (* for manual grading *)
From VFA Require Import Perm.
From VFA Require Import Priqueue.

From Stdlib Require Import FunctionalExtensionality.

Module BinomQueue <: PRIQUEUE.

Definition key := nat.

Inductive tree : Type :=
|  Node: key -> tree -> tree -> tree
|  Leaf : tree.

(** A priority queue (using the binomial queues data structure) is a
   list of trees.  The [i]'th element of the list is either [Leaf] or
   it is a power-of-2-heap with exactly [2^i] nodes.

  This program will make sense to you if you've read the Sedgewick
  reading; otherwise it is rather mysterious.
*)

Definition priqueue := list tree.

Definition empty : priqueue := nil.

Definition smash (t u:  tree) : tree :=
  match t , u with
  |  Node x t1 Leaf, Node y u1 Leaf =>
                   if  x >? y then Node x (Node y u1 t1) Leaf
                                else Node y (Node x t1 u1) Leaf
  | _ , _ => Leaf  (* arbitrary bogus tree *)
  end.

Fixpoint carry (q: list tree) (t: tree) : list tree :=
  match q, t with
  | nil, Leaf        => nil
  | nil, _            => t :: nil
  | Leaf :: q', _  => t :: q'
  | u :: q', Leaf  => u :: q'
  | u :: q', _       => Leaf :: carry q' (smash t u)
 end.

Definition insert (x: key) (q: priqueue) : priqueue :=
     carry q (Node x Leaf Leaf).

Eval compute in fold_left (fun x q =>insert q x) [3;1;4;1;5;9;2;3;5] empty.
(**
    = [Node 5 Leaf Leaf;
       Leaf;
       Leaf;
       Node 9
          (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
             (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf)))
          Leaf]
     : priqueue
*)

Fixpoint join (p q: priqueue) (c: tree) : priqueue :=
  match p, q, c with
    [], _ , _            => carry q c
  | _, [], _             => carry p c
  | Leaf::p', Leaf::q', _              => c :: join p' q' Leaf
  | Leaf::p', q1::q', Leaf            => q1 :: join p' q' Leaf
  | Leaf::p', q1::q', Node _ _ _  => Leaf :: join p' q' (smash c q1)
  | p1::p', Leaf::q', Leaf            => p1 :: join p' q' Leaf
  | p1::p', Leaf::q',Node _ _ _   => Leaf :: join p' q' (smash c p1)
  | p1::p', q1::q', _                   => c :: join p' q' (smash p1 q1)
 end.

Fixpoint unzip (t: tree) (cont: priqueue -> priqueue) : priqueue :=
  match t with
  |  Node x t1 t2   => unzip t2 (fun q => Node x t1 Leaf  :: cont q)
  | Leaf => cont nil
  end.

Definition heap_delete_max (t: tree) : priqueue :=
  match t with
    Node x t1 Leaf  => unzip t1 (fun u => u)
  | _ => nil   (* bogus value for ill-formed or empty trees *)
  end.

Fixpoint find_max' (current: key) (q: priqueue) : key :=
  match q with
  |  []         => current
  | Leaf::q' => find_max' current q'
  | Node x _ _ :: q' => find_max' (if x >? current then x else current) q'
  end.

Fixpoint find_max (q: priqueue) : option key :=
  match q with
  | [] => None
  | Leaf::q' => find_max q'
  | Node x _ _ :: q' => Some (find_max' x q')
 end.

Fixpoint delete_max_aux (m: key) (p: priqueue) : priqueue * priqueue :=
  match p with
  | Leaf :: p'   => let (j,k) := delete_max_aux m p'  in (Leaf::j, k)
  | Node x t1 Leaf :: p' =>
       if m >? x
       then (let (j,k) := delete_max_aux m p'
             in (Node x t1 Leaf::j,k))
       else (Leaf::p', heap_delete_max (Node x t1 Leaf))
  | _ => (nil, nil) (* Bogus value *)
  end.

Definition delete_max (q: priqueue) : option (key * priqueue) :=
  match find_max q with
  | None => None
  | Some  m => let (p',q') := delete_max_aux m q
                            in Some (m, join p' q' Leaf)
  end.

Definition merge (p q: priqueue) := join p q Leaf.

(* ################################################################# *)
(** * Characterization Predicates *)

(** [t] is a complete binary tree of depth [n], with every key <= [m] *)

Fixpoint pow2heap' (n: nat) (m: key) (t: tree) :=
 match n, m, t with
    0, m, Leaf       => True
  | 0, m, Node _ _ _  => False
  | S _, m,Leaf    => False
  | S n', m, Node k l r  =>
       m >= k /\ pow2heap' n' k l /\ pow2heap' n' m r
 end.

(** [t] is a power-of-2 heap of depth [n] *)

Definition pow2heap (n: nat) (t: tree) :=
  match t with
    Node m t1 Leaf => pow2heap' n m t1
  | _ => False
  end.

(** [l] is the [i]th tail of a binomial heap *)

Fixpoint priq'  (i: nat) (l: list tree) : Prop :=
   match l with
  | t :: l' => (t=Leaf \/ pow2heap i t) /\ priq' (S i) l'
  | nil => True
 end.

(** [q] is a binomial heap *)

Definition priq (q: priqueue) : Prop := priq' 0 q.

(* priq has no restrictions on the length of q with same contents
   this is a problem when prove the algorithm efficiency:
   it is imposible to prove theorems like a well formed binom queue has length
   O(log_2 n) *)
Example x_priq_leading_leaf : forall n q, priq' n q -> priq' n (q ++ [Leaf]).
Proof.
  intros.
  generalize dependent n.
  induction q; intros; simpl.
  - auto.
  - simpl in H. destruct H as [? ?].
    auto.
Qed.

(* ################################################################# *)
(** * Proof of Algorithm Correctness *)

(* ================================================================= *)
(** ** Various Functions Preserve the Representation Invariant *)

(** ...that is, the [priq] property, or the closely related property [pow2heap].
*)

(** **** Exercise: 1 star, standard (empty_priq)  *)
Theorem empty_priq: priq empty.
Proof.
  unfold priq.
  simpl. auto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (smash_valid) *)
Theorem smash_valid:
       forall n t u, pow2heap n t -> pow2heap n u -> pow2heap (S n) (smash t u).
Proof.
  intros.
  unfold smash.
  destruct t; [| inv H].
  destruct t2; auto.
  destruct u; [| inv H0].
  destruct u2; auto.
  simpl in *.
  bdestruct (k >? k0); simpl; split; auto; lia.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (carry_valid) *)
Theorem carry_valid:
           forall n q,  priq' n q ->
           forall t, (t=Leaf \/ pow2heap n t) -> priq' n (carry q t).
Proof.
  intros n q.
  generalize dependent n.
  induction q; intros.
  - simpl. destruct t.
    + unfold priq'. auto.
    + auto.
  - simpl. destruct a.
    + destruct t; auto.
      destruct H0; [inv H0|].
      split; auto.
      destruct H. destruct H; [inv H|].
      apply IHq; [exact H1|].
      right.
      apply smash_valid; auto.
    + simpl. split; auto. simpl in H. destruct H as [_ H]. auto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (insert_valid) *)
Theorem insert_priq: forall x q, priq q -> priq (insert x q).
Proof.
  unfold priq.
  intros.
  apply carry_valid; auto.
  right. simpl. constructor.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (join_valid) *)
(* This proof is rather long, but each step is reasonably straightforward.
    There's just one [induction] to do, right at the beginning. *)
Theorem join_valid: forall p q c n, priq' n p -> priq' n q -> (c=Leaf \/ pow2heap n c) -> priq' n (join p q c).
Proof.
  induction p; intros.
  - simpl. apply carry_valid; auto.
  - simpl. destruct H.
    destruct a, q.
    + destruct c.
      * split; auto. apply carry_valid; auto. right.
        destruct H; [inv H|].
        destruct H1; [inv H1|].
        apply smash_valid; auto.
      * split; auto.
    + destruct t; destruct H0.
      * split; auto. apply IHp; auto. right.
        destruct H; [inv H|].
        destruct H0; [inv H0|].
        apply smash_valid; auto.
      * destruct c; split; auto.
        destruct H; [inv H|].
        destruct H1; [inv H1|].
        apply IHp; auto. right.
        apply smash_valid; auto.
    + simpl. split; auto.
    + destruct t; destruct H0.
      * destruct c; split; auto.
        destruct H0; [inv H0|]. destruct H1; [inv H1|].
        apply IHp; auto. right.
        apply smash_valid; auto.
      * split; auto.
Qed.

(** [] *)

Theorem merge_priq:  forall p q, priq p -> priq q -> priq (merge p q).
Proof.
 intros. unfold merge. apply join_valid; auto.
Qed.

(** **** Exercise: 5 stars, standard, optional (delete_max_Some_priq) *)
(* We restate unzip in a slower but prove-friendly way *)
Fixpoint unzip'_select n t :=
  match (n, t) with
  | (_, Leaf) => Leaf
  | (O, Node k t1 t2) => Node k t1 Leaf
  | (S n', Node k t1 t2) => unzip'_select n' t2
  end.

Fixpoint unzip' n t :=
  match n with
  | O => [unzip'_select 0 t]
  | S n' => unzip'_select n t :: unzip' n' t
  end.

Eval compute in unzip (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
             (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf))) (fun _ => nil).


Eval compute in unzip' 2 (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
             (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf))).

Theorem unzip'_select_heap : forall t n1 n2 k,
  pow2heap' (1 + n1 + n2) k t -> pow2heap n1 (unzip'_select n2 t).
Proof.
  intros. generalize dependent t. generalize dependent n1.
  induction n2; intros; simpl; destruct t; simpl in H; auto.
  - destruct H as [_ [? _]].
    rewrite plus_n_O with n1. auto.
  - apply IHn2. destruct H as [_ [_ ?]].
    replace (1 + n1 + n2) with (n1 + S n2) by lia. auto.
Qed.

Theorem unzip'_priq : forall t n1 n2 k,
  pow2heap' (1 + n1 + n2) k t -> priq' n1 (unzip' n2 t).
Proof.
  intros.
  generalize dependent t.
  generalize dependent n1.
  induction n2; intros.
  - destruct t.
    + simpl. split; auto.
      right. simpl in H. destruct H as [_ [? _]].
      rewrite plus_n_O with n1. auto.
    + simpl. auto.
  - simpl; split.
    + destruct t; auto.
      right. apply unzip'_select_heap with k.
      simpl in H. destruct H as [_ [_ ?]].
      replace (1 + n1 + n2) with (n1 + S n2) by lia. auto.
    + apply IHn2. replace (1 + S n1 + n2) with (1 + n1 + S n2) by lia.
      auto.
Qed.

(* The correctness of unzip' *)
Theorem unzip'_tail : forall n k t1 t2,
  unzip' (S n) (Node k t1 t2) = unzip' n t2 ++ [Node k t1 Leaf].
Proof.
  induction n; intros.
  - simpl. auto.
  - simpl. rewrite <-IHn.
    simpl. auto.
Qed.

Theorem unzip'_relate : forall t n k cont,
  pow2heap' (S n) k t -> unzip t cont = unzip' n t ++ cont [].
Proof.
  induction t; intros.
  - destruct H as [? [? ?]].
    simpl. destruct n.
    + simpl in H1. destruct t2; inv H1.
      simpl. auto.
    + simpl. rewrite (IHt2 _ _ _ H1).
      replace (unzip' n t2 ++ Node k t1 Leaf :: cont []) with
              ((unzip' n t2 ++ [Node k t1 Leaf]) ++ cont [])
        by (simpl; rewrite <-app_assoc; auto).
      rewrite <-unzip'_tail. simpl. auto.
  - simpl in H. destruct H.
Qed.

Theorem heap_delete_max_priq : forall t n,
  pow2heap n t ->
  priq' 0 (heap_delete_max t).
Proof.
  intros.
  destruct t; [|inv H].
  simpl in *.
  destruct t2; [inv H|].
  destruct n.
  * simpl in H. destruct t1; inv H.
    simpl. auto.
  * rewrite (unzip'_relate _ _ _ _ H).
    rewrite app_nil_r.
    apply unzip'_priq with k. auto.
Qed.

Theorem delete_max_aux_priq : forall p p0 p1 n k,
  priq' n p ->
  delete_max_aux k p = (p0, p1) ->
  priq' n p0 /\ priq' 0 p1.
Proof.
  induction p; simpl; intros.
  - inv H0. subst. auto.
  - destruct a.
    + destruct a2.
      * inv H0. subst. split; simpl; auto.
      * destruct H. destruct H; [inv H|].
        destruct (k >? k0).
        -- destruct (delete_max_aux k p) eqn:E.
           inv H0.
           destruct (IHp _ _ _ _ H1 E).
           repeat split; auto.
        -- inv H0. split.
           ++ split; auto.
           ++ exact (heap_delete_max_priq _ _ H).
    + destruct (delete_max_aux k p) eqn:E.
      destruct H.
      inv H0. destruct (IHp _ _ _ _ H1 E).
      repeat split; auto.
Qed.

Theorem delete_max_Some_priq:
      forall p q k, priq p -> delete_max p = Some(k,q) -> priq q.
Proof.
  intros.
  unfold delete_max in H0.
  destruct (find_max p); inv H0.
  destruct (delete_max_aux k0 p) eqn:?H. inv H2.
  destruct (delete_max_aux_priq _ _ _ _ _ H H0).
  apply join_valid; auto.
Qed.
  
(** [] *)

(* ================================================================= *)
(** ** The Abstraction Relation *)

(** [tree_elems t l]    means that the keys in t are the same as the
   elements of l (with repetition) *)

Inductive tree_elems: tree -> list key -> Prop :=
| tree_elems_leaf: tree_elems Leaf nil
| tree_elems_node:  forall bl br v tl tr b,
           tree_elems tl bl ->
           tree_elems tr br ->
           Permutation b (v::bl++br) ->
           tree_elems (Node v tl tr) b.

(** **** Exercise: 3 stars, standard (priqueue_elems)

    Make an inductive definition, similar to [tree_elems], to relate
  a priority queue  "l"  to a list of all its elements.

  As you can see in the definition of [tree_elems],  a [tree] relates to
  _any_ permutation of its keys, not just a single permutation.
  You should make your [priqueue_elems] relation behave similarly,
  using (basically) the same technique as in [tree_elems].
*)

Inductive priqueue_elems: list tree -> list key -> Prop :=
| priqueue_elems_nil: priqueue_elems [] []
| priqueue_elems_app: forall t l bh bt b,
    tree_elems t bh ->
    priqueue_elems l bt ->
    Permutation b (bh ++ bt) ->
    priqueue_elems (t :: l) b.
(* Do not modify the following line: *)
Definition manual_grade_for_priqueue_elems : option (nat*string) := None.
(** [] *)

Definition Abs (p: priqueue) (al: list key) := priqueue_elems p al.

(* ================================================================= *)
(** ** Sanity Checks on the Abstraction Relation *)

(** **** Exercise: 2 stars, standard (tree_elems_ext)

    Extensionality theorem for the tree_elems relation *)

Theorem tree_elems_ext: forall t e1 e2,
  Permutation e1 e2 -> tree_elems t e1 -> tree_elems t e2.
Proof.
  intros. destruct H0.
  - apply Permutation_nil in H. subst. constructor.
  - econstructor; [exact H0_|exact H0_0|].
    eapply perm_trans.
    + apply Permutation_sym. exact H.
    + exact H0.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (tree_perm) *)
Theorem tree_perm: forall t e1 e2,
  tree_elems t e1 -> tree_elems t e2 -> Permutation e1 e2.
Proof.
  intros.
  generalize dependent e2.
  induction H; intros.
  - inv H0. auto.
  - inv H2.
    pose proof (IHtree_elems1 _ H6).
    pose proof (IHtree_elems2 _ H8).
    eapply perm_trans.
    + exact H1.
    + apply Permutation_sym in H9. eapply perm_trans; [|apply H9].
      apply perm_skip. apply Permutation_app; auto.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (priqueue_elems_ext)

    To prove [priqueue_elems_ext], you should almost be able to cut-and-paste the
   proof of [tree_elems_ext], with just a few edits.  *)

Theorem priqueue_elems_ext: forall q e1 e2,
  Permutation e1 e2 -> priqueue_elems q e1 -> priqueue_elems q e2.
Proof.
  intros. destruct H0.
  - apply Permutation_nil in H. subst. constructor.
  - econstructor; [exact H0 | exact H1 |].
    eapply perm_trans. { apply Permutation_sym. exact H. }
    exact H2.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (abs_perm) *)
Theorem abs_perm_general: forall p al bl,
   Abs p al -> Abs p bl -> Permutation al bl.
Proof.
  induction p; intros.
  - inv H. inv H0. auto.
  - inv H. inv H0.
    pose proof (tree_perm _ _ _ H3 H2).
    pose proof (IHp _ _ H4 H5).
    eapply perm_trans. exact H6.
    eapply perm_trans. apply Permutation_app; eassumption.
    apply Permutation_sym. auto.
Qed.

Theorem abs_perm: forall p al bl,
   priq p -> Abs p al -> Abs p bl -> Permutation al bl.
Proof. intros. eauto using abs_perm_general. Qed.

(** **** Exercise: 2 stars, standard (can_relate) *)
Lemma tree_can_relate: forall t, exists al, tree_elems t al.
Proof.
  induction t.
  - destruct IHt1, IHt2.
    exists (k :: x ++ x0).
    econstructor; eauto.
  - exists []. constructor.
Qed.

Theorem can_relate:  forall p, priq p -> exists al, Abs p al.
Proof.
  intros. clear H. induction p.
  - exists []. constructor.
  - destruct IHp. destruct (tree_can_relate a).
    exists (x0 ++ x). econstructor; eauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Various Functions Preserve the Abstraction Relation *)
(** **** Exercise: 1 star, standard (empty_relate) *)
Theorem empty_relate:  Abs empty nil.
Proof.
  constructor.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (smash_elems)

     Warning:  This proof is rather long. *)

Theorem smash_elems: forall n t u bt bu,
                     pow2heap n t -> pow2heap n u ->
                     tree_elems t bt -> tree_elems u bu ->
                     tree_elems (smash t u) (bt ++ bu).
Proof.
  intros.
  destruct t; [|inv H].
  destruct u; [|inv H0].
  simpl in *.
  destruct t2; [inv H|]. clear H.
  destruct u2; [inv H0|]. clear H0.
  inv H1. inv H6. rewrite app_nil_r in H7.
  inv H2. inv H6. rewrite app_nil_r in H8.
  rename k into a. rename k0 into b.
  rename bl into l1. rename bl0 into l2.
  bdestruct (a >? b); econstructor; try econstructor; eauto; try constructor;
    rewrite app_nil_r; eapply perm_trans;
    try apply Permutation_app; try apply H7; try apply H8; simpl.
  - (* Permutation (a :: l1 ++ b :: l2) (a :: b :: l2 ++ l1) *)
    apply perm_skip.
    apply Permutation_app_comm.
  - (* Permutation (a :: l1 ++ b :: l2) (b :: a :: l1 ++ l2) *)
    eapply perm_trans; [|apply perm_swap].
    apply perm_skip.
    eapply perm_trans; [apply Permutation_app_comm|].
    simpl. apply perm_skip. apply Permutation_app_comm.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Optional Exercises *)

(**  Some of these proofs are quite long, but they're not especially tricky. *)

(** **** Exercise: 4 stars, standard, optional (carry_elems) *)
Theorem carry_elems:
      forall n q,  priq' n q ->
      forall t, (t=Leaf \/ pow2heap n t) ->
      forall eq et, priqueue_elems q eq ->
                          tree_elems t et ->
                          priqueue_elems (carry q t) (eq++et).
Proof.
  intros n q. revert n.
  induction q; intros.
  - inv H1. simpl. destruct t.
    + econstructor; eauto; try econstructor.
      * apply Permutation_refl. * rewrite app_nil_r. apply Permutation_refl.
    + inv H2. constructor.
  - simpl.
    inv H1.
    destruct a.
    + destruct t.
      * destruct H0; [inv H0|].
        destruct H. destruct H; [inv H|].
        econstructor; [constructor | eauto using smash_valid, smash_elems | simpl].
        eapply perm_trans.
        -- apply Permutation_app_tail. exact H8.
        -- rewrite <-app_assoc. apply Permutation_app_rot.
      * inv H2. rewrite app_nil_r. econstructor; eassumption.
    + inv H5. simpl in H8.
      econstructor; try eassumption.
      eapply perm_trans. apply Permutation_app_comm.
      apply Permutation_app_head. auto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (insert_elems) *)
Theorem insert_relate:
        forall p al k, priq p -> Abs p al -> Abs (insert k p) (k::al).
Proof.
  intros.
  eapply priqueue_elems_ext.
  - apply Permutation_sym.
    apply Permutation_cons_append.
  - eapply carry_elems; eauto.
    + right. constructor.
    + econstructor; constructor. auto.
Qed.
(** [] *)

Lemma Permutation_13_24 : forall pa pb p1 p2 p3 p4 : list key,
  Permutation pa (p1 ++ p2) ->
  Permutation pb (p3 ++ p4) ->
  Permutation (pa ++ pb) (p1 ++ p3 ++ p2 ++ p4).
Proof.
  intros.
  eapply perm_trans. apply Permutation_app; eassumption.
  repeat rewrite <-app_assoc.
  apply Permutation_app_head.
  apply Permutation_app_swap_app.
Qed.

(** **** Exercise: 4 stars, standard, optional (join_elems) *)
Theorem join_elems:
                forall p q c n,
                      priq' n p ->
                      priq' n q ->
                      (c=Leaf \/ pow2heap n c) ->
                  forall pe qe ce,
                             priqueue_elems p pe ->
                             priqueue_elems q qe ->
                             tree_elems c ce ->
                              priqueue_elems (join p q c) (ce++pe++qe).
Proof.
  induction p; intros.
  - simpl. inv H2. simpl.
    eapply priqueue_elems_ext. apply Permutation_app_comm.
    eapply carry_elems; eauto.
  - inv H2. simpl. destruct a, q.
    3: { inv H3. rewrite app_nil_r. inv H7. simpl in H10.
      econstructor; eauto. apply Permutation_app_head. auto. }
    + destruct H. destruct H; [inv H|]. inv H3. rewrite app_nil_r.
      destruct c.
      * destruct H1; [inv H1|].
        econstructor. constructor.
        eapply carry_elems; eauto using smash_valid, smash_elems.
        simpl. eapply perm_trans. apply Permutation_app_head. exact H10.
        rewrite app_assoc. apply Permutation_app_comm.
      * inv H4. econstructor; eauto.
    + inv H. destruct H2; [inv H|].
      inv H3.
      destruct t.
      * inv H0. destruct H2; [inv H0|].
        econstructor. exact H4.
        eapply IHp; eauto using smash_valid, smash_elems.
        apply Permutation_app_head. rewrite <-app_assoc.
        apply Permutation_13_24; auto.
      * inv H0. destruct c.
        -- destruct H1; [inv H0|].
           econstructor. constructor.
           eapply IHp; eauto using smash_valid, smash_elems. simpl.
           rewrite <-app_assoc. apply Permutation_app_head.
           inv H9. simpl in H13.
           rewrite app_assoc. apply Permutation_app; auto.
        -- inv H4. econstructor. eauto.
           eapply IHp; eauto using smash_valid, smash_elems. simpl.
           apply Permutation_13_24; auto.
    + inv H. inv H0. inv H3.
      destruct t.
      * inv H; [inv H0|].
        destruct c.
        -- inv H1; [inv H|].
           econstructor. constructor.
           eapply IHp; eauto using smash_valid, smash_elems.
           simpl. rewrite <-app_assoc. apply Permutation_app_head. inv H7. simpl in H10.
           eapply perm_trans. apply Permutation_app; eassumption. apply Permutation_app_swap_app.
        -- inv H7. simpl in H10. econstructor. eassumption.
           eapply IHp; eauto using smash_valid, smash_elems.
           eapply perm_trans; [| apply Permutation_app_swap_app].
           apply Permutation_app_head. eapply perm_trans; [| apply Permutation_app_swap_app].
           apply Permutation_app; auto.
      * inv H11. simpl in H14. econstructor. eassumption.
        eapply IHp; eauto using smash_valid, smash_elems.
        apply Permutation_app_head. rewrite app_assoc. apply Permutation_app; auto.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (merge_relate) *)
Theorem merge_relate:
    forall p q pl ql al,
       priq p -> priq q ->
       Abs p pl -> Abs q ql -> Abs (merge p q) al ->
       Permutation al (pl++ql).
Proof.
  intros.
  eapply abs_perm.
  2 : exact H3.
  - apply merge_priq; auto.
  - replace (pl ++ ql) with ([] ++ pl ++ ql) by auto.
    eapply join_elems; eauto. constructor.
Qed.
(** [] *)

Theorem find_max_None_relate : forall p,
  Abs p nil <-> find_max p = None.
Proof.
  intros.
  induction p. { split; auto. constructor. }
  split; intros.
  - inv H. apply Permutation_nil in H5. destruct (app_eq_nil _ _ H5). subst.
    intuition. simpl.
    destruct a; auto.
    inv H2. destruct (Permutation_nil_cons H10).
  - inv H. destruct a; inv H1.
    intuition.
    econstructor. constructor. eassumption. auto.
Qed.

(** **** Exercise: 5 stars, standard, optional (delete_max_None_relate) *)
Theorem delete_max_None_relate:
        forall p, priq p -> (Abs p nil <-> delete_max p = None).
Proof.
  intros. destruct (find_max_None_relate p).
  split; intros; intuition.
  - unfold delete_max. rewrite H3; auto.
  - apply H1. unfold delete_max in H2. destruct (find_max p); auto.
    destruct (delete_max_aux k p). inv H2.
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (delete_max_Some_relate) *)
Theorem tree_ge : forall k l r n tl,
  pow2heap n (Node k l r) ->
  tree_elems (Node k l r) tl ->
  Forall (ge k) tl.
Proof.
  intros.
  simpl in H. destruct r. inv H.
  inv H0. inv H6. rewrite app_nil_r in H7.
  eapply Forall_perm. apply Permutation_sym. exact H7. clear H7. clear tl.
  constructor; auto.
  revert H H4. revert k n bl.
  induction l; intros.
  - destruct n; simpl in H. inv H.
    destruct H as [? [? ?]].
    inv H4. eapply Forall_perm. apply Permutation_sym. apply H9.
    constructor; auto.
    apply Forall_app. split; eauto.
    apply Forall_impl with (ge k); eauto. lia.
  - inv H4. auto.
Qed.

Theorem find_max'_ge : forall p k,
  find_max' k p >= k.
Proof.
  induction p; intros.
  - simpl. auto.
  - simpl. destruct a.
    + bdestruct (k0 >? k).
      * specialize IHp with k0. lia.
      * specialize IHp with k. lia.
    + specialize IHp with k. lia.
Qed.    

Theorem priqueue_elems_ge : forall p pl n k0 k,
  priq' n p ->
  find_max' k0 p = k ->
  priqueue_elems p pl ->
  Forall (ge k) pl.
Proof.
  induction p; intros.
  - inv H1. auto.
  - inv H. inv H1.
    destruct a.
    + destruct H2. inv H.
      simpl. remember (if k >? k0 then k else k0) as kmax.
      remember (find_max' kmax p) as k1. symmetry in Heqk1.
      eapply Forall_perm. apply Permutation_sym, H7.
      apply Forall_app. split; eauto.
      pose proof (find_max'_ge p kmax).
      eapply Forall_impl with (ge k). {
        intros. bdestruct (k >? k0); lia.
      }
      eapply tree_ge; eauto.
    + inv H4. simpl in H7.
      simpl. eapply IHp; eauto.
      eapply priqueue_elems_ext. apply Permutation_sym. eauto. auto.
Qed.

Theorem unzip_cont_perm : forall t tl pl cont cl,
  tree_elems t tl ->
  Abs (cont nil) cl ->
  Abs (unzip t cont) pl ->
  Permutation (tl ++ cl) pl.
Proof.
  induction t; intros.
  - simpl in H1.
    inv H.
    epose proof (IHt2 _ _ _ (k :: bl ++ cl) H7 _ H1).
    eapply perm_trans; [| apply H].
    eapply perm_trans. apply Permutation_app_tail. apply H8.
    rewrite app_comm_cons.
    rewrite <-app_assoc. apply Permutation_app_swap_app.
    Unshelve.
    simpl. econstructor; eauto.
    econstructor. exact H5. constructor. rewrite app_nil_r.
    all: eauto.
  - simpl in H1. inv H. simpl. eapply abs_perm_general; eauto.
Qed.

Theorem unzip_perm : forall t tl pl,
  tree_elems t tl ->
  Abs (unzip t (fun u => u)) pl ->
  Permutation tl pl.
Proof.
  intros. replace (tl) with (tl ++ []) by apply app_nil_r.
  eapply unzip_cont_perm; try eassumption.
  simpl. constructor.
Qed.

Lemma find_max'_shadow : forall p k k0 k1,
  find_max' k0 p = k ->
  k > k0 ->
  k0 >= k1 ->
  find_max' k1 p = k.
Proof.
  induction p; intros.
  - simpl in H. try lia.
  - simpl in *. destruct a.
    + bdestruct (k2 >? k1); bdestruct (k2 >? k0); try lia;
      apply IHp with k0; auto.
    + eapply IHp; eauto.
Qed.

Theorem find_max_some : forall p k k0,
  find_max' k0 p = k ->
  k > k0 ->
  find_max p = Some k.
Proof.
  induction p; intros.
  - simpl in H. lia.
  - simpl in *. destruct a.
    + f_equal. bdestruct (k1 >? k0); auto.
      eapply find_max'_shadow; eauto.
    + eauto.
Qed.

Theorem delete_max_aux_relate : forall p q r pl ql rl k n,
  priq' n p ->
  Abs p pl ->
  find_max p = Some k ->
  delete_max_aux k p = (q, r) ->
  Abs q ql ->
  Abs r rl ->
  Permutation pl (k :: ql ++ rl) /\ Forall (ge k) pl. (* save your life *)
Proof.
  induction p; intros; simpl in *. { inv H1. }
  destruct H. destruct a.
  - destruct H. inv H.
    destruct a2. simpl in H. inv H.
    bdestruct (k >? k0).
    + injection H1 as H1.
      pose proof (find_max_some _ _ _ H1 H6). 
      destruct (delete_max_aux k p) eqn:E.
      injection H2 as ?. subst q r.
      inversion H0. clear H0. subst t l b.
      pose proof (tree_ge _ _ _ _ _ H H9) as Hbh.
      inversion H3. clear H3. subst t l b.
      destruct (IHp _ _ _ _ _ _ _ H5 H10 H7 E H11 H4).
      clear H1. inv H9. inv H17. rewrite app_nil_r in H18.
      inv H8. inv H17. rewrite app_nil_r in H19.
      pose proof (tree_perm _ _ _ H13 H15).
      split.
      * (* boring permutation proof *)
        clear -H14 H19 H12 H18 H0 H1.
        eapply perm_trans. exact H12.
        eapply perm_trans. apply Permutation_app. exact H18.
          exact H0.
        rewrite app_comm_cons.
        eapply perm_trans. apply Permutation_app_swap_app .
        simpl. apply perm_skip.
        rewrite app_comm_cons. rewrite app_assoc. apply Permutation_app_tail.
        eapply perm_trans. 2: apply Permutation_sym; exact H14.
        eapply perm_trans. apply Permutation_app_comm. apply Permutation_app_tail.
        apply Permutation_sym. eapply perm_trans. exact H19. apply perm_skip. auto.
      * eapply Forall_perm. apply Permutation_sym. exact H12.
        apply Forall_app. split; auto.
        apply Forall_impl with (ge k0). lia. auto.
    + inv H2. inv H3. inv H8. simpl in H11. inv H0.
      pose proof (tree_ge _ _ _ _ _ H H7).
      inv H7. inv H15. rewrite app_nil_r in H16.
      Check unzip_perm.
      pose proof (unzip_perm _ _ _ H13 H4).
      injection H1 as H1.
      Check priqueue_elems_ge.
      pose proof (priqueue_elems_ge _ _ _ _ _ H5 H1 H8).
      Check find_max'_ge. pose proof (find_max'_ge p k0).
      rewrite H1 in H7. clear H1. assert (k0 = k) by lia. subst k0.
      Check abs_perm_general.
      pose proof (abs_perm_general _ _ _ H8 H9).
      split.
      * clear -H2 H11 H12 H16 H1.
        eapply perm_trans. apply H12. eapply perm_trans.
          apply Permutation_app; eassumption.
        simpl. apply perm_skip. eapply perm_trans. apply Permutation_app_tail. apply H2.
        eapply perm_trans. apply Permutation_app_comm. apply Permutation_app_tail.
        apply Permutation_sym. auto.
      * eapply Forall_perm. apply Permutation_sym. apply H12.
        apply Forall_app. split; auto.
  - destruct (delete_max_aux k p) eqn:E.
    inv H2. inv H3. inv H7. simpl in H10.
    inv H0. inv H6. simpl in H11.
    apply Permutation_sym in H11.
    pose proof (priqueue_elems_ext _ _ _ H11 H7).
    destruct (IHp _ _ _ _ _ _ _ H5 H0 H1 E H8 H4).
    split; auto.
    eapply perm_trans. exact H2. apply perm_skip. apply Permutation_app_tail.
    apply Permutation_sym. auto.
Qed.

Theorem delete_max_Some_relate:
  forall (p q: priqueue) k (pl ql: list key), priq p ->
   Abs p pl ->
   delete_max p = Some (k,q) ->
   Abs q ql ->
   Permutation pl (k::ql) /\ Forall (ge k) ql.
Proof.
  intros.
  unfold delete_max in H1.
  destruct (find_max p) eqn:E; [| inv H1].
  destruct (delete_max_aux k0 p) eqn:?E.
  inv H1.
  Check delete_max_aux_priq.
  destruct (delete_max_aux_priq _ _ _ _ _ H E0).
  destruct (can_relate _ H1).
  destruct (can_relate _ H3).
  Check join_elems.
  epose proof (join_elems _ _ Leaf _ H1 H3 _ _ _ nil H4 H5 _).
  Unshelve. 2: auto. 2: constructor.
  simpl in H6.
  Check delete_max_aux_relate.
  destruct (delete_max_aux_relate _ _ _ _ _ _ _ _ H H0 E E0 H4 H5).
  Check abs_perm_general.
  pose proof (abs_perm_general _ _ _ H2 H6).
  apply Permutation_sym in H9.
  split.
  - eapply perm_trans. exact H7. apply perm_skip. auto.
  - eapply Forall_perm in H8. 2: apply H7.
    inv H8.
    eapply Forall_perm. apply H9. auto.
Qed.

(** [] *)

(** With the following line, we're done!  We have demonstrated that
  Binomial Queues are a correct implementation of mergeable
  priority queues.  That is, we have exhibited a [Module BinomQueue]
  that satisfies the [Module Type PRIQUEUE]. *)

End BinomQueue.

(* ################################################################# *)
(** * Measurement. *)

(** **** Exercise: 5 stars, standard, optional (binom_measurement)

    Adapt the program (but not necessarily the proof) to use Ocaml integers
  as keys, in the style shown in [Extract].   Write an ML program to
  exercise it with random inputs.  Compare the runtime to the implementation
  from [Priqueue], also adapted for Ocaml integers.
*)
(** [] *)

(* 2025-08-24 13:54 *)
