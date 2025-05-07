Require Import String Arith List Lia ZArith.
Import ListNotations.
Require Import FSetFacts.
Require Import FMapInterface.
Require Import FSets.
Require Import FMapFacts.

(* m = num resources, n = num users *)
Definition vector := list nat.
Definition matrix := list (vector).

(* -------------------- COMPARATORS -------------------- *)
Fixpoint list_add (l1 l2 : list nat) : list nat :=
match l1, l2 with
| [], [] => []  
| x1 :: xs1, x2 :: xs2 => (x1 + x2) :: (list_add xs1 xs2) 
| _, _ => []
end.

Fixpoint list_leq (l1 l2 : list nat) : bool :=
match l1, l2 with
| [], [] => true 
| x1 :: xs1, x2 :: xs2 => (x1 <=? x2) && list_leq xs1 xs2 
| _, _ => false 
end.

Fixpoint list_gt (l1 l2 : list nat) : bool :=
match l1, l2 with
| [], [] => true 
| x1 :: xs1, x2 :: xs2 => (x2 <? x1) && list_gt xs1 xs2 
| _, _ => false  
end.

Fixpoint list_eq (l1 l2 : list nat) : bool :=
match l1, l2 with
| [], [] => true 
| x1 :: xs1, x2 :: xs2 => (x1 =? x2) && list_eq xs1 xs2 
| _, _ => false  
end.

Fixpoint matrix_eq (m1 m2 : matrix) : bool :=
match m1, m2 with
| [], [] => true
| r1 :: rs1, r2 :: rs2 => (list_eq r1 r2) && matrix_eq rs1 rs2 
| _, _ => false
end.

Lemma list_eq_refl : forall l, is_true(list_eq l l).
Proof.
  induction l as [| x xs IH].
  - apply eq_refl.
  - simpl. apply andb_true_iff. split.
    * apply Nat.eqb_refl.
    * apply IH. 
Qed.

Lemma matrix_eq_refl : forall m, is_true(matrix_eq m m).
Proof.
  induction m as [| row rows IH]. 
  - apply eq_refl.
  - simpl. apply andb_true_iff. split.
    * apply list_eq_refl.
    * apply IH. 
Qed.

Fixpoint set_row (m : matrix) (idx : nat) (new_row : list nat) : matrix :=
  match m with
  | [] => []
  | h :: t =>
      if Nat.eqb idx 0 then new_row :: t 
      else h :: set_row t (pred idx) new_row 
  end.


(* -------------------- DATA STRUCTURES -------------------- *)
Definition resource_capacities := vector. (* m x 1 *)
Definition consumed_resources := vector. (* m x 1 *)
Definition user_allocations := matrix. (* n x m *)
Definition user_demand_vectors := matrix. (* n x m *)

Fixpoint valid_resource_relation (C : consumed_resources) (R : resource_capacities) : Prop :=
match C, R with
| [], [] => True
| c0 :: cRest, r0 :: rRest =>  c0 <= r0 /\ (valid_resource_relation cRest rRest)
| _, _ => False
end.

Lemma exampleCorrect: valid_resource_relation [1; 1; 2] [1; 2; 3].
Proof.
unfold valid_resource_relation; simpl; auto.
Qed.

Lemma examplesWrong : 
not (valid_resource_relation [1; 1] [1; 2; 3]) (* diff lens *)
/\ not (valid_resource_relation [1; 1; 2] [1; 2]) (* diff lens *)
/\ not (valid_resource_relation [1; 4; 2] [1; 2; 3]). (*cap violated *)
Proof.
unfold valid_resource_relation. split; try split; intro H; try apply H; destruct H as [H1 [H2 [H3 H4]]]; apply Nat.lt_nge in H2; contradiction. 
Qed.


Definition compare_ratios (n1 d1 n2 d2 : nat) : comparison :=
  if n1 * d2 =? n2 * d1 then Eq
  else if n1 * d2 <?  n2 * d1 then Lt
  else Gt.


Fixpoint max_in_list_ratios (num denom : list nat) (max_n max_d max_idx current_idx: nat): nat :=
match num, denom with
| n :: ns, d :: ds =>
  match compare_ratios n d max_n max_d with
  | Gt => max_in_list_ratios ns ds n d current_idx (1 + current_idx)
  | _ => max_in_list_ratios ns ds max_n max_d max_idx (1 + current_idx)
  end
| _, _ => max_idx
end.

Definition max_ratio_index (numerators denominators : list nat) : nat :=
  max_in_list_ratios numerators denominators 0 1 0 0.

(* Compares 4/9 with 2/3 -- 2/3 is the max ratio *)
Example ex_max_ratio:
max_ratio_index [4; 2] [9; 3]  = 1.
Proof.
unfold max_ratio_index; simpl; auto.
Qed. 

(* gives index in the resource array *)
Definition get_user_dominant_share_indices (M: matrix) (R: list nat) : list nat :=
  (* Apply max_ratio_index to each row with R as the denominator list *)
  map (fun row => max_ratio_index row R) M.

Example test_get_user_dominant_share_indices:
get_user_dominant_share_indices [[1; 4]; [3; 1]] [9; 18] = [1; 0].
Proof.
unfold get_user_dominant_share_indices; simpl; auto.
Qed.

Definition min_index_ratios_helper (indices R : list nat) (M : matrix) : option (nat * nat * nat) :=
  match M, indices with
  | [], _ => None  (* No users *)
  | _, [] => None  (* No indices *)
  | row1 :: rest_rows, i1 :: rest_indices =>
      (* Initial min values (using the first row) *)
      let min_idx := 0 in
      let min_numerator := nth i1 row1 0 in
      let min_denominator := nth i1 R 1 in

      (* Fold through remaining users *)
      Some (fold_left (fun acc userI =>
                        let '(min_idx, min_numerator, min_denominator) := acc in
                        match nth_error rest_indices userI, nth_error rest_rows userI with
                        | Some resource_idx, Some numerators =>
                          let numerator := nth resource_idx numerators 0 in
                          let denominator := nth resource_idx R 1 in
                          match compare_ratios numerator denominator min_numerator min_denominator with
                          | Lt => (userI + 1, numerator, denominator)  (* Update if smaller ratio *)
                          | _  => acc  (* Keep previous min *)
                          end
                        | _, _ => acc (* Skip if out of bounds *)
                        end)
                      (seq 0 (length rest_rows))
                      (min_idx, min_numerator, min_denominator))
  end.

Definition min_index_ratios (indices R : list nat) (M : matrix) : nat :=
  match min_index_ratios_helper indices R M with
  | Some (min_idx, _, _) => min_idx
  | None => 0
  end.

(* 4/18 = 0.222 vs 3/9 = 0.3333 --> Choose smaller dom share: 4/18 *)
Example test_min_index_ratios:
let R := [9; 18] in
let U := [[1; 4]; [3; 1]] in 
min_index_ratios (get_user_dominant_share_indices U R) R U = 0.
Proof.
unfold min_index_ratios; simpl; auto.
Qed.

Inductive state : Type :=
    mkState : consumed_resources -> resource_capacities -> user_allocations -> user_demand_vectors -> state.

Definition get_consumed (s : state) : consumed_resources :=
match s with
| mkState C _ _ _ => C
end.

Definition get_resources (s : state) : resource_capacities :=
match s with
| mkState _ R _ _ => R
end.
  
Definition get_allocs (s : state) : user_allocations :=
match s with
| mkState _ _ U _  => U
end.

Definition get_demands (s : state) : user_demand_vectors :=
match s with
| mkState _ _ _ D => D
end.

Definition get_alloc_for_user (s : state) (userI : nat) :=
match s with
| mkState _ _ U _  => 
  let all_allocs := get_allocs s in 
  let user_allocs_wrapped := nth_error all_allocs userI in
  match user_allocs_wrapped with 
  | Some user_alloc => user_alloc
  | None => []
  end
end.

Definition update_state (s : state) (userI : nat) (applied_demand : list nat) : state :=
  let newConsumed := list_add (get_consumed s) (applied_demand) in
  let newUserAllocRow := list_add (get_alloc_for_user s userI) (applied_demand) in
  let newUserAllocs := (set_row (get_allocs s) userI newUserAllocRow) in
  mkState newConsumed (get_resources s) newUserAllocs (get_demands s).

(* ------------- DRF ALGO -------------- *)
Definition DRF_Algorithm (s : state): state :=
    let C := (get_consumed s) in 
    let R := (get_resources s) in
    let U := (get_allocs s) in 
    let D := (get_demands s) in 
    let dominant_shares := (get_user_dominant_share_indices U R) in 
    let user_indx := min_index_ratios dominant_shares R U in
    let demand_vector := nth user_indx D [] in
    let newC := list_add C demand_vector in 
    if (list_leq (newC) R) (* C + D <= R*)
    then (update_state s user_indx demand_vector) 
    else s .


Definition state_equivalence (s1 s2 : state): Prop :=
let matchResources := list_eq (get_resources s1) (get_resources s2) in
let matchConsumed := list_eq (get_consumed s1) (get_consumed s2) in 
let matchAllocs := matrix_eq (get_allocs s1) (get_allocs s2) in
let matchDemands := matrix_eq (get_demands s1) (get_demands s2) in
is_true (matchConsumed) /\ is_true matchResources /\ is_true matchAllocs /\ is_true matchDemands.


(* -------------- FROM CS 345H Notes ----------------- *)
Definition step (s1 s2: state) := s2 = DRF_Algorithm s1.

Inductive step_star : state -> state -> Prop :=
| step_refl : forall s, step_star s s
| step_once : forall s1 s2 s3, step s1 s2 -> step_star s2 s3 -> step_star s1 s3.
(* -------------- END: FROM CS 345H Notes ----------------- *)

Definition equilibrium_state (s : state) : Prop := step s s.

Fixpoint do_n_steps (s : state) (fuel: nat) : state :=
  match fuel with
  | 0 => s (* Fuel gone before finish! *)
  | S fuel_minus_1 => match (DRF_Algorithm s) with
                      | s' => do_n_steps s' fuel_minus_1
                      end
  end.

Example drf_paper_example (s: state) :
let R := [9; 18] in   (* resource capacities *)
let D := [ [1; 4]; [3; 1] ] in 
let C0 := [0; 0] in   (* consumed resources *)
let U0 := [[0; 0]; [0; 0]] in (* user allocations *)
let CN := [9; 14]  in 
let UN := [[3; 12]; [6; 2]] in 
let s0 := mkState C0 R U0 D in
let sN := mkState CN R UN D in
  state_equivalence (do_n_steps s0 5) sN.
Proof.
firstorder. 
Qed.


Lemma step_deterministic :
  forall s s1 s2 : state, step s s1 -> step s s2 -> state_equivalence s1 s2.
Proof.
  intros s s1 s2 Hstep1 Hstep2.
  inversion Hstep1; subst; clear Hstep1.
  inversion Hstep2; subst; clear Hstep2.
  firstorder.
  - apply list_eq_refl.
  - apply list_eq_refl.
  - apply matrix_eq_refl.
  - apply matrix_eq_refl. 
Qed.

Lemma equilibrium_state_cannot_step_to_new_state :
  forall s s', equilibrium_state s -> (step s s' -> state_equivalence s s').
Proof.
  intros; unfold equilibrium_state in H; apply step_deterministic with (s := s); assumption.
Qed.
