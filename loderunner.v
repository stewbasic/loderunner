Require Import Relations.
Require Import List.
Import ListNotations.
 
(* Formalism of loderunner; this must be checked to agree with the desired game.
Note that the y-axis points downwards. *)
Inductive tile := | air | stone | brick | ladder | pipe.
Definition is_solid t := t = stone \/ t = brick.
Definition is_supporting t := is_solid t \/ t = ladder.
Definition is_holdable t := t = ladder \/ t = pipe.

Definition position:Set := nat * nat.
Definition below (p:position) := let (x,y) := p in (x,S y).
Definition above (p q:position) := q = below p.
Definition right (p q:position) := p = let (x,y) := q in (S x,y).
Definition beside p q := right p q \/ right q p.

Definition grid A := list (list A).
Record state := {sp: position ; sg: grid tile ; sd: list position}.
Definition evg {A} a (g:grid A) (p:position) := nth (fst p) (nth (snd p) g []) a.
Definition ev := evg stone.
Definition set p t g h := ev h p = t /\ forall q, q = p \/ ev h q = ev g q.

Definition supported g p := (is_holdable (ev g p)) \/ (is_supporting (ev g (below p))).
Inductive move g : relation position :=
  | move_down : forall p q, above p q -> move g p q
  | move_up : forall p q, above q p -> (ev g p = ladder) -> move g p q
  | move_beside : forall p q, beside p q -> supported g p -> move g p q.
Inductive step : relation state :=
  | step_move p q g d: move g p q -> ~is_solid (ev g q) ->
      step {|sp:=p;sg:=g;sd:=d|} {|sp:=q;sg:=g;sd:=d|}
  | step_destroy p ps pb g h d: beside p ps -> above ps pb ->
      ~is_solid (ev g ps) -> ev g pb = brick -> supported g p -> set pb air g h ->
      step {|sp:=p;sg:=g;sd:=d|} {|sp:=p;sg:=h;sd:=pb::d|}
  | step_solidify p q g h d: p <> q -> set q brick g h ->
      step {|sp:=p;sg:=g;sd:=d++[q]|} {|sp:=p;sg:=h;sd:=d|}.

Definition can_reach := clos_refl_trans _ step.
Definition can_reach_pos g p q := exists d h,
  can_reach {|sp:=p;sg:=g;sd:=[]|} {|sp:=q;sg:=h;sd:=d|}.
Definition rect {A} w h (g:grid A) := length g = h /\ forall r, In r g -> length r = w.
Definition cross g := exists w h, rect (S w) (S h) g /\
  can_reach_pos g (0,0) (w,h) /\
  can_reach_pos g (w,0) (0,h) /\
  ~can_reach_pos g (0,0) (0,h) /\
  ~can_reach_pos g (w,0) (w,h).
Definition contains (g : grid tile) t := exists r, In t r /\ In r g.
Definition exists_cross := exists g, cross g.
Definition cross_required_tiles := forall l,
  (exists g, cross g /\ forall t, contains g t -> In t l) <-> incl [brick;ladder] l.
(* End of formalism. Now we prove exists_cross and cross_required_tiles. *)

Require Import Ascii.
Require Import String.
Require Import Basics.
Require Import EqualitiesFacts.
Require Lists.ListSet.
Import Nat.
Import PeanoNat.Nat.
Import List.

#[local] Instance neq_Symmetric {A} : RelationClasses.Symmetric (fun (x y:A) => x <> y).
intros x y H G. symmetry in G. apply (H G). Qed.
#[local] Instance beside_Symmetric : RelationClasses.Symmetric beside.
intros p q. unfold beside. tauto. Qed.

Definition dims {A} (g:grid A) := let w := length (hd [] g) in
  if forallb (fun r => length r =? w) g then Some(w,length g) else None.
Lemma isrect {A} (g:grid A): match dims g with | Some(w,h) => rect w h g | None => True end.
unfold dims. destruct (forallb _ _) eqn:E. rewrite forallb_forall in E. split. split. intros r H.
rewrite <- eqb_eq. apply (E _ H). split. Qed.

Lemma minus_less {a b c:nat} : S a = b - c -> c < b.
intros H. apply Minus.lt_O_minus_lt. rewrite <- H. apply Le.le_n_S. apply le_0_l. Qed.
Lemma minus_inv {a b:nat}: a < b -> exists c, c < b /\ c = b - S a /\ a = b - S c.
intros H. exists (b-S a). assert (S a=b-(b-S a)) as H1. symmetry. apply add_sub_eq_r. symmetry.
apply Minus.le_plus_minus. apply H. repeat split. apply (minus_less H1). rewrite sub_succ_r.
apply (f_equal pred H1). Qed.

Definition grid_map {A B} (f:A->B) g := map (map f) g.
Lemma nth_nil {A} (a:A) n: nth n [] a = a. destruct n; split. Qed.
Lemma nth_y {A x y a w h} {gr:grid A} : rect w h gr -> h <= y -> evg a gr (x,y) = a.
intros [Hh _] Hy. unfold evg. simpl. rewrite <- Hh in Hy. rewrite (nth_overflow _ _ Hy). apply nth_nil. Qed.
Lemma nth_x {A x y a w h} {gr:grid A} : rect w h gr -> w <= x -> evg a gr (x,y) = a.
intros [_ Hw] Hx. unfold evg. apply nth_overflow. eapply Le.le_trans. 2: apply Hx.
destruct (nth_in_or_default y gr []) as [H|H]. rewrite Hw. constructor. apply H. simpl.
rewrite H. apply le_0_l. Qed.
Definition grid_size {A} (g:grid A) := fold_left plus (map (@length _) g) 0.
Fixpoint replace {A} (x:nat) (a:A) l := match (x,l) with | (_,[]) => []
  | (S x,b::l) => b::(replace x a l)
  | (0,b::l) => a::l end.
Lemma replace_len {A x l} {a:A}: length (replace x a l) = length l.
revert x. induction l; intros [|x]; try split. simpl. rewrite IHl. split. Qed.
Lemma replace1 {A x l} {a b:A}: x < length l -> nth x (replace x a l) b = a.
revert x. induction l. intros x H. inversion H. intros [|x] H. split. apply Le.le_S_n in H. apply (IHl _ H). Qed.
Lemma replace2 {A x1 x2 l} {a b:A}: x1 = x2 \/ nth x1 (replace x2 a l) b = nth x1 l b.
revert x1 x2. induction l. intros x1 [|x2]; right; split. intros [|x1] [|x2]. left. split. 1,2:right;split.
destruct (IHl x1 x2) as [H|H]. left. rewrite H. split. right. apply H. Qed.
Definition replaceg {A} (p:position) (a:A) g := let (x,y):= p in replace y (replace x a (nth y g [])) g.
Definition setg {A} p (d t:A) g h := evg d h p = t /\ forall q, q = p \/ evg d h q = evg d g q.
Lemma set_equiv p t g h : set p t g h <-> setg p stone t g h. unfold set. unfold setg. tauto. Qed.
Lemma replace_set {A} p (d t:A) g: evg d g p = d \/ setg p d t g (replaceg p t g).
destruct p as [x y]. unfold replaceg. unfold setg. unfold evg. simpl.
epose proof (Compare_dec.le_lt_dec _ x) as [H|H]. left. apply nth_overflow. apply H. right.
epose proof (replace1 _) as G. split. rewrite G. apply replace1. apply H. intros [z w]. simpl.
epose proof replace2 as [F|F]. 2:rewrite F. rewrite F. rewrite G. epose proof replace2 as [E|E]. 2:rewrite E.
left. rewrite E. split. all:right;split. Unshelve. epose proof (Compare_dec.le_lt_dec _ y) as [G|G].
rewrite nth_overflow in H. inversion H. all:apply G. Qed.

Definition flipg {A} := map (@rev A).
Definition flipp w (p:position) := match p with | (x,y) => (w-S x,y) end.
Module Sym.
Section Sym.
Context {w:nat}.
Definition flipx x := if x<?w then w-S x else x.
Definition flipr r := let r1 := r ++ (repeat stone (w-length r)) in
  (rev (firstn w r1))++(skipn w r1).
Lemma flipr_nth x r : nth x r stone = nth (flipx x) (flipr r) stone.
unfold flipr. set (r++_) as r1.
erewrite (_:forall a b d, length a = w -> nth (flipx x)(rev a++b) d=nth x (a++b) d). rewrite firstn_skipn.
unfold r1. destruct (Compare_dec.le_lt_dec (length r) x) as [Hx|Hx]. rewrite app_nth2. rewrite nth_repeat.
apply nth_overflow. 1,2:apply Hx. rewrite app_nth1. split. apply Hx. apply firstn_length_le.
unfold r1. rewrite app_length. rewrite repeat_length. rewrite add_comm. apply sub_add_le. Unshelve.
intros a b d Hw. unfold flipx. destruct (x<?w) eqn:Hx. apply Compare_dec.leb_complete in Hx.
destruct (minus_inv Hx) as [x1[H1[H2 H3]]]. rewrite <- H2. repeat (rewrite app_nth1). rewrite H3.
rewrite <- Hw. apply rev_nth. 3:rewrite rev_length. 1,2,3: rewrite Hw. 1,3:apply H1. apply Hx.
apply Compare_dec.leb_complete_conv in Hx. apply Le.le_S_n in Hx. repeat (rewrite app_nth2).
1,3: rewrite rev_length. split. 1,2: rewrite Hw. 1,2: apply Hx. Qed.

Definition flipg1 g := map flipr g.
Definition flipp1 (p:position) := match p with | (x,y) => (flipx x,y) end.
Lemma flip_ev g p: ev (flipg1 g) (flipp1 p) = ev g p.
symmetry. unfold ev. unfold evg. unfold flipg1. destruct p as [x y]. simpl.
destruct (Compare_dec.le_lt_dec (length g) y) as [Hy|Hy]. repeat (rewrite (nth_overflow _ [])).
repeat (rewrite nth_nil). split. rewrite map_length. 1,2:apply Hy. erewrite (nth_indep (map _ _)).
rewrite map_nth. apply flipr_nth. rewrite map_length. apply Hy. Qed.
Lemma flipr_eq r: length r = w -> rev r = flipr r.
intros Hr. unfold flipr. rewrite <- Hr. rewrite sub_diag. simpl. rewrite app_nil_r. rewrite skipn_all.
rewrite app_nil_r. rewrite firstn_all. split. Qed.
Lemma flipg1_eq {h g}: rect w h g -> flipg g = flipg1 g.
intros [Hh Hw]. unfold flipg1. unfold flipg. apply map_ext_in. intros r Hr. apply flipr_eq. apply Hw.
apply Hr. Qed.
Lemma flipp1_eq {p}: fst p < w -> flipp w p = flipp1 p.
destruct p as [x y]. simpl. unfold flipx. intros Hx. rewrite <- ltb_lt in Hx. rewrite Hx. split. Qed.
Definition thin g:= forall p, ~ is_solid (ev g p) -> fst p < w.
Lemma flip_below p: flipp1 (below p) = below (flipp1 p). destruct p as [x y]. split. Qed.
Lemma flip_right {p q}: right p q -> fst p < w -> right (flipp1 q) (flipp1 p).
destruct q as [x y]. intros Hr. rewrite Hr. intros Hx1. repeat (rewrite <- flipp1_eq). 3:apply Le.le_S_n.
3:constructor. 2,3:apply Hx1. unfold right. simpl. rewrite <- sub_succ_l. rewrite sub_succ. split. apply Hx1.
Qed.
Lemma flip_beside {p q}: beside p q -> fst p < w -> fst q < w -> beside (flipp1 p) (flipp1 q).
unfold beside. intros [H|H] Hp Hq. 1:right. 2:left. all:apply flip_right. all:assumption. Qed.
Lemma flip_above {p q}: above p q -> above (flipp1 p) (flipp1 q).
unfold above. rewrite <- flip_below. apply f_equal. Qed.
Lemma flip_supported {g p}: supported g p -> supported (flipg1 g) (flipp1 p).
intros [H|H]. 1:left. 2:right. 2:rewrite <- flip_below. 1,2:rewrite flip_ev. 1,2:assumption. Qed.
Lemma flip_move {g p q}: fst p < w -> fst q < w -> move g p q -> move (flipg1 g) (flipp1 p) (flipp1 q).
intros Hp Hq H. inversion H. 3:apply move_beside. 4:apply flip_supported. 3:apply flip_beside.
2:apply move_up. 1:apply move_down. 1,2:apply flip_above. 3:rewrite flip_ev. all:assumption. Qed.
Lemma flipx_inv x : flipx (flipx x) = x.
unfold flipx. destruct (Compare_dec.le_lt_dec w x) as [Hx|Hx]. rewrite <- ltb_ge in Hx. repeat (rewrite Hx).
split. destruct (minus_inv Hx) as [x1[H1[H2 H3]]]. rewrite <- ltb_lt in Hx. rewrite Hx. rewrite <- H2.
rewrite <- ltb_lt in H1. rewrite H1. symmetry. apply H3. Qed.
Lemma flipp1_inv p: flipp1 (flipp1 p) = p. destruct p. simpl. rewrite flipx_inv. split. Qed.
Lemma flip_set {g h p t}: set p t g h -> set (flipp1 p) t (flipg1 g) (flipg1 h).
intros [H1 H2]. split. rewrite flip_ev. apply H1. intros q. rewrite <- (flipp1_inv q). set (flipp1 q) as r.
repeat (rewrite flip_ev). destruct (H2 r) as [Hr|Hr]. left. rewrite Hr. split. right. apply Hr. Qed.
Definition thins s := fst (sp s) < w /\ thin (sg s).
Definition flips s := {|sp:=flipp1 (sp s);sg:=flipg1 (sg s);sd:=map flipp1 (sd s)|}.
Lemma flip_step {s t}: thins s -> step s t -> thins t /\ step (flips s) (flips t).
destruct s as [p g d]. destruct t as [q h e]. intros [Hp Hg] Hs. unfold flips. simpl. inversion Hs.
rewrite H4 in Hg. pose proof (Hg _ H6) as Hq. split. apply  (conj Hq Hg). apply step_move.
apply (flip_move Hp Hq H1). rewrite flip_ev. apply H6. rewrite H2 in Hp. pose proof (Hg _ H7) as Hps.
repeat split. apply Hp. simpl. intros r Hr. destruct ((proj2 H10) r) as [Hr1|Hr1]. replace (fst r) with (fst ps).
apply Hps. rewrite Hr1. rewrite H6. destruct ps. split. rewrite Hr1 in Hr. apply (Hg _ Hr).
apply (step_destroy _ (flipp1 ps)). apply (flip_beside H5 Hp). apply Hps. apply (flip_above H6).
1,2:(rewrite flip_ev; assumption). apply (flip_supported H9). apply (flip_set H10). rewrite H3 in Hp.
repeat split. apply Hp. simpl. intros r Hd. destruct ((proj2 H6) r) as [Hr|Hr]; rewrite Hr in Hd.
rewrite (proj1 H6) in Hd. destruct Hd. right. split. apply (Hg _ Hd). rewrite map_app. apply step_solidify.
intros Heq. apply (f_equal flipp1) in Heq. repeat (rewrite flipp1_inv in Heq). apply (H1 Heq).
apply (flip_set H6). Qed.
Lemma flip_reach {s t}: thins s -> can_reach s t -> thins t /\ can_reach (flips s) (flips t).
intros Hs. revert t. apply clos_refl_trans_ind_left. split. apply Hs. apply rt_refl.
intros t r Hst [Ht Hr] Htr. destruct (flip_step Ht Htr) as [H1 H2]. split. apply H1. eapply rt_trans.
apply Hr. apply rt_step. apply H2. Qed.

Theorem reach {h g p q}: rect w h g -> fst p < w -> can_reach_pos g p q
  -> can_reach_pos (flipg g) (flipp w p) (flipp w q).
intros Hg Hp [d [g1 Hd]]. eassert _ as Ht. 2:destruct (flip_reach Ht Hd) as [[Ht1 _] Hr]. split. apply Hp.
intros [x y] Hs. destruct (Compare_dec.le_lt_dec w x) as [Hx|Hx]. unfold ev in Hs. rewrite (nth_x Hg Hx) in Hs.
destruct Hs. left. split. apply Hx. rewrite (flipp1_eq Hp). simpl in Ht1. rewrite (flipp1_eq Ht1).
rewrite (flipg1_eq Hg). eexists. eexists. apply Hr. Qed.
End Sym.
End Sym.
Theorem cross_sym {w h g}: g=flipg g -> rect (S w) (S h) g ->
  can_reach_pos g (w,0) (0,h) -> ~can_reach_pos g (0,0) (0,h) -> cross g.
intros Hs Hg Hp Hn. exists w. exists h. eenough ((0,0)=_) as H1.
unshelve (eapply (conj Hg (conj _ (conj Hp (conj Hn _))))). 2:intros H. 2:apply Hn. 1,2:rewrite Hs; rewrite H1.
erewrite (_:(w,h)=_). eapply (Sym.reach Hg _ Hp). erewrite (_:(0,h)=_).
eapply (Sym.reach Hg _ H). Unshelve. 3,5:constructor. all:unfold flipp. 1,3:rewrite sub_diag.
3:(rewrite sub_succ;rewrite sub_0_r). all:split. Qed.

Scheme Equality for tile. (* Defines tile_beq, internal_tile_dec_bl *)
Definition is_empty t := ~is_solid t.
Definition emptyb t := match t with | stone | brick => false | _ => true end.
Definition supportingb t := match t with | stone | brick | ladder => true | _ => false end.
Definition holdableb t := match t with | ladder | pipe => true | _ => false end.
Definition supportedb g p := ((holdableb (ev g p)) || (supportingb (ev g (below p))))%bool.
Lemma tile_dec {t1 t2} : (t1 = t2) <-> tile_beq t1 t2 = true.
split. apply internal_tile_dec_lb. apply internal_tile_dec_bl. Qed.
Lemma not_equiv P Q: ((P \/ Q) /\ ~(P /\ Q)) -> (~P <-> Q).
intros [HO HN]. split. intros H. destruct HO as [HP|HQ]. destruct (H HP). apply HQ. intros HQ HP.
apply (HN (conj HP HQ)). Qed.
Proposition empty_equiv {t} : is_empty t <-> emptyb t = true.
unfold is_empty. apply not_equiv. unfold is_solid. repeat (rewrite tile_dec). split. destruct t; tauto.
destruct t; simpl; intros [[H|H] G]; inversion H; inversion G. Qed.
Lemma empty_dec {t} : is_empty t \/ is_solid t.
rewrite empty_equiv. unfold is_solid. destruct t; simpl; tauto. Qed.
Proposition supporting_equiv {t} : is_supporting t <-> supportingb t = true.
unfold is_supporting. unfold is_solid. repeat (rewrite tile_dec). destruct t; simpl; tauto. Qed.
Proposition holdable_equiv {t} : is_holdable t <-> holdableb t = true.
unfold is_holdable. repeat (rewrite tile_dec). destruct t; simpl; tauto. Qed.
Proposition supported_equiv {g p} : supported g p <-> supportedb g p = true.
unfold supported. unfold supportedb. rewrite Bool.orb_true_iff. rewrite supporting_equiv.
rewrite holdable_equiv. tauto. Qed.
Lemma air_empty: is_empty air. rewrite empty_equiv. split. Qed.

Module PP.
Inductive token := | token_tile (t:tile) | newline | unknown.
Definition parse_tile a := match a with
  | "010"%char => newline
  | " "%char => token_tile air
  | "B"%char => token_tile brick
  | "S"%char => token_tile stone
  | "+"%char => token_tile ladder
  | "-"%char => token_tile pipe
  | _ => unknown end.
Fixpoint parse_helper s r l := match s with
  | EmptyString => (rev r)::l
  | String a s1 => let (r1,l1) := match (parse_tile a) with
    | newline => ([], (rev r)::l)
    | token_tile t => (t::r, l)
    | unknown => (r, l) end in parse_helper s1 r1 l1 end.
Fixpoint chop {A} (l : list (list  A)) := match l with
  | []::l1 => chop l1
  | _ => l end.
Definition parse s := chop (rev (chop (parse_helper s [] []))).

Fixpoint rev_list_ascii_to_string (s : list ascii) (t : string) := match s with
  | [] => t
  | a::s1 => rev_list_ascii_to_string s1 (String a t) end.
Definition index_char x := ascii_of_nat (48 + (x mod 10)).
Definition print_row swy r := match swy with
  | (s,w,y) => (["010"%char;index_char y;" "%char]++(rev_append r s),max w (length r),S y) end.
Fixpoint index_row w s := match w with | 0 => s | S w => index_row w ((index_char w)::s) end.
Definition print_grid g := match fold_left print_row g (["010"%char],0,0) with
  | (s,w,_) => rev_list_ascii_to_string (rev_append (index_row w []) s) "" end.

Definition tile_to_ascii t := match t with
  | air => " "%char
  | brick => "B"%char
  | stone => "S"%char
  | ladder => "+"%char
  | pipe => "-"%char end.
Definition print_tiles g := print_grid (grid_map tile_to_ascii g).
End PP.

Fixpoint while {A B} (f:A -> A*option B) a n := match n with
  | 0 => None
  | S n => let (a,b) := f a in if b then b else while f a n end.
Lemma while_inv {A B} {f:A -> A*option B} {a b n} {P:A->Prop}: (forall c, P c -> P (fst (f c))) -> P a ->
  while f a n = Some b -> exists c, P c /\ snd (f c) = Some b.
intros Hp. generalize a. induction n; intros c Hc H. inversion H. simpl in H.
destruct (f c) as (d,[e|]) eqn:Hfc. exists c. rewrite Hfc. apply (conj Hc H). unshelve (eapply (IHn _ _ H)).
pose proof (Hp _ Hc) as Hd. rewrite Hfc in Hd. apply Hd. Qed.

Module PosDec.
Include PairUsualDecidableType PeanoNat.Nat PeanoNat.Nat.
Include Equalities.HasEqDec2Bool.
End PosDec.
Definition poss := ListSet.set position.
Definition poss_union := ListSet.set_union PosDec.eq_dec.
Definition poss_diff := ListSet.set_diff PosDec.eq_dec.
Definition poss_mem := ListSet.set_mem PosDec.eq_dec.
Definition poss_inter := ListSet.set_inter PosDec.eq_dec.
Definition poss_remove := ListSet.set_remove PosDec.eq_dec.

Fixpoint splitn_helper {A} (n:nat) (p q:list A) := match (n,p,q) with
  | (S n,p,a::q) => splitn_helper n (a::p) q
  | _ => (n,p,q) end.
Definition splitn {A} n (l:list A) := match splitn_helper n [] l with
  | (0,p,q) => Some (rev p, q)
  | _ => None end.
Lemma splitn_app {A n} {l p q:list A}: splitn n l = Some (p,q) -> length p = n /\ l=p++q.
assert (forall m u r s, @splitn_helper A m r s = (0,u,q)->exists t,length t=m/\u=(rev t)++r/\s=t++q) as H.
induction m. intros u r s H. inversion H. exists []. repeat split. intros u r [|a s] H. inversion H. simpl in H.
destruct (IHm _ _ _ H) as [t [Ht [Hp Hq]]]. exists (a::t). rewrite <- Ht. rewrite Hp. rewrite Hq. simpl.
rewrite <- app_assoc. repeat split. unfold splitn. destruct (splitn_helper _ _ _) as [[[|m] r] s] eqn:E;
intros H1; inversion H1. rewrite H3 in E. destruct (H _ _ _ _ E) as [t [Ht [Hu Hs]]]. rewrite app_nil_r in Hu.
rewrite Hu. rewrite rev_involutive. apply (conj Ht Hs). Qed.
Lemma app1 {A s p q} {d:A}: length p = s -> forall x, nth (x+s) (p++q) d = nth x q d.
intros H x. rewrite add_comm. rewrite <- H. apply app_nth2_plus. Qed.
Lemma app2 {A s w x p q r} {d e:A}: length p = s -> length q = w -> x < w -> nth (x+s) (p++q++r) d = nth x q e.
intros Hs Hw Hx. rewrite (app1 Hs). rewrite <- Hw in Hx. rewrite app_nth1. apply nth_indep. all:apply Hx. Qed.
Lemma nth_hd {A n p q} {d:A}: length p = n -> nth n (p++q) d = hd d q.
intros H. rewrite (app1 H 0). destruct q; split. Qed.
Lemma len1 {A l n} {a:A}: length l = n -> length (l++[a]) = S n.
intros H. rewrite app_length. rewrite H. apply add_comm. Qed.
Lemma nxt {A} p q {a:A}: p++a::q = (p++[a])++q. rewrite <- app_assoc. split. Qed.

Module Pos.
Definition can_reach_any g p q := forall d, exists e h,
  can_reach {|sp:=p;sg:=g;sd:=d|} {|sp:=q;sg:=h;sd:=e|}.
Definition state1:Type := (position * grid tile).
Definition reach1 (s t:state1) := forall d, exists e,
  can_reach {|sp:=fst s;sg:=snd s;sd:=d|} {|sp:=fst t;sg:=snd t;sd:=e|}.
Ltac reach1_step := intros ?; eexists; apply rt_step; simpl.
Lemma reach1_refl: reflexive _ reach1. intros [p g] d. eexists. apply rt_refl. Qed.
(* Split the middle pair to make eapply more convenient *)
Lemma reach1_trans {s t p g}: reach1 s (p,g) -> reach1 (p,g) t -> reach1 s t.
intros H1 H2 d. destruct (H1 d) as [e H3]. destruct (H2 e) as [f H4]. eexists. eapply rt_trans.
apply H3. apply H4. Qed.

Section Reach.
Context (g:grid tile).
Definition pre_neighbors (p:position) := let (x,y) := p in
  let s := supportedb g p in [
  (s, (S x,y));
  ((s && (0 <? x))%bool, (pred x, y));
  ((tile_beq (ev g p) ladder && (0 <? y))%bool, (x, pred y));
  (true, (x, S y))].
Definition neighbors p :=
  let n1 := map (@snd _ _) (filter (@fst _ _) (pre_neighbors p)) in
  filter (fun q => emptyb (ev g q)) n1.
Definition reachb_step p oc := match oc with
  | ([],_) => (oc,None)
  | (q::o,c) => ((poss_union (poss_diff (neighbors q) c) o,q::c),if (PosDec.eqb p q) then Some tt else None)
end.
Definition reachb p q := if (while (reachb_step q) ([p],[]) (grid_size g)) then true else false.
Definition reach_pos p q := forall d, can_reach {|sp:=p;sg:=g;sd:=d|} {|sp:=q;sg:=g;sd:=d|}.
Definition reach_set p oc := forall q, In q (@fst poss poss oc) -> reach_pos p q.
Lemma reach_set_init p: reach_set p ([p],[]).
intros q [H|[]] d. rewrite H. apply rt_refl. Qed.
Lemma pre_neighbors_suff p q: In (true,q) (pre_neighbors p) -> move g p q.
destruct p as [x y]. intros [H|[H|[H|[H|[]]]]]; inversion H. 2,3:rewrite Bool.andb_true_iff in H1.
2,3:destruct H1 as [H1 H3]. 1,2:(rewrite <- supported_equiv in H1;apply move_beside). 2,4:apply H1.
right. split. destruct x. 3:destruct y. 1,3:(rewrite ltb_irrefl in H3;inversion H3). left. split.
apply move_up. split. rewrite <- tile_dec in H1. apply H1. apply move_down. split. Qed.
Lemma neighbors_suff p q: In q (neighbors p) -> reach_pos p q.
unfold neighbors. intros H d. rewrite filter_In in H. destruct H as [H1 H2]. apply rt_step. apply step_move.
apply pre_neighbors_suff. rewrite in_map_iff in H1. destruct H1 as [[b q1][H3 H4]]. rewrite filter_In in H4.
destruct H4 as [H4 H5]. rewrite <- H3. rewrite <- H5. apply H4. apply (proj2 empty_equiv H2). Qed.
Lemma reach_set_inv p q oc: reach_set p oc -> reach_set p (fst (reachb_step q oc)).
intros H r Hr. destruct oc as [[|s o] c]. apply H. apply Hr. simpl in Hr.
destruct (ListSet.set_union_elim _ _ _ _ Hr) as [H1|H1]. apply ListSet.set_diff_elim1 in H1. intros d.
eapply rt_trans. apply H. left. split. apply neighbors_suff. apply H1. apply H. right. apply H1. Qed.
Lemma reachb_correct {p q}: reachb p q = true -> reach_pos p q.
unfold reachb. destruct (while _ _ _) eqn:H. intros _. eapply (while_inv _ (reach_set_init p)) in H.
destruct H as [[[|r o] c] [H1 H2]]; simpl in H2. inversion H2. destruct (PosDec.eqb q r) eqn:Hqr.
rewrite PosDec.eqb_eq in Hqr. rewrite Hqr. apply H1. left. split. inversion H2. intros H2. inversion H2.
Unshelve. apply reach_set_inv. Qed.
Lemma reach_pos1 {p q}: reach_pos p q -> reach1 (p,g) (q,g). intros H d. eexists. apply H. Qed.
End Reach.
Lemma mv q g p: if reachb g p q then reach1 (p,g) (q,g) else True.
destruct (_:bool) eqn:H. apply reachb_correct in H. apply (reach_pos1 _ H). split. Qed.

Section Destroy.
Lemma beside_left {x y}: beside (x,y) (S x,y). right. split. Qed.
Lemma beside_right {x y}: beside (S x,y) (x,y). left. split. Qed.
Definition destroyb g p q := (supportedb g p && emptyb (ev g q) && tile_beq (ev g (below q)) brick)%bool.
Lemma destroy_suff g p q d: beside p q -> destroyb g p q = true -> let r := below q in
  step {|sp:=p;sg:=g;sd:=d|} {|sp:=p;sg:=replaceg r air g;sd:=r::d|}.
unfold destroyb. repeat (rewrite Bool.andb_true_iff). rewrite <- supported_equiv. rewrite <- tile_dec.
rewrite <- empty_equiv. intros Hp [[Hs He] Hb]. eapply step_destroy. apply Hp. split. apply He.
apply Hb. apply Hs. rewrite set_equiv. epose proof (replace_set _ _ _ _) as [H|H]. 2:apply H.
unfold ev in Hb. rewrite H in Hb. inversion Hb. Qed.
Lemma destroy r {q} (Hb:beside q r) g p: if (destroyb g q r && reachb g p q)%bool then
  reach1 (p,g) (q,(replaceg (below r) air g)) else True.
destruct (_:bool) eqn:H. rewrite Bool.andb_true_iff in H. destruct H as [Hd H]. eapply reach1_trans.
pose proof (mv q g p) as Hm. rewrite H in Hm. apply Hm. reach1_step. apply destroy_suff; assumption. split. Qed.
End Destroy.

Section Drill.
Definition drill_row s w r := match splitn s r with | None => None | Some (r1,r2) =>
  match splitn w r2 with | None => None | Some (r3,r4) =>
    if forallb (tile_beq brick) ((hd stone r4)::r3) then
      Some (Some (r1++(repeat air w)++r4))
    else if (forallb (emptyb) r3) then Some None else None
end end.
Fixpoint drill_top s w g h := match g with | [] => None | r::g1 => match drill_row s w r with
  | None => None
  | Some None => Some (rev_append g h, length g1)
  | Some (Some r1) => drill_top s (S w) g1 (r1::h) end end.
Definition drill_helper (q:position) g p := let (x,y) := q in match (splitn (S y) g) with | None => None
  | Some (gb,h) => match drill_top x 1 (rev gb) [] with | None => None | Some (ga,z) =>
    if reachb g p (x,z) then Some (ga++h) else None end end.

Definition forp s w (P:nat->Prop) := forall x, x < w -> P (x+s).
Definition forr s w r P := forp s w (fun x => P(nth x r stone)).
Lemma for_sub {s1 w1 s2 w2 P}: forp s1 w1 P -> s1 <= s2 -> w2 + s2 <= w1 + s1 -> forp s2 w2 P.
intros H L R x Hx. assert (x+s2=x+s2-s1+s1) as E. symmetry. apply sub_add. eapply le_trans. apply L.
apply Plus.le_plus_r. rewrite E. apply H. rewrite <- (add_sub w1 s1). apply le_add_le_sub_r. simpl. rewrite <- E.
eapply le_trans. 2:apply R. apply Plus.plus_lt_compat_r. apply Hx. Qed.
Lemma forS {s w P}: forp s (S w) P -> forp s w P /\ forp (S s) w P.
intros H. split; apply (for_sub H). 4:rewrite add_succ_r. all:repeat constructor. Qed.

Lemma movei {w y g} s x1 x2: forp s w (fun x => is_empty (ev g (x,y)) /\ supported g (x,y)) -> x1 < w -> x2 < w
  -> reach1 (x1+s,y,g) (x2+s,y,g).
intros H. assert (x1<=x2 \/ x2<=x1) as [G|G]. epose proof Compare_dec.le_lt_dec as [G|G]. left. apply G.
right. apply Le.le_Sn_le. apply G. all:induction G; intros H1 H2. 1,3:apply reach1_refl.
pose proof (Le.le_Sn_le _ _ H2) as H3. eapply reach1_trans. apply (IHG H1 H3). reach1_step.
apply step_move. apply move_beside. right. split. apply (proj2 (H _ H3)). apply (proj1 (H _ H2)).
pose proof (Le.le_Sn_le _ _ H1) as H3. eapply reach1_trans. 2:apply (IHG H3 H2). reach1_step.
apply step_move. apply move_beside. left. split. apply (proj2 (H _ H1)). apply (proj1 (H _ H3)). Qed.

Definition brick_air s w b a := exists r1 r2, length r1 = s /\ b = r1++(repeat brick w)++r2 /\
  a = r1++(repeat air w)++r2.
Lemma ev_app {A g1 g2 r1 r2 x y} {a d:A}: length g1 = y -> length r1 = x
  -> evg d (g1++(r1++a::r2)::g2) (x,y) = a.
intros Hy Hx. unfold evg. simpl. rewrite (nth_hd Hy). simpl. rewrite (nth_hd Hx). split. Qed.
Lemma nth_app1  {A n p q} {a b d:A}: length p = n \/ nth n (p++a::q) d = nth n (p++b::q) d.
revert n. induction p; intros [|n]; try tauto. destruct (IHp n) as [H|H]. left. apply (f_equal _ H). right.
simpl. rewrite H. split. Qed.
Lemma set_app {A x y g1 g2 r1 r2} {a b d:A}: length g1 = y -> length r1 = x ->
  setg (x,y) d a (g1++(r1++b::r2)::g2) (g1++(r1++a::r2)::g2).
intros Hy Hx. split. apply (ev_app Hy Hx). intros [z w]. unfold evg. simpl. epose proof nth_app1 as [H|H].
2:rewrite H;right;split. repeat (rewrite (nth_hd H)). simpl. epose proof nth_app1 as [G|G]. 2:right;apply G.
left. rewrite <- Hx. rewrite <- Hy. rewrite <- H. rewrite <- G. split. Qed.
Lemma brick_support {g p}: ev g (below p) = brick -> supported g p. right. left. right. apply H. Qed.
Lemma ev_app0 {g1 g2 r x y}: length g1 = y -> ev (g1++r::g2) (x,y) = nth x r stone.
intros Hy. unfold ev. unfold evg. simpl. rewrite nth_hd. split. apply Hy. Qed.
Lemma ev_app1 {g1 g2 r1 r2 x y}: length g1 = y -> ev (g1++r1::r2::g2) (below (x,y)) = nth x r2 stone.
intros Hy. rewrite nxt. simpl. apply (ev_app0 (len1 Hy)). Qed.
Lemma stripr {y g1 g2 r a b} s w: length g1 = y -> brick_air s w b a -> supported (g1++r::b::g2) (w+s,y)
  -> forr s (S w) r is_empty -> reach1 (s,y,g1++r::b::g2) (w+s,y,g1++r::a::g2).
intros Hy [r1 [r2 [Hs [Hb Ha]]]]. rewrite Ha. rewrite Hb. clear Ha Hb. revert r1 s Hs. induction w;
intros r1 s Hs Hw1 E. apply reach1_refl. simpl.
eassert (forall x r3 h, ev (g1++r::(r1++r3)::h) (below(x+s,y))=_) as E1. intros x r3 h. rewrite (ev_app1 Hy).
apply (app1 Hs). eenough _ as Hb. eapply reach1_trans. eapply reach1_trans; reach1_step. apply step_move.
apply move_beside. right. split. apply brick_support. apply Hb. rewrite (ev_app0 Hy). apply (E 1).
repeat (apply Le.le_n_S). apply Le.le_0_n. eapply (step_destroy _ (_,_)). left. 1,2:split. rewrite (ev_app0 Hy).
 apply (E 0). repeat (apply Le.le_n_S). apply Le.le_0_n. apply Hb. destruct w. apply Hw1. apply brick_support.
rewrite (E1 1). split. rewrite nxt. simpl. apply set_app. apply (len1 Hy). apply Hs. rewrite <- app_assoc. simpl.
rewrite <- add_succ_r. repeat (rewrite (nxt r1 (_++r2))). apply IHw. apply (len1 Hs). rewrite add_succ_r.
destruct Hw1 as [Hw1|Hw1]. left. revert Hw1. repeat (rewrite (ev_app0 Hy)). tauto. right. rewrite <- app_assoc.
revert Hw1. simpl. repeat (rewrite (E1 (S w))). simpl. tauto. apply (proj2 (forS E)). rewrite (E1 0). split. Qed.

Lemma nth_repeat1 {s w x t r1 r2}: length r1 = s -> x < w -> nth (x+s) (r1++(repeat t w)++r2) stone = t.
intros Hs Hx. erewrite (app2 Hs (repeat_length _ _) Hx). apply nth_repeat. Qed. 
Lemma drill_row_brick {s w b a}: drill_row s w b = Some (Some a) -> brick_air s w b a /\
  forr s (S w) b (Logic.eq brick) /\ forr s w a is_empty /\ nth (w+s) a stone = brick.
unfold drill_row. destruct (splitn _ _) as [[r1 rr]|] eqn:E. apply splitn_app in E.
destruct (splitn _ _) as [[r2 r3]|] eqn:F. apply splitn_app in F. destruct (forallb _ _) eqn:G.
2: destruct (forallb _ r2). all:intros H; inversion H. rewrite forallb_forall in G. eassert _ as H3.
eapply G. left. split. rewrite <- tile_dec in H3. eassert (r2=_) as H2. eapply Forall_eq_repeat.
rewrite Forall_forall. intros x Hx. rewrite tile_dec. apply G. right. apply Hx. rewrite (proj2 E).
rewrite (proj2 F). rewrite H2. rewrite (proj1 F). eassert (forall t,_=nth _ (r1++repeat t w++r3) _) as B.
intros t. rewrite app_assoc. rewrite nth_hd. apply H3. rewrite app_length. rewrite repeat_length. split.
rewrite <- (proj1 E). repeat eexists. 1,2:intros x Hx. inversion Hx. rewrite add_comm. apply B. symmetry.
apply (nth_repeat1 (eq_refl _) H4). rewrite (nth_repeat1 (eq_refl _) Hx). apply air_empty.
rewrite add_comm. symmetry. apply B. Qed.

Lemma drill1 {g1 g2 b a r x y w}: length g1=y -> drill_row x w b = Some (Some a) ->
  forr x (S w) r is_empty -> w>0 -> (w=1 \/ forr x w (hd [] g2) (Logic.eq brick)) ->
  reach1 (x,y,g1++r::b::g2) (x,S y,g1++r::a::g2).
intros Hy Hd E W B2. destruct (drill_row_brick Hd) as [Hab [B1 [A A1]]]. eapply reach1_trans.
apply (stripr _ _ Hy Hab). apply brick_support. rewrite (ev_app1 Hy). symmetry. apply B1. constructor. apply E.
destruct w. inversion W. eapply reach1_trans. eapply reach1_trans; reach1_step; eapply (step_move (_,_)).
apply move_beside. left. split. apply brick_support. rewrite (ev_app1 Hy). apply A1. rewrite (ev_app0 Hy).
apply E. apply le_succ_diag_r. apply move_down. split. rewrite (ev_app1 Hy). apply A. constructor.
destruct w. apply reach1_refl. destruct B2 as [B2|B2]. inversion B2. eapply (movei x (S w) 0). 2:constructor.
intros z Hz. split. replace (z+x,S y) with (below(z+x,y)). rewrite (ev_app1 Hy). apply (A z Hz). split.
apply brick_support. rewrite nxt. rewrite (nxt _ g2). unfold ev. unfold evg. rewrite nth_hd. symmetry.
apply (B2 z Hz). apply len1. apply (len1 Hy). apply Le.le_n_S. apply Le.le_0_n. Qed.

Lemma drill_row_empty {s w r}: drill_row s w r = Some None -> forr s w r is_empty.
unfold drill_row. destruct (splitn _ _) as [[r1 rr]|] eqn:E. apply splitn_app in E.
destruct (splitn _ _) as [[r2 r3]|] eqn:F. apply splitn_app in F. destruct (forallb _ _).
2:destruct (forallb _ r2) eqn:G. all:intros H;inversion H. rewrite (proj2 E). rewrite (proj2 F). intros x Hx.
erewrite (app2 (proj1 E) (proj1 F) Hx). rewrite empty_equiv. rewrite forallb_forall in G. apply G. apply nth_In.
rewrite (proj1 F). apply Hx. Unshelve. apply air. Qed.
Lemma drill2 {x y w b g h k}: drill_top x w b h = Some (k,y) -> (w=1 \/ forr x w (hd [] g) (Logic.eq brick)) ->
  w>0 -> exists a r, k=a++r::h /\ reach1 (x,y,(rev b)++g) (x,length a,a++r::g) /\ forr x w r is_empty.
revert w g h k. induction b; intros w g h k. 2:simpl; destruct (drill_row _ _ _) as [[r1|]|] eqn:E.
all:intros H Hb Hw; inversion H. destruct (drill_row_brick E) as [_ [Hb1 [He1 _]]].
epose proof (IHb _ (a::g) _ _ H _ _) as [l [r [Hk [Hr He]]]]. exists (l++[r]). exists r1.
repeat (rewrite <- app_assoc). repeat split. apply Hk. eapply reach1_trans. apply Hr. rewrite app_length.
rewrite add_comm. simpl. apply (drill1 (eq_refl _) E He Hw Hb). apply He1. exists (rev b). exists a.
rewrite rev_append_rev. repeat split. rewrite <- app_assoc. rewrite rev_length. apply reach1_refl.
apply (drill_row_empty E). Unshelve. right. apply Hb1. constructor. apply Hw. Qed.
Lemma drill_length {x y w b h k}: drill_top x w b h = Some (k,y) -> length h + length b = length k.
revert w h. induction b; intros w h. 2:simpl; destruct (drill_row _ _ _) as [[r1|]|] eqn:E.
all:intros H; inversion H. rewrite <- (IHb _ _ H). rewrite add_succ_r. split. rewrite rev_append_rev.
rewrite app_length. rewrite rev_length. rewrite add_comm. simpl. rewrite add_succ_r. split. Qed.

Lemma drill q g p: match drill_helper q g p with | Some h => reach1 (p,g) (q,h) | _ => True end.
destruct q as [x y]. unfold drill_helper. destruct (splitn _ _) as [[b h]|] eqn:E.
destruct (drill_top _ _ _ _) as [[a z]|] eqn:F. destruct (reachb _ _ _) eqn:G. apply splitn_app in E.
epose proof (drill2 F _ _) as [k [r [Hk [Hr _]]]]. eapply reach1_trans. apply reach_pos1.
apply (reachb_correct _ G). rewrite (proj2 E). rewrite Hk. rewrite <- app_assoc. replace y with (length k).
rewrite rev_involutive in Hr. apply Hr. apply drill_length in F. rewrite rev_length in F. rewrite Hk in F.
rewrite (proj1 E) in F. rewrite app_length in F. simpl in F. rewrite add_comm in F. inversion F. all:split.
Unshelve. left. split. constructor. Qed.

Fixpoint ind_helper {A} (f:A->bool) l n := match l with | [] => None
  | a::l => if (f a) then Some n else ind_helper f l (S n) end.
Definition ind {A} (f:A->bool) l := ind_helper f l 0.
Definition striph0 s w r := match (splitn s r) with | None => None | Some (r1,r2) =>
  match (splitn w r2) with | None => None | Some (r3,r4) =>
  if forallb emptyb r3 then ind holdableb r3 else None end end.
Definition striph1 s w r := match (splitn s r) with | None => None | Some (r1,r2) =>
  match (splitn w r2) with | None => None | Some (r3,r4) =>
  if forallb (tile_beq brick) r3 then Some(r1++repeat air w++r4) else None end end.
Definition striph p s w y g := match (splitn y g) with
  | Some (g1,r0::r1::g2) => match (striph0 s w r0,striph1 s w r1) with
    | (Some x,Some a) => if (reachb g p (x+s,y) && (1<?w))%bool then Some (x+s,g1++r0::a::g2) else None
    | _ => None end
  | _ => None end.

Lemma ind_helper_nth {A f n m l} {a:A}: ind_helper f l n = Some m -> exists k, m=n+k /\ k < length l /\
  f (nth k l a) = true.
revert n. induction l; intros n; simpl. 2:destruct (f _) eqn:E. all:intros H. 1,2:inversion H. repeat eexists.
apply plus_n_O. apply Le.le_n_S. apply Le.le_0_n. apply E. destruct (IHl _ H) as [k [Hm [Hk Hf]]]. exists (S k).
rewrite add_succ_r. repeat split. apply Hm. apply Le.le_n_S. apply Hk. apply Hf. Qed.
Lemma ind_nth {A f m l} {a:A}: ind f l = Some m -> m < length l /\ f (nth m l a) = true.
intros H. epose proof (ind_helper_nth H) as [k [Hm G]]. rewrite Hm. apply G. Qed.
Lemma striph0_suff {s w x r}: striph0 s w r = Some x -> forr s w r is_empty /\ x < w /\
  is_holdable (nth (x+s) r stone).
unfold striph0. destruct (splitn _ _) as [[r1 r2]|] eqn:E. apply splitn_app in E.
destruct (splitn _ _) as [[r3 r4]|] eqn:F. apply splitn_app in F. destruct (forallb _ _) eqn:G. all:intros H.
2,3,4:inversion H. eapply ind_nth in H. rewrite (proj2 E). rewrite (proj2 F). split. intros u Hu.
erewrite (app2 (proj1 E) (proj1 F) Hu). rewrite empty_equiv. rewrite forallb_forall in G. apply G. apply nth_In.
rewrite (proj1 F). apply Hu. apply proj1 in F. rewrite F in H. erewrite (app2 (proj1 E) F (proj1 H)).
rewrite holdable_equiv. apply H. Unshelve. all: apply air. Qed.
Lemma striph1_suff {s w a b}: striph1 s w b = Some a -> brick_air s w b a.
unfold striph1. destruct (splitn _ _) as [[r1 r2]|] eqn:E. apply splitn_app in E.
destruct (splitn _ _) as [[r3 r4]|] eqn:F. apply splitn_app in F. destruct (forallb _ _) eqn:G. all:intros H;
inversion H. rewrite (proj2 E). rewrite (proj2 F). rewrite forallb_forall in G. eassert (r3=_) as H2.
eapply Forall_eq_repeat. rewrite Forall_forall. intros t Ht. rewrite tile_dec. apply (G _ Ht). rewrite H2.
rewrite (proj1 F). repeat eexists. apply (proj1 E). Qed.

Lemma stripl {y g1 g2 r a b} s w: length g1 = y -> brick_air (S s) w b a -> supported (g1++r::b::g2) (s,y)
  -> forr s (S w) r is_empty -> reach1 (w+s,y,g1++r::b::g2) (s,y,g1++r::a::g2).
intros Hy [r1 [r2 [Hs [Hb Ha]]]]. rewrite Ha. rewrite Hb. clear Ha Hb. revert r1 s Hs. induction w;
intros r1 s Hs H0 E. apply reach1_refl. simpl. eapply reach1_trans. rewrite (nxt r1). rewrite <- add_succ_r.
apply IHw. apply (len1 Hs). apply brick_support. rewrite (ev_app1 Hy). 1,3:rewrite <- nxt. rewrite (nth_hd Hs).
split. eenough _ as B. eapply reach1_trans; reach1_step. eapply (step_move _ (_,_)). apply move_beside.
left. split. apply brick_support. apply B. rewrite (ev_app0 Hy). apply (E 0). apply lt_0_succ.
eapply step_destroy. right. split. split. rewrite (ev_app0 Hy). apply (E 1). apply Le.le_n_S. apply lt_0_succ.
apply B. destruct H0 as [H0|H0]. left. revert H0. repeat (rewrite (ev_app0 Hy)). tauto. right. revert H0.
repeat (rewrite (ev_app1 Hy)). eassert (forall q, nth s (r1++q) _=nth s r1 _) as T. intros q. apply app_nth1.
rewrite Hs. constructor. repeat (rewrite T). tauto. simpl. repeat (rewrite (nxt g1 (_::g2))). apply set_app.
apply (len1 Hy). apply Hs. rewrite (ev_app1 Hy). rewrite (nth_hd Hs). split. apply (proj2 (forS E)). Qed.

Lemma strip s w y g p: match striph p s w y g with | Some (z,h) => reach1 (p,g) (z,y,h) | _ => True end.
unfold striph. destruct (splitn _ _) as [[g1 [|r0 [|b g2]]]|] eqn:Hy; try split. apply splitn_app in Hy.
destruct (striph0 _ _ _) as [x|] eqn:F. apply striph0_suff in F. destruct F as [E Hx].
destruct (striph1 _ _ _) as [a|] eqn:G. apply striph1_suff in G. rewrite (proj2 Hy). apply proj1 in Hy.
destruct (reachb _ _ _) eqn:R. destruct (1<?w) eqn:W. all:try split. simpl. eapply reach1_trans.
apply reach_pos1. apply (reachb_correct _ R). destruct w as [|[|w]]; inversion W. apply ltb_lt in W.
destruct G as [r1 [r2 [Hs [Hb Ha]]]]. rewrite Hb. rewrite Ha. eassert (forall h, supported (g1++r0::h) _) as Hh.
intros h. left. erewrite (ev_app0 Hy). apply (proj2 Hx). apply proj1 in Hx. eassert (x<=_) as Hx1. apply le_S.
apply Le.le_S_n. apply Hx. eassert (forall z h, z<_ -> is_empty (ev (g1++r0::h) _)) as He. intros z h Hz.
erewrite (ev_app0 Hy). apply (E _ Hz). destruct x. eenough _ as Hb0. eapply reach1_trans. reach1_step.
apply step_move. apply move_beside. right. split. apply brick_support. apply Hb0. apply (He 1). apply W.
eapply reach1_trans. reach1_step. eapply (step_destroy _ (_,_)). left. split. split. apply (He 0).
apply lt_0_succ. apply Hb0. apply brick_support. rewrite (ev_app1 Hy). rewrite nxt. rewrite nth_hd. split.
apply (len1 Hs). rewrite nxt. apply (set_app (len1 Hy) Hs). rewrite <- nxt. eapply reach1_trans.
eapply (movei (S s) 0 w). 3:constructor. intros z Hz. split. rewrite add_succ_r. apply (He (S z)).
apply Le.le_n_S. apply Hz. apply brick_support. rewrite (ev_app1 Hy). rewrite nxt.
replace (brick::_++r2) with (repeat brick (S w)++r2). erewrite app2. apply nth_repeat. apply (len1 Hs).
apply repeat_length. apply Hz. split. apply lt_0_succ. rewrite add_succ_r. apply (stripl s (S w) Hy). simpl.
exists (r1++[air]). eexists. repeat (rewrite <- nxt). repeat split. apply (len1 Hs). apply Hh. apply E.
rewrite (ev_app1 Hy). rewrite (nth_hd Hs). split. eenough _ as Hsp. eassert _ as Hwx1.
apply Minus.le_plus_minus_r. apply Le.le_S_n. apply Hx1. eassert (S(S w)=_) as Hwx. rewrite <- Hwx1. symmetry.
apply add_succ_l. eapply reach1_trans. eapply (movei s (S x) (S w)). 3: constructor. intros z Hz. split.
apply He. apply Hz. apply (Hsp z Hz). apply Hx. eapply reach1_trans. erewrite (_:S w+s=_).
eapply (stripl (x+s) (S w-x)). apply Hy. rewrite Hwx. rewrite repeat_app. rewrite <- app_assoc.
rewrite app_assoc. repeat eexists. rewrite app_length. rewrite repeat_length. rewrite Hs. rewrite add_comm.
apply add_succ_l. apply Hsp. eapply le_trans. 2:apply Hx. apply le_succ_diag_r. intros z Hz. rewrite add_assoc.
apply E. rewrite <- Hwx1. rewrite add_comm. rewrite <- add_succ_r. apply Plus.plus_lt_compat_l. apply Hz.
eapply reach1_trans. eapply (movei s x 0). 2:constructor. intros z Hz. split. apply He. eapply le_trans.
apply Hz. apply Hx1. rewrite <- app_assoc. apply brick_support. rewrite (ev_app1 Hy). erewrite (app2 Hs _ Hz).
apply nth_repeat. apply lt_0_succ. apply (stripr s (S x) Hy). rewrite Hwx. rewrite repeat_app.
repeat (rewrite <- app_assoc). repeat eexists. apply Hs. apply Hh. intros z Hz. apply E. eapply le_trans.
apply Hz. apply Hx. Unshelve. intros z Hz. apply brick_support. rewrite (ev_app1 Hy).
erewrite (app2 Hs (repeat_length _ _) Hz). apply nth_repeat. rewrite add_assoc. rewrite (add_comm _ x).
rewrite Hwx1. split. apply repeat_length. Qed.
End Drill.

Ltac display := lazymatch goal with
  | |- can_reach_any ?g ?p ?q =>
    let s := eval compute in (PP.print_tiles g) in idtac s end.
Lemma init g {p q}: can_reach_any g p q -> can_reach_pos g p q.
intros H. destruct (H []) as [d [h H1]]. repeat eexists. apply H1. Qed.
Ltac init := lazymatch goal with
  | |- can_reach_pos ?g _ _  => apply (init g) end.
Lemma helper {g p t q h}: reach1 (p,g) (q,h) -> can_reach_any h q t -> can_reach_any g p t.
intros H1 H2 d. epose proof (H1 d) as [e H3]. epose proof (H2 e) as [f [? H4]]. repeat eexists.
eapply rt_trans. apply H3. apply H4. Qed.
Ltac helper f := lazymatch goal with
  | |- can_reach_any ?g ?p _ => let H := fresh in (
    pose proof (f g p) as H; compute in H; apply (helper H); clear H) end.
Ltac mv q := helper (mv q).
Ltac dl r := helper (destroy r beside_right).
Ltac dr r := helper (destroy r beside_left).
Ltac drill q := helper (drill q).
Ltac strip s w h := helper (strip s w h).
Lemma done g p q: reachb g p q = true -> can_reach_any g p q.
intros H d. exists d. exists g. apply (reachb_correct _ H). Qed.
Ltac done := lazymatch goal with
  | |- can_reach_any ?g ?p ?q => apply (done g p q (Logic.eq_refl true)) end.
End Pos.

Fixpoint consec {A} P (l:list A) := match l with
  | a::((b::t) as m) => (P a b) /\ consec P m
  | _ => True end.
Definition hasfirst {A} P (l:list A):Prop := match l with | [] => False | a::_ => P a end.
Lemma consec1 {A P} {l m:list A}: consec P (l++m) -> consec P l /\ consec P m.
induction l. simpl. tauto. destruct l. destruct m; repeat split. apply (proj2 H). intros [G H]. repeat split;
tauto. Qed.
Lemma consec2 {A P l m} {a:A}: consec P (a::m) -> consec P (l++[a]) -> consec P (l++a::m).
destruct m. tauto. intros [H M]. induction l. intros _. apply (conj H M). destruct l. intros [G _]. split.
apply G. apply IHl. split. intros [G C]. split. apply G. apply IHl. apply C. Qed.

Module Neg.
Definition reach1 s p := exists t, can_reach s t /\ sp t = p.
Definition desc (P:state->Prop) s := forall t, can_reach s t -> P t.
Definition inv (P:state->Prop) := forall s t, step s t -> P s -> P t.
Definition rinv (P Q:state->Prop) := forall s t, step s t -> P s -> Q s -> Q t.
Lemma desc_inv {P}: inv (desc P).
intros s t H D u R. apply D. eapply rt_trans. eapply rt_step. apply H. apply R. Qed.
Lemma inv1 {P s t}: inv P -> can_reach s t -> P s -> P t. intros H R Ps. revert t R.
apply clos_refl_trans_ind_left. apply Ps. intros ? ? _ P1 Hs. apply (H _ _ Hs P1). Qed.
Definition frontier (P Q:state->Prop) := forall s t, step s t -> P s -> (P t \/ Q t).
Definition fronts s P Q := P s /\ frontier P Q.
Definition andp {A} P Q (a:A) := P a /\ Q a.
Definition orp {A} P Q (a:A) := P a \/ Q a.
Lemma refs {P Q R s}: rinv P R -> R s -> fronts s P Q -> fronts s (andp P R) (andp Q R).
intros I Rs [Ps F]. repeat split; try assumption. intros t u K [Pt Rt]. pose proof (I _ _ K Pt Rt).
pose proof (F _ _ K Pt). unfold andp. tauto. Qed.
Definition implp {A} (P Q:A->Prop) := forall a, P a -> Q a.
Lemma impl_rinv {P Q R}: rinv Q R -> implp P Q -> rinv P R.
intros QR I s t H Ps Rs. apply (QR s t H (I _ Ps) Rs). Qed.
Lemma fronts_reach {P Q s t}: fronts s P Q -> can_reach s t ->
  P t \/ exists u, can_reach s u /\ can_reach u t /\ Q u.
intros [Ps F]. revert t. apply clos_refl_trans_ind_left. tauto. intros t u ST [Pt|[v [SV [VT Qv]]]] TU.
destruct (F _ _ TU Pt) as [Pu|Qu]. tauto. right. exists u. repeat split. eapply rt_trans. apply ST.
apply rt_step. apply TU. apply rt_refl. tauto. right. exists v. repeat split; try assumption. eapply rt_trans.
apply VT. apply rt_step. apply TU. Qed.
Lemma applyf {P Q s p}: fronts s P Q -> reach1 s p -> exists t, can_reach s t /\ ((P t /\ sp t = p) \/
  (Q t /\ reach1 t p)).
intros F [t [R T]]. pose proof (fronts_reach F R) as [Pt|[u[SU[UT Qu]]]]. exists t. tauto. exists u.
assert (reach1 u p). exists t. all:tauto. Qed.

Inductive tilep := | is: tile -> tilep | qm.
Inductive tilem (destroyed:Prop): tilep -> tile -> Prop :=
  | matchis t: ~destroyed -> tilem destroyed (is t) t
  | matchb: ~destroyed -> tilem destroyed qm brick
  | matcha: destroyed -> tilem destroyed qm air.
Definition tilems t p s := (tilem (In p (sd s)) t (ev (sg s) p)).
Definition free s := is_empty (ev (sg s) (sp s)).
Definition validd s := NoDup (sd s) /\ forall p, In p (sd s) -> ev (sg s) p = air.
Definition evp := evg (is stone).
Definition gridm gp ps s := In (sp s) ps /\ (forall p, tilems (evp gp p) p s) /\ free s /\ validd s.
Lemma gridm_app g p q s: gridm g (p++q) s <-> gridm g p s \/ gridm g q s.
unfold gridm. rewrite in_app_iff. tauto. Qed.
Lemma grid_map_ev {A B} (f:A->B) g p a: evg (f a) (grid_map f g) p = f (evg a g p).
unfold evg. unfold grid_map. erewrite (_:[]=_). rewrite map_nth. apply map_nth. Unshelve. split. Qed.
Lemma init g p {q}: emptyb (ev g p) = true -> can_reach_pos g p q ->
  exists s, reach1 s q /\ (gridm (grid_map is g) [p] s).
intros E [d [h H]]. repeat eexists. apply H. split. left. split. intros r. unfold evp. rewrite grid_map_ev.
apply matchis. intros []. unfold free. rewrite empty_equiv. apply E. constructor. intros ? []. Qed.
Definition tilep_to_ascii t := match t with | is t => PP.tile_to_ascii t | _ => "?"%char end.
Definition print_gp gp := PP.print_grid (grid_map tilep_to_ascii gp).
Lemma notthere {g ps s p}: gridm g ps s -> sp s = p -> poss_mem p ps = false -> False.
intros [M] P. rewrite P in M. unfold poss_mem. rewrite ListSet.set_mem_correct2. apply Bool.diff_true_false.
apply M. Qed.

Ltac init := lazymatch goal with
  | |- ~can_reach_pos ?g ?p ?q  => let H := fresh in (
    intros H; apply (init g p (Logic.eq_refl _)) in H; destruct H as [? [? ?]]) end.
Ltac display := lazymatch goal with
  | [ _:reach1 ?s _ , _:gridm ?g ?ps ?s |- False ] =>
    let s := eval compute in (print_gp g) in idtac s; idtac ps end.
Ltac applyf := 
  let splitp := repeat (match goal with
    | [H:andp _ _ _ |- _] => destruct H as [??]
    | [H:orp _ _ _ |- _] => destruct H as [?|?] end) in
  let clears s := repeat (match goal with
    | [H:desc ?P s, R:can_reach s ?t |- _] => apply (inv1 desc_inv R) in H end); clear dependent s in
  let notthere := try (match goal with
    | [M:gridm _ ?ps ?s, P:(sp ?s) = ?q |- False] => apply (notthere M P (Logic.eq_refl false)) end) in
  lazymatch goal with
    | [R:reach1 ?s _, F:fronts ?s _ _ |- False] =>
      destruct (applyf F R) as [?[?[[??]|[??]]]]; clears s; splitp; notthere end.

Definition up (p:position) := match p with | (x,y) => (x,pred y) end.
Definition candestroy s p := snd p > 0 /\ beside (sp s) (up p) /\ supported (sg s) (sp s) /\
  is_empty (ev (sg s) (up p)).
Lemma candestroy1 {s pb} ps: beside (sp s) ps -> above ps pb -> supported (sg s) (sp s) ->
  is_empty (ev (sg s) ps) -> candestroy s pb.
unfold candestroy. destruct ps as [u v]. intros B A Q E. rewrite A. split. apply lt_0_succ. tauto. Qed.
Lemma setgneq {A p q g h} {a b:A}: setg p a b g h -> p <> q -> evg a h q = evg a g q.
intros H P. destruct (proj2 H q) as [E|E]. symmetry in E. destruct (P E). apply E. Qed.
Lemma setneq {p q t g h}: set p t g h -> p <> q -> ev h q = ev g q.
intros H P. destruct (proj2 H q) as [E|E]. symmetry in E. destruct (P E). apply E. Qed.
Lemma stepev {s t} p: step s t -> (ev (sg t) p = ev (sg s) p /\ (In p (sd s) <-> In p (sd t))) \/
  (ev (sg t) p = brick /\ (sp s) <> p /\ sd s = (sd t)++[p]) \/
  (ev (sg s) p = brick /\ ev (sg t) p = air /\ candestroy s p /\ sd t = p::sd s).
intros H. inversion H; simpl. tauto. destruct (PosDec.eq_dec pb p) as [E|E]; unfold PosDec.eq in E. right. right.
rewrite <- E. apply proj1 in H5. set (candestroy _ _) as C. enough C. tauto. apply (candestroy1 ps); assumption.
rewrite (setneq H5 E). tauto. destruct (PosDec.eq_dec q p) as [E|E]; unfold PosDec.eq in E. right. left.
rewrite <- E. repeat split; try tauto. apply (proj1 H1). rewrite (setneq H1 E). rewrite in_app_iff. simpl. tauto.
Qed.
Lemma solidinv {s t p}: step s t -> is_solid (ev (sg s) p) -> is_solid (ev (sg t) p) \/
  (candestroy s p /\ sd t = p::sd s).
intros H B. destruct (stepev p H) as [[E _]|[[E _]|E]]; try (rewrite E). 2:unfold is_solid. all:tauto. Qed.
Lemma steppos {s t}: step s t -> (move (sg s) (sp s) (sp t) /\ free t /\ sg t = sg s /\ sd t = sd s) \/
  sp t = sp s. intros H. inversion H; tauto. Qed.
Lemma freeinv: inv free.
unfold free. intros s t H F. destruct (steppos H) as [[_ [G]]|P]. tauto. rewrite P. destruct (stepev (sp s) H)
as [[E]|[[_[E]]|[_[E]]]]; try rewrite E. tauto. destruct E. split. apply air_empty. Qed.
Lemma validdinv: inv validd.
unfold validd. intros [? ? ?] t H. inversion H; simpl; intros [D A]. tauto. split. constructor. intros E.
apply (A _) in E. rewrite E in H6. inversion H6. apply D. intros q [Q|Q]. rewrite <- Q. apply (proj1 H9).
destruct (proj2 H9 q) as [E|E]. rewrite E. apply (proj1 H9). rewrite E. apply (A _ Q). apply NoDup_remove in D.
rewrite app_nil_r in D. split. tauto. intros r R. destruct (proj2 H5 r) as [E|E]. rewrite E in R. tauto.
rewrite E. apply A. rewrite in_app_iff. tauto. Qed.
Lemma tilem_iff {P Q tp t} (H:P <-> Q): tilem P tp t -> tilem Q tp t.
intros M. inversion M; constructor; tauto. Qed.
Lemma qminv {p}: rinv validd (tilems qm p).
unfold tilems. intros s t H [V] M. destruct (stepev p H) as [[E D]|[[E[_ D]]|[_[E[_ D]]]]]; rewrite E.
apply (tilem_iff D M). rewrite D in V. apply NoDup_remove in V. rewrite app_nil_r in V. apply matchb. tauto.
apply matcha. rewrite D. left. split. Qed.

Section Expand.
Definition emptybp t := match t  with | is t => emptyb t | _ => true end.
Definition supportingbp t := match t  with | is t => supportingb t | _ => true end.
Definition holdablebp t := match t with | is t => holdableb t | _ => false end.
Definition supportedbp g p := ((holdablebp (evp g p)) || (supportingbp (evp g (below p))))%bool.
Definition brickbp t := match t with | is brick => true | _ => false end.
Definition ladderbp t := match t with | is ladder => true | _ => false end.
Definition qmbp t := match t with | qm => true | _ => false end.
Definition notholdableb t := negb (holdablebp t).
Definition adj p q := match (p,q) with | ((x,y),(z,w)) =>
  (((x=?z)&&((y=?S w)||(w=?S y)))||((y=?w)&&((z=?S x)||(x=?S z))))%bool end.

Definition ft pr g l := filter (fun p => pr (evp g p)) l.
Definition fe := ft emptybp.
Definition prenh g p := if supportedbp g p then (S(fst p),snd p)::(
  if 0<?fst p then [(pred(fst p),snd p)] else []) else [].
Definition prenv g p := (below p)::(if (ladderbp (evp g p)&&(0<?snd p))%bool then [(fst p,pred(snd p))] else []).
Definition neighbors g p := let (nh,nv) := (fe g (prenh g p),fe g (prenv g p)) in
  let d := ft brickbp g (map below nh) in (d,nh++nv).
Definition destroyall g l := fold_right (fun p h => replaceg p qm h) g l.
Definition expand_step b goc := match goc with
  | (g,[],c) => (goc,Some (g,c))
  | (g,p::o,c) => if poss_mem p b then (g,o,c,None) else let (d,n) := neighbors g p in
    let (c1,c2) := partition (fun q => existsb (adj q) d) c in
    (destroyall g d, poss_union (poss_diff (n++c1) c2) o, p::c2,None) end.
Definition expand g ps b := while (expand_step b) (g,ps,[]) (5*(grid_size g)).

Definition from (p:position) (l:list position) := map (fun q => (p,q)) l.
Definition expand_step1 b db gocl := match gocl with
  | (g,[],c,l) => (gocl,Some (g,c,l))
  | (g,p::o,c,l) => if poss_mem p b then (g,o,c,l,None) else let (d,n) := neighbors g p in
    let (d1,d2) := partition (fun q => poss_mem q db) d in
    let (c1,c2) := partition (fun q => existsb (adj q) d2) c in
    (destroyall g d2, poss_union (poss_diff (n++c1) c2) o, p::c2,(from p d1)++l,None) end.
Definition expand1 g ps b db := while (expand_step1 b db) (g,ps,[],[]) (5*(grid_size g)).

Lemma emptym {P t tp}: is_empty t -> tilem P tp t -> emptybp tp = true.
intros H M. inversion M. rewrite empty_equiv in H. apply H. all:split. Qed.
Lemma supportingm {P t tp}: is_supporting t -> tilem P tp t -> supportingbp tp = true.
intros H M. inversion M. rewrite supporting_equiv in H. apply H. all:split. Qed.
Lemma holdablem {P t tp}: is_holdable t -> tilem P tp t -> holdablebp tp = true.
intros H M. rewrite holdable_equiv in H. inversion M. apply H. all:rewrite <- H2 in H; inversion H. Qed.
Lemma supportedm {ps gp s p}: supported (sg s) p -> gridm gp ps s -> supportedbp gp p = true.
unfold supportedbp. intros [H|H] [_ [M]]. rewrite (holdablem H (M _)). split. rewrite (supportingm H (M _)).
apply Bool.orb_true_r. Qed.
Lemma ladderm {ps gp s p}: ev (sg s) p = ladder -> gridm gp ps s -> ladderbp (evp gp p) = true.
intros H [_ [M]]. pose proof (M p) as P. unfold tilems in P. rewrite H in P. inversion P. split. Qed.
Lemma brickbp_equiv {t}: brickbp t = true <-> t = is brick.
destruct t. destruct t0. 3:tauto. all:simpl; split; intros H; inversion H. Qed.
Lemma notholdable_suff {g ps s p}: gridm g ps s -> notholdableb (evp g p) = true -> ~is_holdable (ev (sg s) p).
intros [_[M _]] T H. apply Bool.diff_true_false. rewrite <- T. unfold notholdableb. rewrite Bool.negb_false_iff.
eapply (holdablem H). apply M. Qed.

Lemma destroyall_evp {g l}: (forall p, In p l -> evp g p = is brick) -> forall p, evp (destroyall g l) p =
  if (poss_mem p l) then qm else evp g p.
unfold destroyall. unfold evp. induction l. split. simpl. intros B p. epose proof (IHl _) as IH.
epose proof replace_set as [R|R]. rewrite IH in R. rewrite B in R. destruct (poss_mem _ _) in R; inversion R.
left. split. destruct (_ p a) as [E|E]. rewrite E. apply (proj1 R). destruct (proj2 R p) as [P|P].
destruct (E P). rewrite P. apply IH. Unshelve. intros q Q. apply B. tauto. Qed.
Lemma prenh_beside {g p q}: In q (prenh g p) -> beside p q.
unfold prenh. destruct (_:bool). intros [H|H]. right. rewrite <- H. destruct p; split. destruct p as [[|x] y].
destruct H. destruct H as [H|[]]. rewrite <- H. left. split. intros []. Qed.
Lemma pren_adj g {p q}: In q (prenh g p) \/ In q (prenv g p) -> adj p q = true.
unfold adj. unfold prenv. intros [H|[H|H]]. destruct (prenh_beside H) as [E|E]; rewrite E.
destruct q. 2:destruct p. 3:rewrite <- H; destruct p. 4:destruct (_:bool) eqn:E in H. 4:destruct H as [H|[]];
rewrite <- H; destruct p as [x [|y]]. all:simpl;repeat (rewrite eqb_refl); repeat (rewrite Bool.orb_true_r);
try split. rewrite Bool.andb_false_r in E. inversion E. destruct H as []. Qed.

Section Destroy.
Context {g:grid tilep} {p:position} {d d2:list position} {n:list position}.
Hypothesis E: neighbors g p = (d,n).
Hypothesis D: incl d2 d.
Notation h := (destroyall g d2).
Lemma dbrick q: In q d2 -> evp g q = is brick.
intros I. apply D in I. revert I. unfold neighbors in E. inversion E. unfold ft. rewrite filter_In. intros [_ H].
destruct (evp g q) as [t|]. destruct t. 3:split. all:inversion H. Qed.
Lemma evph {q}: (In q d2 /\ evp g q = is brick /\ evp h q = qm) \/ evp h q = evp g q.
unfold h. rewrite (destroyall_evp dbrick). destruct (poss_mem q d2) eqn:M. apply ListSet.set_mem_correct1 in M.
left. repeat split. apply M. apply (dbrick _ M). right. split. Qed.
Lemma dpren {pr q}: pr = prenh \/ pr = prenv -> pr h q = pr g q.
intros [P|P]; rewrite P. unfold prenh. unfold supportedbp. erewrite (_:holdablebp _=_).
erewrite (_:supportingbp _=_). split. unfold prenv. unfold ladderbp. epose proof evph as [[_ [G H]]|H];
rewrite H; try (rewrite G); split. Unshelve. all:epose proof evph as [[_ [G H]]|H]; rewrite H; try (rewrite G);
split. Qed.
Lemma dempty q: ~In q d2 -> emptybp (evp h q) = emptybp (evp g q).
intros Q. epose proof evph as [[H _]|H]. destruct (Q H). rewrite H. split. Qed.
Definition notdadj q := forall r, In r d2 -> adj q r = false.
Lemma dadj: notdadj p.
assert (forall n, n=?S n=false) as F. intros x. rewrite eqb_neq. apply n_Sn. intros r I. apply D in I. revert I.
unfold neighbors in E. inversion E. unfold ft. intros H. apply incl_filter in H. rewrite in_map_iff in H.
destruct H as [q [R Q]]. rewrite <- R. unfold fe in Q. apply incl_filter in Q. unfold adj. unfold below.
destruct (prenh_beside Q) as [B|B]; rewrite B; [destruct q;rewrite eqb_sym|destruct p]; repeat (rewrite F);
split. Qed. 
Lemma fgh {pr q}: notdadj q -> pr = prenh \/ pr = prenv -> fe h (pr h q) = fe g (pr g q).
intros R P. rewrite (dpren P). unfold fe. unfold ft. apply filter_ext_in. intros a A. apply dempty. intros I.
apply R in I. erewrite (pren_adj g) in I. inversion I. destruct P as [P|P]; rewrite <- P; tauto. Qed.
Lemma ngh {q e d1 m}: neighbors g q = (e,m) -> notdadj q -> incl e (d1++d2) -> exists e1, incl e1 d1 /\
  neighbors h q = (e1,m).
unfold neighbors. intros P Q I. repeat (rewrite (fgh Q)). rewrite pair_equal_spec in P. rewrite (proj2 P).
eexists. repeat split. unfold ft. intros r. rewrite filter_In. rewrite (destroyall_evp dbrick r).
destruct (poss_mem _ _) eqn:M. intros [_ H]. inversion H. apply ListSet.set_mem_complete1 in M. intros [R B].
assert (In r e) as K. rewrite <- (proj1 P). unfold ft. rewrite filter_In. tauto. apply I in K.
rewrite in_app_iff in K. all:tauto. Qed.
Lemma np {d1}: incl d (d1++d2) -> exists e, incl e d1 /\ neighbors h p = (e,n). apply (ngh E dadj). Qed.
End Destroy.
Lemma oc_incl d c {p n o b}: let (c1,c2) := partition (fun q => existsb (adj q) d) c in
  incl (n++p::o++c++b) (poss_union (poss_diff (n++c1) c2) o++(p::c2)++b).
destruct (partition _ _) as [c1 c2] eqn:C. intros q. repeat (rewrite in_app_iff). unfold poss_union.
rewrite ListSet.set_union_iff. simpl. unfold poss_diff. rewrite ListSet.set_diff_iff.
repeat (rewrite in_app_iff). rewrite (elements_in_partition _ _ C). assert (In q c2\/~In q c2).
destruct (poss_mem q c2) eqn:H. apply ListSet.set_mem_correct1 in H. 2: apply ListSet.set_mem_complete1 in H.
all:tauto. Qed.
Lemma part_incl {A d d1 d2} {f:A->bool}: partition f d = (d1,d2) -> incl d (d1++d2) /\ incl d2 d.
intros H. split; intros a; pose proof (elements_in_partition _ _ H a); try rewrite (in_app_iff); tauto. Qed.
Lemma from_incl {p d e}: incl d e -> incl (from p d) (from p e).
intros I pq. unfold from. repeat (rewrite in_map_iff). intros [q[P Q]]. apply I in Q. exists q. tauto. Qed.
Lemma partf {A f} {l:list A}: let (_,m) := partition f l in forall a, In a m -> f a = false.
induction l. intros _ [].  simpl. destruct (partition f l). destruct (f a) eqn:F. apply IHl. intros x [X|X].
rewrite <- X. apply F. apply (IHl _ X). Qed.
Lemma existsb_false {A f} {l:list A}: existsb f l = false -> forall a, In a l -> f a = false.
induction l. intros _ ? []. simpl. rewrite Bool.orb_false_iff. intros [F H] b [B|B]. rewrite <- B. apply F.
apply (IHl H _ B). Qed.
Definition hasn b gocl := match gocl with | (g,o,c,l) => forall p, In p c -> let (d,n) := neighbors g p in
  incl n (o++c++b) /\ incl (from p d) l end.
Lemma hasninv b db gocl: hasn b gocl -> hasn b (fst (expand_step1 b db gocl)).
unfold expand_step1. destruct gocl as [[[g [|r o]] c] l]. tauto. destruct (poss_mem r b) eqn:M.
intros H p Hp. pose proof (H p Hp) as G. destruct (neighbors _ _) as [d n]. split. intros q Hq.
destruct (proj1 G q Hq) as [I|I]. rewrite app_assoc. apply in_or_app. right. eapply ListSet.set_mem_correct1.
rewrite <- I. apply M. apply I. apply (proj2 G). destruct (neighbors _ _) as [d n] eqn:N.
destruct (partition _ _) as [d1 d2] eqn:D. apply part_incl in D. epose proof (oc_incl d2 c) as I.
destruct (partition _ _) as [c1 c2] eqn:C. intros H p [Hp|Hp]. rewrite <- Hp.
pose proof (np N (proj2 D) (proj1 D)) as [e[E N1]]. rewrite N1. split. eapply incl_tran. apply incl_appl.
apply incl_refl. apply I. apply incl_appl. apply (from_incl E). epose proof (H p _) as G.
destruct (neighbors g p) as [e m] eqn:N1. epose proof (ngh N (proj2 D) N1 _ (incl_appl _ _)) as [e1[E N2]].
rewrite N2. split. eapply incl_tran. apply incl_appr. apply (proj1 G). apply I. apply incl_appr.
eapply incl_tran. apply (from_incl E). apply (proj2 G). Unshelve. apply part_incl in C. apply (proj2 C _ Hp).
unfold notdadj. apply existsb_false. epose proof partf as P. rewrite C in P. apply (P _ Hp). apply incl_refl.
Qed.

Lemma prenh_suff {g ps p q s}: gridm g ps s -> beside p q -> supported (sg s) p -> In q (prenh g p).
intros M B H. unfold prenh. rewrite (supportedm H M). destruct B as [E|E]; rewrite E. destruct q. right. left.
split. destruct p. left. split. Qed.
Lemma pren_suff {g ps p q s}: gridm g ps s -> move (sg s) p q -> In q (prenh g p ++ prenv g p).
rewrite in_app_iff. intros M H. inversion H. 1,2:right. rewrite H0. left. split. unfold prenv.
rewrite (ladderm H1 M). rewrite H0. destruct q. right. left. split. left. apply (prenh_suff M H0 H1). Qed.
Definition justdestroyed g p q s := gridm (replaceg q qm g) [p] s /\ candestroy s q /\ is_empty(ev (sg s) q).
Definition jdl g l s := exists p q, In (p,q) l /\ justdestroyed g p q s.
Lemma tilemqm {P tp t}: tilem P tp t -> P -> tp = qm. intros M H. inversion M; tauto. Qed.
Lemma tilemb {P tp t}: t = brick -> tilem P tp t -> tp = is brick \/ tp = qm.
intros H M. rewrite H in M. inversion M; tauto. Qed.
Lemma right_irrefl {p}: ~right p p. destruct p as [x y]. intros P. inversion P. eapply n_Sn. apply H0. Qed.
Lemma beside_irrefl {p}: ~beside p p. intros [P|P]; apply (right_irrefl P). Qed.
Lemma besidey {p q}: beside p q -> snd p = snd q.
intros [E|E]; rewrite E. destruct q as [? ?]. split. destruct p as [? ?]. split. Qed.
Lemma upbelow {p}: up(below p) = p. destruct p; split. Qed.
Lemma setgeq {A p g} {a:A}: setg p a (evg a g p) g g. repeat split. intros q. tauto. Qed.
Lemma tilemsset {p a b g h s t}: (forall q, tilems (evp g q) q s) -> setg p (is stone) a g h ->
  set p b (sg s) (sg t) -> (forall q, p<>q -> (In q (sd s) <-> In q (sd t))) ->
  tilem (In p (sd t)) a b -> forall q, tilems (evp h q) q t.
intros T H L I P q. unfold tilems. unfold evp. destruct (PosDec.eq_dec p q) as [E|E]; unfold PosDec.eq in E.
rewrite <- E. rewrite (proj1 H). rewrite (proj1 L). apply P. rewrite (setgneq H E). rewrite (setneq L E).
eapply tilem_iff. apply (I q E). apply T. Qed.
Lemma nsuff {g p d n}: neighbors g p = (d,n) -> frontier (gridm g [p]) (orp (gridm g n) (jdl g (from p d))).
unfold neighbors. unfold fe. unfold ft. rewrite <- filter_app. rewrite pair_equal_spec.
intros [D N] [???] t H M. pose proof M as [[P|[]] [T [F V]]]. unfold tilems in T. apply (freeinv _ _ H) in F.
apply (validdinv _ _ H) in V. inversion H. right. left. assert (In q n). rewrite <- N. rewrite filter_In.
split. rewrite P. apply (pren_suff M H4). apply (emptym H5 (T _)). unfold gridm. unfold tilems. simpl.
rewrite H2. tauto. pose proof (tilemb H6 (T _)) as [G|G]. right. right. exists p. exists pb. split. unfold from.
rewrite in_map_iff. eexists. repeat split. rewrite <- D. rewrite filter_In. split. rewrite in_map_iff.
exists ps. rewrite H4. repeat split. rewrite filter_In. split. rewrite P. apply (prenh_suff M H3 H8).
apply (emptym H5 (T _)). rewrite G. split. split. split. simpl. tauto. split. epose proof replace_set as [R|R].
assert (is brick=is stone) as X. rewrite <- G. apply R. inversion X. eapply (tilemsset T R). apply H9. simpl.
tauto. apply matcha. simpl. tauto. rewrite H7. tauto. split. set (_:state) as s in H.
assert (candestroy s pb) as X. apply (candestroy1 ps); simpl; tauto. unfold candestroy. unfold supported. simpl.
repeat (erewrite (setneq H9)). apply X. 1,2,3:rewrite H4. 1,3:destruct ps as [? v]; intros E; apply (n_Sn v).
symmetry. apply (f_equal (@snd _ _) E). rewrite <- E in H3. apply besidey in H3. symmetry. apply H3.
intros E. apply (f_equal up) in E. repeat (rewrite upbelow in E). rewrite E in H3. apply (beside_irrefl H3).
simpl. rewrite (proj1 H9). apply air_empty. left. split. simpl. tauto. split. eapply (tilemsset T setgeq).
apply H9. simpl. tauto. fold evp. rewrite G. apply matcha. simpl. tauto. rewrite H7. tauto. left. split. simpl.
tauto. split. eapply (tilemsset T setgeq). apply H5. rewrite <- H3. intros ?. simpl. rewrite in_app_iff. simpl.
tauto. fold evp. rewrite (tilemqm (T q)). apply matchb. rewrite <- H2 in V. intros X. apply (proj2 V _) in X.
simpl in X. rewrite (proj1 H5) in X. inversion X. rewrite <- H3. simpl. rewrite in_app_iff. simpl. tauto.
rewrite H2. tauto. Qed.

Definition gridme {L} s (gocl:(_*L)) := match gocl with | (g,o,c,_) => gridm g (o++c) s end.
Lemma gridmeinv b db s (B:~In (sp s) b) gocl: gridme s gocl -> gridme s (fst (expand_step1 b db gocl)).
destruct gocl as [[[g [|r o]] c] ?]. unfold expand_step1. tauto. destruct s as [p h d]. unfold gridme.
intros [P [T [F V]]]. unfold expand_step1. destruct (poss_mem r b) eqn:M. simpl. destruct P as [P|P].
destruct B. rewrite <- P. eapply ListSet.set_mem_correct1. apply M. unfold gridm. tauto.
destruct (neighbors g r) as [e n] eqn:N. destruct (partition _ _) as [d1 d2] eqn:D. apply part_incl in D.
epose proof (oc_incl d2 c) as I. destruct (partition _ _) as [c1 c2]. simpl. split.
repeat (rewrite app_nil_r in I). eapply incl_tran. 2:apply I. apply incl_appr. apply incl_refl. apply P. split.
unfold tilems. unfold tilems in T. intros q. simpl. pose proof (T q) as Q. simpl in Q.
epose proof (evph N (proj2 D)) as [[_ [G H]]|G]. rewrite G in Q. inversion Q. rewrite H. apply matchb. apply H2.
rewrite G. apply Q. tauto. Qed.

Lemma expandterm {gocl h qs l b db}: snd(expand_step1 b db gocl)=Some (h, qs, l) -> gocl = (h,[],qs,l).
unfold expand_step1. destruct gocl as [[[g [|r o]] c] ?]. 2:destruct (poss_mem r b). 3:destruct (neighbors _ _);
repeat (destruct (partition _ _)). all:intros H; inversion H. split. Qed.
Lemma gridm_incl {g ps qs s}: incl ps qs -> gridm g ps s -> gridm g qs s.
intros H. pose proof (H (sp s)). unfold gridm. tauto. Qed.
Lemma orpassoc {g p q s P}: gridm g p s \/ (orp (gridm g q) P s) <-> gridm g (p++q) s \/ P s.
unfold orp. rewrite gridm_app. tauto. Qed.
Theorem expandsuff1 {g ps s} h qs l b db: gridm g ps s -> poss_inter ps b = [] ->
  expand1 g ps b db = Some (h, qs, l) -> fronts s (gridm h qs) (orp (gridm h b) (jdl h l)).
intros G P H. split. epose proof (while_inv (gridmeinv b db s _) _ H) as [c [C T]]. apply expandterm in T.
rewrite T in C. apply C. epose proof (while_inv (hasninv b db) _ H) as [c [C T]]. apply expandterm in T.
rewrite T in C. intros t u TU M. rewrite orpassoc. pose proof (proj1 M) as Q. pose proof (C (sp t) Q) as CT.
destruct (neighbors h _) as [d n] eqn:N. apply nsuff in N. epose proof (N _ _ TU _) as K.
rewrite orpassoc in K. destruct K as [K|K]. left. eapply gridm_incl. 2:apply K. intros r [R|R]. rewrite <- R.
rewrite in_app_iff. tauto. apply (proj1 CT). apply R. right. destruct K as [p[q[V W]]]. exists p. exists q.
apply (proj2 CT) in V. tauto. Unshelve. intros I. eassert (In _ []) as []. rewrite <- P.
apply ListSet.set_inter_intro. apply (proj1 G). apply I. unfold gridme. rewrite app_nil_r. apply G. intros ? [].
split. simpl. tauto. apply (proj2 M). Qed.
Lemma jdlsplit {g p q l s}: jdl g ((p,q)::l) s -> justdestroyed g p q s \/ jdl g l s.
intros [?[?[[E|E]D]]]. inversion E. tauto. right. eexists. eexists. apply (conj E D). Qed.
Lemma jdlnil {g s}: ~jdl g [] s. intros [?[?[[]]]]. Qed.
Lemma standing {s q g p}: candestroy s q -> gridm g [p] s ->
  ((notholdableb (evp g p)&&qmbp(evp g (below p)))%bool=true) ->
  is_solid (ev (sg s) (below p)) /\ is_empty (ev (sg s) (up q)).
rewrite Bool.andb_true_iff. intros [_[_[H E]]] M [F Q]. pose proof M as [[P|[]] [T _]]. rewrite <- P in H. split.
destruct H as [H|[H|H]]. destruct (notholdable_suff M F H). tauto. pose proof (T(below p)) as K.
unfold tilems in K. rewrite H in K. inversion K. rewrite <- H0 in Q. inversion Q. apply E. Qed.

Lemma part_allf {A f} {l:list A}: (forall a, f a = false) -> partition f l = ([],l).
intros H. induction l. split. simpl. rewrite IHl. rewrite H. split. Qed.
Lemma stepequiv {b goc}: expand_step1 b [] (goc,[]) = let (goc1,res) := expand_step b goc in
  ((goc1,[]),option_map (fun x => (x,[])) res).
unfold expand_step1. unfold expand_step. destruct goc as [[g [|p o]]c]. split. destruct (poss_mem _ _). split.
destruct (neighbors _ _). rewrite part_allf. destruct (partition _ _). split. split. Qed.
Lemma whileequiv {b goc n}: while (expand_step1 b []) (goc,[]) n =
  option_map (fun x => (x,[])) (while (expand_step b) goc n).
revert goc. induction n. split. intros goc. unfold while. rewrite stepequiv. destruct (expand_step b goc) as
[goc1 [res|]]; simpl. split. apply IHn. Qed.
Theorem expandsuff {g ps s} h qs b: gridm g ps s -> poss_inter ps b = [] ->
  expand g ps b = Some (h, qs) -> fronts s (gridm h qs) (gridm h b).
unfold expand. intros M I E. epose proof (expandsuff1 h qs [] b [] M I _) as [H F]. split. apply H.
intros t u U T. destruct (F t u U T) as [?|[?|[?[?[[]]]]]]; tauto. Unshelve. unfold expand1. rewrite whileequiv.
rewrite E. split. Qed.
End Expand.
Ltac untilf b := lazymatch goal with
  | [ _:reach1 ?s _ , M:gridm ?g ?ps ?s |- False ] =>
    lazymatch eval compute in (expand g ps b) with
      | Some (?h,?qs) => pose proof (expandsuff h qs b M (Logic.eq_refl _) (Logic.eq_refl _)) end end.
Ltac splitapp := repeat (lazymatch goal with
    | [H:gridm _ (_++_) _ |- _] => rewrite gridm_app in H; destruct H as [?|?] end).
Ltac until b := untilf b; applyf; splitapp.
Ltac until1 b db := let applydestroy := try (lazymatch goal with
    | [D:candestroy ?s ?q, M:gridm ?g [?p] ?s |- _] => let H := fresh in let K := fresh in
      pose proof (standing D M (Logic.eq_refl _)) as [H K]; simpl in H; simpl in K end) in
  let jdls := repeat (lazymatch goal with
    | [H:jdl _ (_::_) _ |- _] => apply jdlsplit in H; destruct H as [[?[??]]|?]; [applydestroy|idtac]
    | [H:jdl _ [] _ |- False] => apply (jdlnil H) end) in
  lazymatch goal with | [ _:reach1 ?s _ , M:gridm ?g ?ps ?s |- False ] =>
    lazymatch eval compute in (expand1 g ps b db) with | Some (?h,?qs,?l) =>
      pose proof (expandsuff1 h qs l b db M (Logic.eq_refl _) (Logic.eq_refl _)); applyf; jdls
end end.
Ltac stuck := until (@nil position); lazymatch goal with
  | [M:gridm _ [] ?s |- _] => destruct M as [[]] end.

Section Strip.
Definition hassolid d s := exists p, In p d /\ is_solid (ev (sg s) p).
Definition row x (y:nat) w := map (fun u => (u,y)) (seq x w).
Lemma plusin {x w} u: u < w -> x <= u+x < w+x.
intros W. split. apply Plus.le_plus_r. apply Plus.plus_lt_compat_r. apply W. Qed.
Lemma int_in {x w u}: x<=u<w+x <-> exists v, v<w /\ u=v+x.
split. intros [L R]. exists (u-x). rewrite <- (add_sub w x). rewrite <- lt_add_lt_sub_r. rewrite (sub_add _ _ L).
tauto. intros [v [W E]]. rewrite E. apply (plusin _ W). Qed.
Lemma int0 {x u}: ~(x<=u<x). intros [L R]. eapply lt_irrefl. eapply le_trans. apply R. apply L. Qed.
Lemma int1 {x u}: x<=u<S x -> u=x. intros [L R]. inversion R. split. destruct (int0 (conj L H0)). Qed.
Lemma row_in {x y w p}: In p (row x y w) <-> exists u, u<w /\ p=(u+x,y).
unfold row. rewrite in_map_iff. split. intros [u [P I]]. revert I. rewrite in_seq. rewrite add_comm.
rewrite int_in. intros [v [W X]]. rewrite X in P. exists v. symmetry in P. tauto. intros [u [W P]]. rewrite P.
exists (u+x). repeat split. rewrite in_seq. rewrite (add_comm x w). rewrite int_in. exists u. tauto. Qed.
Definition walled x y w g := is_solid (ev g (w+x,y)) /\
  match x with | 0 => True | S x => is_solid (ev g (x,y)) end.
Definition inbox x y w h p := match p with | (u,v) => x<=u<w+x /\ y<=v<h+y end.
Definition nohold x y w h s := forall p, inbox x y w h p -> ~is_holdable (ev (sg s) p).
Definition hasstrip x y w s := walled x y w (sg s) /\ nohold x y w 2 s /\ free s.

Definition walledin {x y w p q g}: In p (row x y w) -> beside q p -> walled x y w g ->
  In q (row x y w) \/ is_solid (ev g q).
repeat (rewrite row_in). unfold walled. intros [u [W P]]. rewrite P. intros [B|B]. inversion W. rewrite B.
tauto. intros _. left. exists (S u). split. apply Le.le_n_S. 1,2:assumption. destruct q as [v z].
destruct u as [|u]; inversion B. tauto. intros _. left. eexists. repeat split. eapply Le.le_trans.
apply le_succ_diag_r. apply W. Qed.
Lemma rowbox {x y w h p} z: In p (row x (z+y) w) -> z<h -> inbox x y w h p.
rewrite row_in. intros [u [W P]] H. rewrite P. split. apply (plusin _ W). apply (plusin _ H). Qed.
Lemma rowup {x y w p}: In p (row x (S y) w) -> In (up p) (row x y w).
repeat (rewrite row_in). intros [u [W P]]. rewrite P. exists u. tauto. Qed.
Lemma rowdown {x y w p}: In p (row x y w) -> In (below p) (row x (S y) w).
repeat (rewrite row_in). intros [u [W P]]. rewrite P. exists u. tauto. Qed.
Lemma stripf {x y w}: rinv (hasstrip x y w) (hassolid (row x (S y) w)).
intros [p g d] t T [W [H E]]. intros [q [Q B]]. destruct (solidinv T B) as [F|[[_[F[G]]]]]. exists q. tauto.
destruct (walledin (rowup Q) F W) as [P|P]. destruct G as [G|[G|G]]. destruct (H p). apply (rowbox 0 P).
apply lt_0_succ. apply G. eexists. split. apply (rowdown P). destruct (solidinv T G) as [K|[[_[K]]]]. apply K.
destruct p as [u v]; destruct (beside_irrefl K). destruct (H (below p)). apply (rowbox 1 (rowdown P)).
apply le_refl. left. apply G. destruct (E P). Qed.

Definition rowfb x w f r := match splitn x r with | None => false | Some (r1,r2) =>
  match splitn w r2 with | None => false | Some (r3,r4) =>
    (negb(emptybp (last r1 (is stone))||emptybp (hd (is stone) r4)) && forallb f r3)%bool end end.
Definition noholdb x w r := match splitn x r with | None => false | Some (r1,r2) =>
  match splitn w r2 with | None => false | Some (r3,r4) => forallb notholdableb r3 end end.
Definition hasbrickb x w r := match splitn x r with | None => false | Some (r1,r2) =>
  match splitn w r2 with | None => false | Some (r3,r4) => existsb brickbp r3 end end.
Definition stripb x y w g := match splitn y g with | Some (_,r1::r2::_) =>
  ((rowfb x w notholdableb r1)&&(noholdb x w r2))%bool
  | _ => false end.
Definition strip x y w g ps := let r := row x (S y) w in match expand g ps r with
  | None => None | Some (h, qs) =>
    if ((hasbrickb x w (nth (S y) g []))&&(stripb x y w h)&&(length(poss_inter ps r)=?0))%bool then
    Some (h, qs) else None end.

Lemma nth_last {A n l} {d:A}: length l = S n -> nth n l d = last l d.
revert n. induction l; intros n H. inversion H. simpl in H. apply (f_equal pred) in H. simpl in H. destruct n;
destruct l. 2,3:inversion H. split. apply IHl. apply H. Qed.
Lemma emptybp_false {g ps s p}: gridm g ps s -> emptybp (evp g p) = false -> is_solid (ev (sg s) p).
intros [_[M]] E. epose proof empty_dec as [K|K]. 2:apply K. rewrite (emptym K (M _)) in E. inversion E. Qed.
Lemma rowfb_suff {x y w f g ps s}: gridm g ps s -> rowfb x w f (nth y g []) = true ->
  walled x y w (sg s) /\ (forall u, x<=u<w+x -> f (evp g (u,y)) = true).
intros M. unfold rowfb. destruct (splitn _ _) as [[r1 r2]|] eqn:E. apply splitn_app in E.
destruct (splitn _ _) as [[r3 r4]|] eqn:F. apply splitn_app in F. rewrite Bool.andb_true_iff.
rewrite Bool.negb_true_iff. rewrite Bool.orb_false_iff. rewrite forallb_forall. intros [[R L] T].
eassert (forall u,evp g (u,y)=_) as G. intros u. unfold evp. unfold evg. simpl. rewrite (proj2 E).
rewrite (proj2 F). split. repeat split. apply (emptybp_false M). rewrite G. rewrite (app1 (proj1 E)).
rewrite (app1 (proj1 F) 0). erewrite (_:nth 0 _ _=_). apply L. destruct x. split. apply (emptybp_false M).
rewrite G. rewrite app_nth1. rewrite (nth_last (proj1 E)). apply R. rewrite (proj1 E). apply le_refl. intros u.
rewrite int_in. intros [v [V U]]. rewrite U. rewrite G. rewrite (app1 (proj1 E)). rewrite <- (proj1 F) in V.
rewrite app_nth1. apply T. apply nth_In. 1,2:apply V. all:intros H; inversion H. Unshelve. destruct r4; split.
Qed.
Lemma noholdb_suff {x w r d}: noholdb x w r = true -> forall u, x<=u<w+x -> notholdableb(nth u r d)=true.
unfold noholdb. destruct (splitn _ _) as [[r1 r2]|] eqn:E. apply splitn_app in E.
destruct (splitn _ _) as [[r3 r4]|] eqn:F. apply splitn_app in F. intros H u U. rewrite int_in in U.
destruct U as [v[V U]]. rewrite U. rewrite forallb_forall in H. rewrite (proj2 E). rewrite (app1 (proj1 E)).
rewrite (proj2 F). rewrite <- (proj1 F) in V. rewrite app_nth1. apply H. apply nth_In. 1,2:apply V.
all:intros H;inversion H. Qed.
Lemma hasbrickb_suff {x w r d}: hasbrickb x w r = true -> exists u, u<w /\ nth (u+x) r d=is brick.
unfold hasbrickb. destruct (splitn _ _) as [[r1 r2]|] eqn:E. apply splitn_app in E.
destruct (splitn _ _) as [[r3 r4]|] eqn:F. apply splitn_app in F. all:intros H. rewrite existsb_exists in H.
destruct H as [t [T B]]. apply (In_nth _ _ d) in T. destruct T as [u[U T]]. exists u. split.
rewrite <- (proj1 F). apply U. rewrite <- brickbp_equiv. rewrite (proj2 E). rewrite (app1 (proj1 E)).
rewrite (proj2 F). rewrite app_nth1. rewrite T. apply B. apply U. all:inversion H. Qed.
Lemma stripb_suff {x y w s g ps}: stripb x y w g = true -> gridm g ps s -> hasstrip x y w s.
pose proof Bool.diff_false_true. unfold stripb. destruct (splitn _ _) as [[g1 [|r1[|r2 g2]]]|] eqn:E; try tauto.
apply splitn_app in E. rewrite Bool.andb_true_iff. erewrite (_:r1=_). intros [R1 X] M.
eapply (rowfb_suff M) in R1. epose proof (noholdb_suff X) as R2. split. apply (proj1 R1). split.
intros [u v] [U [V1 V2]]. apply (notholdable_suff M). inversion V2. erewrite (_:r2=_) in R2. apply (R2 u U).
rewrite (int1 (conj V1 H1)). apply (proj2 R1 u U). destruct M. tauto. Unshelve. all:rewrite (proj2 E).
rewrite (app1 (proj1 E) 0). split. rewrite (app1 (proj1 E) 1). split. Qed.
Lemma solidbrick: is_solid brick. right. split. Qed.
Theorem stripsuff {g ps s} r h qs x y w: gridm g ps s -> (strip x y w g ps,row x (S y) w) = (Some(h,qs),r) ->
  fronts s (andp (gridm h qs) (hassolid r)) (andp (gridm h r) (hassolid r)).
rewrite pair_equal_spec. unfold strip. destruct (expand _ _ _) as [[??]|] eqn:E. destruct (_:bool) eqn:B.
all:intros M [H R]; inversion H. rewrite <- R. replace _ with (h,qs) in E. revert B. rewrite H1.
repeat (rewrite Bool.andb_true_iff). rewrite eqb_eq.
rewrite length_zero_iff_nil. intros [[B ST] I]. apply refs. apply (impl_rinv stripf). intros t.
apply (stripb_suff ST). epose proof (hasbrickb_suff B) as [u [U G]]. exists (u+x,S y). rewrite row_in. split.
exists u. tauto. replace _ with brick. apply solidbrick. destruct M as [_[M _]]. epose proof (M _) as M1.
replace _ with (is brick) in M1. inversion M1. apply H3. unfold evp. unfold evg. symmetry. apply G.
eapply expandsuff. apply M. apply I. apply E. rewrite pair_equal_spec. split; symmetry; tauto. Qed.
Lemma ess s p: is_empty(ev (sg s) p) \/ is_solid(ev (sg s) p). apply empty_dec. Qed.
Lemma applyempty {s p} d e: is_empty(ev (sg s) p) -> poss_remove p d = e -> hassolid d s -> hassolid e s.
intros A E [q [D Q]]. rewrite <- E. eexists. split. apply ListSet.set_remove_3. apply D. intros F.
apply A. rewrite <- F. all:apply Q. Qed.
Definition tobrick p g := if qmbp (evp g p) then replaceg p (is brick) g else g.
Lemma tobrick_suff {g p}: tobrick p g = g \/ (evp g p = qm /\ setg p (is stone) (is brick) g (tobrick p g)).
unfold tobrick. destruct (evp _ _) eqn:E; simpl; try tauto. epose proof replace_set as [R|R]. unfold evp in E.
rewrite E in R. inversion R. right. apply (conj (Logic.eq_refl _) R). Qed.
Lemma tobrickm {g ps s p}: gridm g ps s -> is_solid (ev (sg s) p) -> gridm (tobrick p g) ps s.
unfold gridm. unfold tilems. intros [P[T[F V]]] H. split. apply P. split. epose proof tobrick_suff as [E|[QM E]].
rewrite E. apply T. intros q. unfold evp. destruct (proj2 E q) as [G|G]. rewrite G. pose proof (T p) as Tp.
rewrite QM in Tp. inversion Tp. rewrite (proj1 E). constructor. tauto. destruct air_empty. rewrite H0. apply H.
rewrite G. apply T. tauto. Qed.
Lemma solidp {g ps qs s}: gridm g ps s -> (forall p, In p ps -> is_empty(ev(sg s)p) -> In p qs) -> gridm g qs s.
intros [P[T[F V]]] H. split. apply (H _ P F). tauto. Qed.
Lemma applysolid {s p} g ps h qs: is_solid (ev (sg s) p) -> (tobrick p g,poss_remove p ps)=(h,qs)
  -> gridm g ps s -> gridm h qs s.
rewrite pair_equal_spec. intros E [H Q] M. rewrite <- H. apply tobrickm. apply (solidp M). intros r R F.
rewrite <- Q. apply ListSet.set_remove_3. apply R. intros G. destruct F. rewrite G. all:apply E. Qed.
Lemma splitsolid {p d s}: hassolid (p::d) s -> is_solid (ev (sg s) p) \/ hassolid d s.
intros [q [[E|I] Q]]. rewrite E. tauto. right. eexists. apply (conj I Q). Qed.
Lemma nilsolid {s}: hassolid [] s -> False. intros [q [[]]]. Qed.
End Strip.
Ltac strip x y w := lazymatch goal with
  | [_:reach1 ?s _ , M:gridm ?g ?ps ?s |- _] =>
    match eval compute in (strip x y w g ps,row x (S y) w) with
      | (Some (?h,?qs),?r) => pose proof (stripsuff r h qs x y w M (Logic.eq_refl _)); applyf
end end.
Ltac usesolid p H := try (lazymatch goal with
  | [_:reach1 ?s _ , M:gridm ?g ?ps ?s |- _] =>
    match eval compute in (tobrick p g,poss_remove p ps) with
      | (?h,?qs) => apply (applysolid g ps h qs H (Logic.eq_refl _)) in M end end);
  try (lazymatch goal with
  | [M:gridm ?g [] ?s |- _] => destruct M as [[]] end).
Ltac useempty p H := try (lazymatch goal with
  | [_:reach1 ?s _ , B:hassolid ?d ?s |- _] =>
    match eval compute in (poss_remove p d) with
      | ?e => apply (applyempty d e H (Logic.eq_refl _)) in B end end).
Ltac es p := lazymatch goal with
  | [_:reach1 ?s _ |- _] =>
    let H := fresh in pose proof (ess s p) as [H|H]; [useempty p H|usesolid p H] end.
Ltac splitsolid := let rec helper := try (lazymatch goal with
  | [H:hassolid [] ?s |- False] => apply (nilsolid H)
  | [H:hassolid (?p::?d) ?s |- _] => apply splitsolid in H; destruct H as [H|H]; [usesolid p H|helper]
end) in helper.

Section Box.
(*
Can't escape from:
B*  B
BBBBB
BBBBB
 BBB
*)

Definition incup x y w h p := match p with | (u,v) => ((x=S u \/ u=w+x) /\ (y<=v<h+y)) \/
  ((x<=u<w+x) /\ (v=h+y)) end.
Definition hasbricks x y w h s := forall p, inbox x y w h p -> ev (sg s) p = brick.
Definition hascup x y w h s := forall p, incup x y w h p -> is_solid (ev (sg s) p).
Definition inrow x y w s := In (sp s) (row x y w).

Lemma rowy {x y w p}: In p (row x y w) -> snd p = y. rewrite row_in. intros [? [_ P]]. rewrite P. split. Qed.
Lemma cupinv {x y w h}: w <= h -> rinv (inrow x y w) (hascup x y w h).
intros W [p g d] t H. unfold inrow. unfold hascup. simpl. intros P C q Q. destruct h as [|h]. inversion W.
rewrite H0 in P. destruct P. destruct (solidinv H (C q Q)) as [G|[[_[G[_ E]]]_]]. apply G.
epose proof (E (C _ _)) as []. Unshelve. destruct q as [u v]. pose proof (besidey G) as V. simpl in V.
rewrite (rowy P) in V. destruct Q as [[X Y]|[X Y]]. left. split. apply X. rewrite <- V. apply (plusin 0).
apply lt_0_succ. destruct h. rewrite Y in G. simpl in G. destruct w as [|[|w]]. destruct P. destruct P as [P|[]].
destruct X as [L R]. inversion R. rewrite H1 in G. rewrite P in G. destruct (beside_irrefl G).
destruct (int0 (conj L H1)). apply Le.le_S_n in W. inversion W. rewrite Y in V.
simpl in V. destruct (lt_irrefl (h+y)). unfold "<". simpl in V. rewrite <- V. apply Plus.le_plus_r. Qed.
Lemma brickinv {x y w h}: rinv (inrow x y w) (hasbricks x (2+y) w h).
intros s t H. intros P B q Q. destruct (stepev q H) as [[E _]|[[E]|[_[_[[_ [E]]]]]]]. 1,2:rewrite E.
apply (B q Q). split. destruct q as [u v]. apply besidey in E. rewrite (rowy P) in E. destruct Q as [_ [Q]].
apply pred_le_mono in Q. simpl in E. rewrite <- E in Q. destruct (lt_irrefl _ Q). Qed.
Lemma noholdinv {x y w h}: inv (nohold x y w h).
intros s t H N p P. destruct (stepev p H) as [[E _]|[[E]|[_ [E]]]]; rewrite E. apply (N p P).
all:rewrite holdable_equiv; apply Bool.diff_false_true. Qed.
Lemma cupwall {x y w h s}: hascup x y w (S h) s <-> walled x y w (sg s) /\ hascup x (S y) w h s.
unfold hascup. unfold incup. rewrite add_succ_r. rewrite add_succ_l. split. intros C. split.
pose proof (@plusin y _ 0 (lt_0_succ h)) as Y. split. apply C. tauto. destruct x. split. apply C. tauto.
intros [u v] [H|H]; apply C. assert (y<=v). eapply le_trans. apply le_succ_diag_r. 1,2,3:tauto.
intros [[R L] C] [u v] [[X [Y1 Y2]]|H]. inversion Y1. rewrite <- H. destruct X as [X|X]. rewrite X in L.
apply L. rewrite X. apply R. apply Le.le_n_S in H. rewrite <- H0 in Y2. all:apply C; tauto. Qed.
Lemma dropdown {x y w h s t}: step s t -> inrow x y w s -> walled x y w (sg s) -> nohold x y w (S h) s ->
  inrow x y w t \/ inrow x (S y) w t.
destruct s as [p g d]. intros H P C L. inversion H. inversion H4. right. rewrite H6. apply (rowdown P).
destruct (L p). apply (rowbox 0 P). apply lt_0_succ. simpl. rewrite H7. left. split.
symmetry in H6. destruct (walledin P H6 C) as [Q|Q]. tauto. destruct (H5 Q). all:left; apply P. Qed.
Definition subint x1 w1 x2 w2 := x1 <= x2 /\ w2+x2 <= w1+x1.
Lemma sub_add1 {a b c}: b<a -> (a-S b)+(S b+c)=a+c.
intros H. rewrite add_assoc. rewrite sub_add. split. apply H. Qed.
Lemma subwall {x y w s}: hassolid (row x y w) s -> walled x y w (sg s) -> inrow x y w s -> free s ->
  exists x1 w1, w1<w /\ subint x w x1 w1 /\ walled x1 y w1 (sg s) /\ inrow x1 y w1 s.
unfold inrow. rewrite row_in. unfold hassolid. intros [q [Q F]] [R L] [u [U P]] E.
rewrite row_in in Q. destruct Q as [v [V Q]]. rewrite Q in F. destruct (Compare_dec.le_lt_dec u v) as [H|H].
inversion H. destruct E. rewrite P. rewrite H0. apply F. exists x. exists v. repeat split; try assumption.
apply le_refl. apply Plus.plus_le_compat_r. apply lt_le_incl. apply V. rewrite row_in. exists u. split.
rewrite <- H1. apply Le.le_n_S. apply H0. apply P. exists (S v+x). exists (w-S v). repeat split. unfold "<".
rewrite Minus.minus_Sn_m. rewrite sub_succ. apply le_sub_l. apply V. apply Plus.le_plus_r. rewrite (sub_add1 V).
apply le_refl. rewrite (sub_add1 V). apply R. rewrite add_succ_l. apply F. rewrite row_in. exists (u-S v). split.
apply lt_add_lt_sub_r. rewrite sub_add. apply U. apply H. rewrite (sub_add1 H). apply P. Qed.
Lemma subcup {x y w h x1 w1 s}: subint x w x1 w1 -> hascup x y w h s -> hasbricks x y w h s ->
  hascup x1 y w1 h s.
intros [L R] C B [u v] [[[X|X]Y]|H]. inversion L. apply C. rewrite H. left. tauto. rewrite B. apply solidbrick.
split. split. rewrite X in H0. inversion H0. rewrite <- H2. apply H. eapply le_trans. rewrite <- X.
eapply Plus.le_plus_r. apply R. apply Y. inversion R. rewrite H0 in X. apply C. left. tauto. rewrite B.
apply solidbrick. split. rewrite X. split. eapply le_trans. apply L. apply Plus.le_plus_r. rewrite <- H.
apply Le.le_n_S. apply H0. apply Y. apply C. right. split. split; eapply le_trans. apply L. 3:apply R. all:tauto.
Qed.
Lemma subbox {x y w h x1 w1 p}: subint x w x1 w1 -> inbox x1 y w1 h p -> inbox x y w h p.
destruct p as [u v]. intros [L R] [[U1 U2] V]. split. split; eapply le_trans. 1:apply L. 3:apply R. all:tauto.
Qed.
Lemma boxup {x y w h p}: inbox x (S y) w (pred h) p -> inbox x y w h p.
destruct p as [u v]. intros [U [V1 V2]]. destruct h. apply Le.le_S_n in V2. destruct (int0 (conj V2 V1)).
apply (le_trans _ _ _ (le_succ_diag_r _)) in V1. rewrite add_succ_r in V2. unfold inbox. rewrite add_succ_l.
tauto. Qed.
Lemma solid_hold {t}: is_solid t -> ~is_holdable t.
rewrite holdable_equiv. intros [T|T]; rewrite T; apply Bool.diff_false_true. Qed.
Theorem boxreach {x y w h p s}: w <= h -> hascup x y w h s -> hasbricks x (S y) w (pred h) s ->
  nohold x y w h s -> inrow x y w s -> reach1 s p -> free s -> inbox x y w h p.
revert x y w s. induction h; intros x y w s W. inversion W. intros _ _ _ []. set (hascup _ _ _ _) as hc.
set (nohold _ _ _ _) as nh. intros C B H P R F.
assert (fronts s (andp(inrow x y w)(andp hc (andp nh free))) (andp(inrow x (S y) w)hc)) as FR. unfold andp.
split. tauto. intros t u U [Pt [Ct [Ht Ft]]]. epose proof (dropdown U Pt _ Ht). pose proof (noholdinv _ _ U Ht).
pose proof (cupinv W _ _ U Pt Ct). apply (freeinv _ _ U) in Ft. tauto.
eapply (refs (impl_rinv brickinv _)) in FR. eapply (refs (impl_rinv stripf _)) in FR.
epose proof (applyf FR R) as [t [T [[[[[P1]]]P2]|X]]]. rewrite <- P2. apply (rowbox 0 P1). apply lt_0_succ.
apply (inv1 noholdinv T) in H. apply (inv1 freeinv T) in F. clear dependent s. destruct X as [[[[P C]B]SL]R].
destruct h. 2:{unfold hc in C. repeat (rewrite cupwall in C). destruct C as [_[WL C]].
destruct (subwall SL WL P F) as [x1 [w1 [W1[SB[WL1 P1]]]]]. epose proof (IHh _ _ _ _ _ _ _ _ P1 R F) as P2.
apply (subbox SB) in P2. apply boxup. apply P2. } destruct w as [|[|?]]. destruct P as []. destruct P as [P|[]].
destruct SL as [q [[Q|[]] Qs]]. destruct F. rewrite <- P. rewrite Q. tauto. apply Le.le_S_n in W. inversion W.
destruct w. destruct P as []. exists (x,S y). split. left. split. destruct h. apply C. right. split.
apply (plusin 0). apply lt_0_succ. split. rewrite B. apply solidbrick. split. apply (plusin 0). apply lt_0_succ.
split. apply le_refl. simpl. apply Le.le_n_S. apply Plus.le_plus_r. intros q Q. apply B. apply boxup. apply Q.
Unshelve. apply (proj1 cupwall) in Ct. tauto. intros ? [I _]. apply I. clear dependent s.
intros t [[_[C [H F]]]B]. split. apply (proj1 cupwall) in C. tauto. split. intros [u v] [U [V1 V2]].
epose proof (Lt.le_lt_or_eq v (S h+y) _) as [V3|V3]. apply H. unfold inbox. tauto. rewrite V3. apply solid_hold.
apply C. right. tauto. tauto. apply Le.le_S_n. eapply le_trans. apply W1. apply W.
 rewrite cupwall. split. apply WL1. apply (subcup SB C B). intros q Q. apply B. apply (subbox SB Q). intros q Q.
apply H. apply boxup. simpl. apply (subbox SB Q). Unshelve. apply Le.le_S_n. eapply le_trans. apply V2.
rewrite (add_succ_l h). repeat (apply Le.le_n_S). apply Plus.le_plus_r. Qed.

Fixpoint boxhelper x w h g := match (h,g) with
  | (1,_) => negb (existsb emptybp (map (fun x => evp g (x,0)) (seq x w)))
  | (S h,r::g) => if rowfb x w brickbp r then boxhelper x w h g else false
  | _ => false end.
Definition boxb x y w g := match splitn y g with | Some (_,r::h) =>
  ((rowfb x w notholdableb r) && boxhelper x w w h)%bool
  | _ => false end.
Definition inboxb x y w h p := match p with | (u,v) => ((x<=?u)&&(u<?w+x)&&(y<=?v)&&(v<?h+y))%bool end.
Definition rowb x y w p := match p with | (u,v) => ((v=?y)&&(x<=?u)&&(u<?w+x))%bool end.
Definition boxpb x y w g ps p := ((boxb x y w g)&&(forallb (rowb x y w) ps) && negb (inboxb x y w w p))%bool.

Lemma inboxb_eq {x y w h p}: inbox x y w h p <-> inboxb x y w h p = true.
destruct p as [u v]. unfold inboxb. repeat (rewrite Bool.andb_true_iff). repeat (rewrite ltb_lt).
repeat (rewrite leb_le). unfold inbox. tauto. Qed.
Lemma rowb_suff {x y w p}: rowb x y w p = true -> In p (row x y w).
destruct p as [u v]. unfold rowb. repeat (rewrite Bool.andb_true_iff). rewrite ltb_lt. rewrite leb_le.
rewrite eqb_eq. unfold row. rewrite in_map_iff. intros [[Y L] R]. exists u. rewrite in_seq. rewrite add_comm.
rewrite Y. tauto. Qed.
Lemma appg {g1 g2 x y}: length g1 = y -> forall v, evp (g1++g2) (x,v+y) = evp g2 (x,v).
intros Y v. unfold evp. unfold evg. simpl. rewrite (app1 Y). split. Qed.
Lemma boxhelper_suff {x y w h g1 g2 ps s}: length g1 = y -> gridm (g1++g2) ps s -> boxhelper x w (S h) g2 = true
  -> hascup x y w h s /\ hasbricks x y w h s.
revert y g1 g2. induction h. simpl. intros y g1 g2 Y M. rewrite Bool.negb_true_iff. intros H. split.
intros [u v] [[_ V]|[U V]]. destruct (int0 V). rewrite V. eapply (emptybp_false M). eapply existsb_false.
apply H. rewrite in_map_iff. exists u. split. symmetry. apply (appg Y 0). rewrite in_seq. rewrite add_comm.
apply U. intros [u v] [_ V]. destruct (int0 V). intros y g1 [|r g2] Y M; simpl. intros H. inversion H.
destruct (rowfb _ _ _ ) eqn:R; intros H. epose proof (IHh (S y) (g1++[r]) g2 _ _ H) as [C B]. rewrite cupwall.
erewrite (_:r=_) in R. epose proof (rowfb_suff M R) as [W B0]. split. apply (conj W C).
intros [u v] [U [V1 V2]]. inversion V1. destruct M as [_[M _]]. unfold tilems in M. epose proof (M _) as M1.
pose proof (B0 u U) as B1. rewrite brickbp_equiv in B1. rewrite B1 in M1. inversion M1. rewrite <- H0. symmetry.
apply H2. apply B. unfold inbox. apply Le.le_n_S in H0. rewrite <- H1 in V2. rewrite add_succ_r. tauto.
inversion H. Unshelve. apply (len1 Y). rewrite <- app_assoc. apply M. rewrite (app1 Y 0). split. Qed.
Theorem boxbs_suff x y w {g ps p s}: gridm g ps s -> reach1 s p -> boxpb x y w g ps p = true -> False.
pose proof Bool.diff_false_true as FT. unfold boxpb. unfold boxb. destruct (splitn _ _) as [[g1 [|r g2]]|] eqn:E.
1,3:simpl; tauto. repeat (rewrite Bool.andb_true_iff). rewrite Bool.negb_true_iff. intros M R [[[H T]PT]P].
apply FT. rewrite <- P. rewrite <- inboxb_eq. apply splitn_app in E. destruct E as [Y E]. erewrite (_:r=_) in H.
eapply (rowfb_suff M) in H. assert (inrow x y w s) as PS. apply rowb_suff. rewrite forallb_forall in PT.
apply PT. apply (proj1 M). destruct w as [|w]. destruct PS. epose proof (boxhelper_suff (len1 Y) _ T) as [C B].
eapply boxreach. apply le_refl. rewrite cupwall. apply (conj (proj1 H) C). apply B. intros [u v] [U [V W]]. 
inversion V. apply (notholdable_suff M). rewrite <- H0. apply (proj2 H). apply U. rewrite holdable_equiv.
erewrite (_:_=false). apply FT. apply PS. apply R. destruct M as [_ M]. tauto. Unshelve.
rewrite E. rewrite (nth_hd Y). split. 3:{rewrite <- app_assoc. simpl. rewrite <- E. apply M. } rewrite B. split.
unfold inbox. rewrite <- H1 in W. apply Le.le_n_S in H0. rewrite add_succ_r. tauto. Qed.
End Box.
Ltac box x y w := lazymatch goal with
  | [ R : reach1 _ _ , M : gridm _ _ _ |- False ] =>
    apply (boxbs_suff x y w M R (Logic.eq_refl true)) end.

Section Column.
Definition fd f s := filter f (sd s).
Definition destroyed f s t p := (fd f t=p::fd f s) /\ candestroy s p /\ step s t.
Lemma stepfd {f s t}: step s t -> let (ds,dt) := (fd f s,fd f t) in
  ds = dt \/ exists p, dt++[p]=ds \/ destroyed f s t p.
unfold destroyed. unfold fd. intros H. pose proof H as G. revert G. inversion H; intros G; simpl. tauto.
destruct (f _). right. exists pb. right. unfold candestroy. destruct ps as [u v]. replace (up pb) with (u,v).
repeat split; simpl; try assumption. 1,2:rewrite H1. apply lt_0_succ. split. tauto. rewrite filter_app. simpl.
destruct (f q). right. exists q. tauto. rewrite app_nil_r. tauto. Qed.
Lemma fdtrue {f s p}: In p (fd f s) -> f p = true. unfold fd. rewrite filter_In. tauto. Qed.
Lemma destroyedtrue {f s t p}: destroyed f s t p -> f p = true.
intros [E _]. eapply fdtrue. rewrite E. left. split. Qed.
Lemma fdempty {f s p}: tilems qm p s -> is_empty (ev (sg s) p) -> f p = true -> In p (fd f s).
unfold fd. rewrite filter_In. intros T E. inversion T. destruct E. rewrite <- H. apply solidbrick. tauto. Qed.
Definition hasqm x y h s := validd s /\ forall p, inbox x y 1 h p -> tilems qm p s.
Lemma hasqminv {x y h}: inv (hasqm x y h).
intros s t H [V Q]. split. apply (validdinv s t H V). intros p P. apply (qminv s t H V (Q p P)). Qed.
Definition rabove p q := above q p.
Definition column x y h s := consec rabove (fd (inboxb x y 1 h) s) /\ hasqm x y h s /\ 
  desc (fun t => ~candestroy t (x,y)) s.
Lemma inboxtop {x y h p}: inboxb x y 1 h p = true ->
  p = (x,y) \/ (inboxb x y 1 h (up p) = true /\ above (up p) p).
repeat (rewrite <- inboxb_eq). destruct p as [u v]. intros [U [V1 V2]]. inversion V1. apply int1 in U. rewrite U.
tauto. right. split. split. apply U. simpl. split. tauto. apply lt_le_incl. rewrite H0. tauto. split. Qed.
Lemma desc1 {P s}: desc P s -> P s. intros H. apply H. apply rt_refl. Qed.
Lemma columndestroyed {x y h s t p}: column x y h s -> destroyed (inboxb x y 1 h) s t p ->
  hasfirst (rabove p) (fd (inboxb x y 1 h) s).
intros [C[[V Q] N]] D. pose proof (destroyedtrue D) as P. destruct D as [E [D T]].
destruct (inboxtop P) as [F|[F A]]. apply desc1 in N. destruct N. rewrite <- F. tauto.
destruct D as [_[_[_ D]]]. epose proof (fdempty _ D F) as U. apply in_split in U. destruct U as [l1[l2 G]].
rewrite <- (rev_involutive l1) in G. destruct (rev l1) as [|q ?]; simpl in G. rewrite G. apply A.
rewrite <- nxt in G. replace q with p in G. eassert (NoDup (p::_)) as X. rewrite <- E. unfold fd.
apply NoDup_filter. apply (proj1 (validdinv _ _ T V)). inversion X. destruct H1. rewrite G. rewrite in_app_iff.
simpl. tauto. rewrite G in C. apply consec1 in C. destruct C as [_ [C _]]. rewrite C. apply A. Unshelve.
apply Q. rewrite inboxb_eq. tauto. Qed.
Lemma columninv {x y h}: inv (column x y h).
intros s t H G. pose proof G as [C[Q N]]. split. epose proof (stepfd H) as [F|[p[F|F]]]. rewrite <- F.
apply C. rewrite <- F in C. apply consec1 in C. tauto. rewrite (proj1 F). apply (columndestroyed G) in F.
destruct (fd _ s) as [|q l]. destruct F. apply (conj F C). split. eapply hasqminv. 3:eapply desc_inv.
1,3:apply H. all:tauto. Qed.
Definition hasqmb x y h g := forallb (fun(z:nat) => (if z then qmbp else brickbp) (evp g (x,z+y))) (seq 0 h).
Lemma hasqmb_suff {x y h g}: hasqmb x y h g = true -> forall p, inbox x y 1 h p ->
  evp g p = is brick \/ (p = (x,y) /\ evp g p = qm).
unfold hasqmb. rewrite forallb_forall. intros H [u v] [U V]. rewrite int_in in V. destruct V as [w[W E]].
apply int1 in U. rewrite U. rewrite E. epose proof (H w _) as F. pose proof Bool.diff_false_true.
destruct w as [|w]; revert F. destruct (evp g _); simpl; tauto. rewrite brickbp_equiv. tauto. Unshelve.
rewrite in_seq. split. apply Le.le_0_n. apply W. Qed.
Lemma nodup1 {A l P} {a:A}: NoDup l -> incl l [a] -> consec P l.
intros D I. eassert (forall b,_->b=a) as E. intros b B. apply (I b) in B. destruct B as [B|[]]. symmetry. tauto.
destruct l as [|b[|c l]]. 1,2:split. inversion D. destruct H1. left. rewrite E. apply E. all:simpl; tauto. Qed.
Definition besideb (p q:position) := match (p,q) with
  | ((x,y),(u,v)) => ((y=?v)&&((x=?S u)||(u=?S x)))%bool end.
Lemma besideb_eq {p q}: beside p q <-> besideb p q = true.
destruct p as [x y]. destruct q as [u v]. unfold beside. unfold right. unfold besideb.
rewrite Bool.andb_true_iff. rewrite Bool.orb_true_iff. repeat (rewrite eqb_eq).
repeat (rewrite (@pair_equal_spec nat nat)). rewrite (eq_sym_iff v y). tauto. Qed.
Definition colb x y h g ps := match expand g ps [] with
  | Some(_,qs) => (negb(existsb (besideb (x,pred y)) qs) && hasqmb x y h g)%bool
  | _ => false end.

Lemma in_nil {A} {l:list A}: (forall a, ~In a l) -> l = [].
destruct l as [|a ?]. split. intros H. destruct (H a). left. split. Qed.
Lemma colbsuff {g ps s} x y h: gridm g ps s -> colb x y h g ps = true -> desc (column x y h) s.
unfold colb. destruct (expand _ _ _) as [[? qs]|] eqn:E. rewrite Bool.andb_true_iff. rewrite Bool.negb_true_iff.
intros M [D Q]. eapply (expandsuff _ _ _ M _) in E. pose proof M as [_[T[_ [V A]]]]. eenough _ as C.
intros t R. apply (inv1 columninv R C). repeat split; try tauto. unfold fd.
eapply nodup1. apply NoDup_filter. apply V. intros p. rewrite filter_In. rewrite <- inboxb_eq. intros [P I].
pose proof (hasqmb_suff Q p I) as [F|[F _]]. rewrite (tilemqm (T p) P) in F. inversion F. left. symmetry.
apply F. intros p I. pose proof (T p) as P. pose proof (hasqmb_suff Q p I) as [F|[_ F]]; rewrite F in P.
unfold tilems. unfold tilems in P. inversion P. constructor. tauto. tauto. intros t R.
destruct (fronts_reach E R) as [[N _]|[?[_[_[[]]]]]]. intros [_ [B _]]. apply Bool.diff_false_true.
rewrite <- (existsb_false D _ N). rewrite <- besideb_eq. symmetry. apply B. intros _ H. inversion H.
Unshelve. apply in_nil. intros p. unfold poss_inter. rewrite ListSet.set_inter_iff. intros [? []]. Qed.

Lemma abovet {l p}: consec rabove l -> In p l -> snd (hd p l) >= snd p.
induction l. intros _ []. intros C [P|P]. rewrite P. apply Le.le_refl. destruct l as [|[x y] l].
destruct P as []. destruct C as [B C]. rewrite B. simpl. constructor. apply (IHl C P). Qed.
Ltac introsdup H := let K := fresh in intros H; pose proof H as K; revert K.
Lemma subbox1 {x y h k p}: h<=k -> inbox x y 1 h p -> inbox x y 1 k p.
destruct p as [u v]. intros H [U [V1 V2]]. split. apply U. split. apply V1. eapply le_trans. apply V2.
apply Plus.plus_le_compat_r. apply H. Qed.
Lemma subconsec {x y h k l}: h<=k -> consec rabove (filter (inboxb x y 1 k) l) ->
  consec rabove (filter (inboxb x y 1 h) l).
intros H. eenough (forall p,_ p=true->_ p=true) as B. induction l. split. destruct (inboxb x y 1 h a) eqn:I.
introsdup C. erewrite filter_ext_in. intros E. apply E. intros [u v] P. apply Bool.eq_true_iff_eq. split.
introsdup K. revert I. introsdup J. apply B in J. destruct a as [? w]. repeat (rewrite <- inboxb_eq).
intros [_[_ W]] [U [V1 _]]. eassert (In _ _) as Q. rewrite filter_In. apply (conj P K). apply (abovet C) in Q.
unfold filter in Q. rewrite J in Q. simpl in Q. split. apply U. split. apply V1. eapply le_trans.
apply Le.le_n_S. apply Q. apply W. apply B. simpl. rewrite I. intros C. apply (IHl B).
destruct (inboxb _ _ _ k _). apply (proj2 (@consec1 _ _ [a] _ C)). apply C. intros p.
repeat (rewrite <- inboxb_eq). apply (subbox1 H). Qed.
Definition column1 x y h s := column x y (S h) s /\ hd (x,h+y) (fd (inboxb x y 1 (S h)) s) = (x,h+y).
Lemma hasfirst_hd {A P l} {a:A}: hasfirst P l -> P (hd a l). destruct l as [|b l]. intros []. simpl. tauto. Qed.
Lemma column1destroyed {x y h s t p}: column1 x y h s -> ~destroyed (inboxb x y 1 (S h)) s t p.
intros [C E] F. pose proof (columndestroyed C F) as P. eassert (In (below(x,h+y)) (p::_)) as Q. left.
rewrite <- E. apply (hasfirst_hd P). rewrite <- (proj1 F) in Q. apply fdtrue in Q. rewrite <- inboxb_eq in Q.
destruct Q as [_ [_ Q]]. destruct (lt_irrefl _ Q). Qed.
Lemma column1inv {x y h}: inv (column1 x y h).
intros s t H [C E]. split. apply (columninv s t H C). epose proof (stepfd H) as [F|[p[F|F]]]. rewrite <- F.
apply E. destruct (fd _ t) as [|q l]. split. rewrite <- F in E. apply E.
destruct (column1destroyed (conj C E) F). Qed.
Lemma col1suff {x y k s} h: desc (column x y k) s -> is_empty(ev (sg s) (x,h+y)) ->
  (h<?k)=true -> desc (column1 x y h) s.
rewrite ltb_lt. intros C E K. eenough _ as C1. intros t R. apply (inv1 column1inv R C1). eenough _ as Cs.
split. apply Cs. eenough _ as I. destruct Cs as [A [[_ Q] _]]. eapply (fdempty (Q _ _) E) in I.
eapply (abovet A) in I. destruct (fd _ s) as [|[u v] l] eqn:L. split. simpl in I. eassert (In _ (fd _ _)) as V.
rewrite L. left. split. apply fdtrue in V. rewrite <- inboxb_eq in V. destruct V as [U [V1 V2]].
rewrite (int1 U). rewrite (int1 (conj I V2)). split. rewrite <- inboxb_eq. repeat split. 1,2,4:constructor.
apply Plus.le_plus_r. eassert (column x y k s) as C1. apply (desc1 C). revert C1. unfold column.
intros [A[[[??] Q] D]]. repeat split; try tauto. apply (subconsec K A). intros p P. apply Q.
apply (subbox1 K P). Unshelve. rewrite inboxb_eq. apply I. Qed.

Definition tobrickl l g ps := (fold_right tobrick g l, poss_diff ps l).
Lemma applysolidl {s l g ps h qs}: gridm g ps s -> tobrickl l g ps = (h,qs) -> 
  (forall p, In p l -> is_solid (ev (sg s) p)) -> gridm h qs s.
unfold tobrickl. rewrite pair_equal_spec. intros M [H Q] E. apply (@solidp _ ps). rewrite <- H.
clear dependent h. clear dependent qs. revert E. induction l; simpl. tauto. intros E. apply tobrickm. apply IHl.
intros q Q. 1,2:apply E; tauto. intros r R F. rewrite <- Q. apply ListSet.set_diff_intro. apply R. intros L.
destruct F. apply E. apply L. Qed.
Definition tobrickc x y h := tobrickl (map (fun z => (x,z+y)) (seq 0 h)).
Definition qmsolid f s := forall p, f p = true -> tilems qm p s -> is_solid (ev (sg s) p).
Lemma applysolidc {s x y h g ps h1 qs}: gridm g ps s -> hasqm x y h s -> tobrickc x y h g ps = (h1,qs) ->
  qmsolid (inboxb x y 1 h) s -> gridm h1 qs s.
intros M Q H E. apply (applysolidl M H). intros p. rewrite in_map_iff. intros [z [P Z]]. rewrite in_seq in Z.
eenough _ as I. apply E. rewrite <- inboxb_eq. apply I. apply Q. apply I. rewrite <- P. repeat split.
1,2:constructor. apply Plus.le_plus_r. unfold "<". rewrite <- add_succ_l. apply Plus.plus_le_compat_r.
apply (proj2 Z). Qed.
Lemma fdnil {p f s}: hd p (fd f s) = p -> is_solid(ev (sg s) p) -> validd s -> qmsolid f s.
destruct (fd f s) as [|q l] eqn:F. intros _ _ _ q Q T. epose proof empty_dec as [H|H]. 2:apply H.
assert (In q []) as []. rewrite <- F. apply fdempty; tauto. simpl. intros Q H [_ V]. destruct air_empty.
rewrite <- (V q). rewrite Q. apply H. eapply proj1. rewrite <- filter_In. unfold fd in F. rewrite F. left. split.
Qed.
Lemma applycol1 {x y h s} g ps h1 qs: desc (column1 x y h) s -> is_solid(ev (sg s) (x,h+y)) ->
  tobrickc x y (S h) g ps = (h1,qs) -> gridm g ps s -> gridm h1 qs s.
intros C B E M. apply desc1 in C. destruct C as [[_[Q _]] H]. apply (applysolidc M Q E). apply (fdnil H B).
unfold gridm in M. tauto. Qed.

Definition incolbo x y h p q:bool := inboxb x y 1 (S h) q || PosDec.eqb p q.
Definition colo x y h p s := hd p (fd (incolbo x y h p) s) = p.
Definition column2 x y h l s := column1 x y h s /\ (forall p, In p l -> is_solid(ev (sg s) p) \/ colo x y h p s).
Definition column3 x y h p s := column1 x y h s /\ colo x y h p s.
Definition subb {A} f g := forall(a:A), f a = true -> g a = true.
Lemma subfilter {A f g} {l:list A}: subb f g -> filter f (filter g l) = filter f l.
intros B. induction l. split. simpl. destruct (f a) eqn:F. rewrite (B _ F). simpl. rewrite F. rewrite IHl.
split. destruct (g a). simpl. rewrite F. all:apply IHl. Qed.
Lemma subdestroy {f g s t p}: subb f g -> f p = true -> destroyed g s t p -> destroyed f s t p.
intros B P [G H]. split. apply (f_equal (filter f)) in G. simpl in G. rewrite P in G. unfold fd in G.
repeat (rewrite (subfilter B) in G). apply G. apply H. Qed.
Lemma column3inv {x y h p}: inv (column3 x y h p).
unfold column3. unfold colo. intros s t R [C H]. split. apply (column1inv s t R C).
epose proof (stepfd R) as [F|[q[F|F]]]. rewrite <- F. apply H. destruct (fd _ t) as [|r l]. split.
rewrite <- F in H. apply H. pose proof (destroyedtrue F) as B. unfold incolbo in B. revert B.
rewrite Bool.orb_true_iff. rewrite PosDec.eqb_eq. intros [B|B]. eapply (subdestroy _ B) in F.
destruct (column1destroyed C F). rewrite (proj1 F). symmetry. apply B. Unshelve. intros r. unfold incolbo.
rewrite Bool.orb_true_iff. tauto. Qed.
Lemma column2inv {x y h l}: inv (column2 x y h l).
unfold column2. intros s t R [C H]. split. apply (column1inv s t R C). intros p P. destruct (H p P) as [K|K].
destruct (solidinv R K) as [L|[_ L]]. tauto. right. unfold colo. unfold fd. rewrite L. simpl.
replace _ with true. split. unfold incolbo. erewrite (proj2 (PosDec.eqb_eq _ _)). rewrite Bool.orb_true_r. split.
split. right. apply (proj2 (column3inv s t R (conj C K))). Qed.
Lemma col2suff {g ps s x y h} l: gridm g ps s -> desc (column1 x y h) s ->
  forallb (fun p => brickbp (evp g p)) l = true -> desc (column2 x y h l) s.
rewrite forallb_forall. intros [_ [T _]] C B. eenough _ as C1. intros t R. apply (inv1 column2inv R C1). split.
apply (desc1 C). intros p P. left. apply B in P. rewrite brickbp_equiv in P. pose proof (T p) as Tp.
rewrite P in Tp. inversion Tp. apply solidbrick. Qed.
Lemma col3suff {s x y h l p}: desc (column2 x y h l) s -> is_empty(ev (sg s) p) ->
  poss_mem p l = true -> desc(column3 x y h p) s.
unfold is_empty. intros C E P. apply desc1 in C. apply ListSet.set_mem_correct1 in P. eenough _ as C1.
intros t R. apply (inv1 column3inv R C1). split. apply (proj1 C). apply (proj2 C) in P. tauto. Qed.
Lemma applycol3 {x y h s p} g ps h1 qs: desc (column3 x y h p) s -> is_solid(ev (sg s) p) ->
  tobrickc x y (S h) g ps = (h1,qs) -> gridm g ps s -> gridm h1 qs s.
intros C B E M. apply desc1 in C. destruct C as [[[_[Q _]] _] H]. apply (applysolidc M Q E).
destruct M as [_[_[_ M]]]. pose proof (fdnil H B M) as G. intros r R. apply G. unfold incolbo. rewrite R.
split. Qed.
End Column.

Ltac usesolid1 := lazymatch goal with
  | [H:is_solid(ev _ ?p) |- _] => usesolid p H end.
Ltac col x y h := lazymatch goal with
  | [M:gridm _ _ _ |- _] => pose proof (colbsuff x y h M (Logic.eq_refl _)) end.
Ltac col1 x y := lazymatch goal with
  | [C:desc (column x ?z _) ?s, E:is_empty(ev (sg ?s) (x,y)) |- _] => let h := eval compute in (y-z) in
    pose proof (col1suff h C E (Logic.eq_refl _)) end.
Ltac col1s x y := lazymatch goal with
  | [C:desc (column1 x ?z ?h) ?s, B:is_solid(ev (sg ?s) (x,y)), M:gridm ?g ?ps ?s |- _] =>
    match eval compute in (tobrickc x z (S h) g ps) with | (?h1,?qs) =>
    apply (applycol1 g ps h1 qs C B (Logic.eq_refl _)) in M end end.
Ltac col2 x l := lazymatch goal with
  | [M:gridm ?g _ ?s, C:desc (column1 x _ _) ?s |- _] => pose proof (col2suff l M C (Logic.eq_refl _)) end.
Ltac col3 p := lazymatch goal with
  | [C:desc (column2 _ _ _ _) ?s, E:is_empty(ev (sg ?s) p) |- _] =>
    pose proof (col3suff C E (Logic.eq_refl _)) end.
Ltac col3s p := lazymatch goal with
  | [C:desc (column3 ?x ?y ?h p) ?s, B:is_solid(ev (sg ?s) p), M:gridm ?g ?ps ?s |- _] =>
    match eval compute in (tobrickc x y (S h) g ps) with | (?h1,?qs) =>
    apply (applycol3 g ps h1 qs C B (Logic.eq_refl _)) in M end end.

Lemma notbrickempty {g ps s p}: gridm g ps s -> is_empty (ev (sg s) p) -> ~(evp g p = is brick).
intros [_[T _]] E B. apply E. pose proof (T p) as P. rewrite B in P. inversion P. apply solidbrick. Qed.
Ltac brickempty p := lazymatch goal with
  | [M:gridm _ _ _, E:is_empty (ev _ p) |- False] => apply (notbrickempty M E (Logic.eq_refl _)) end.

Definition replaceq p g := if brickbp (evp g p) then Some(replaceg p qm g) else None.
Lemma replaceqm {ps s} p g h: replaceq p g = Some h -> gridm g ps s -> gridm h ps s.
unfold replaceq. destruct (_:bool) eqn:B; intros H; inversion H. rewrite brickbp_equiv in B.
intros [P[T V]]. split. tauto. split. intros q. epose proof replace_set as [R|R]. unfold evp in B.
rewrite B in R. inversion R. pose proof (T q) as Q. revert Q. destruct (proj2 R q) as [E|E]. rewrite E.
rewrite (proj1 R). rewrite B. unfold tilems. intros Q. inversion Q. apply matchb. tauto. unfold evp. rewrite E.
all:tauto. Qed.
Ltac relax p := lazymatch goal with
  | [M:gridm ?g ?ps ?s |- _] => match eval compute in (replaceq p g) with | Some ?h =>
  apply (replaceqm p g h (Logic.eq_refl _)) in M end end.
End Neg.

Module Cross.
Example g := PP.parse "
   BBB   
BBB+++BBB
  +   +  
   B B   
SB-+S+-BS
SB B B BS
SBBBBBBBS
SBBBBBBBS
SBBBBBBBS
 BBBBBBB 
".

Lemma pos: can_reach_pos g (8,0) (0,9).
Pos.init. Pos.dl (6,0). Pos.dl (5,2). Pos.dr (3,2). Pos.dr (1,3). Pos.dl (1,4). Pos.dr (3,4). Pos.dl (5,4).
Pos.drill (1,9). Pos.done. Qed.
Lemma neg: ~can_reach_pos g (0,0) (0,9).
Neg.init. Neg.until ((Neg.row 0 3 4)++(Neg.row 4 2 2)). Neg.until (Neg.row 1 5 4). Neg.box 1 5 4. Neg.stuck. Qed.
Theorem cr: cross g. apply (cross_sym (Logic.eq_refl _) (isrect g) pos neg). Qed.
End Cross.

Module BL.
Definition g := PP.parse "
++BBBBBBBBB++
BBBBBBBBBBBBB
BB++BBBBB++BB
BBBBBBBBBBBBB
+BBB+BBB+BBB+
+BBBBBBBBBBB+
+BBBB+B+BBBB+
+BB+BBBBB+BB+
+BBBBBBBBBBB+
+BBBBBBBBBBB+
+B++BB+BB++B+
+BBB+BBB+BBB+
+BBBBBBBBBBB+
+BBBBBBBBBBB+
+BBBB+B+BBBB+
+BBBBBBBBBBB+
+BB++BBB++BB+
+BBBBBBBBBBB+
+++BBB+BBB+++
BBBBBBBBBBBBB
++++BB+BB++++
BBBBBBBBBBBBB
BBBBBBBBBBBBB
BBBBBBBBBBBBB
BBBBBBBBBBBBB
BBBBBBBBBBBBB
BBBBBBBBBBBBB
BBBBBBBBBBBBB
BBBBBBBBBBBBB
".

Lemma pos: can_reach_pos g (12,0) (0,28).
Pos.init. Pos.strip 11 2 0. Pos.dl (11,1). Pos.strip 9 3 2. Pos.dr (11,3). Pos.dl (9,3). Pos.strip 8 2 4.
Pos.dl (8,5). Pos.strip 7 2 6. Pos.strip 7 3 7. Pos.drill (7,10). Pos.strip 6 2 10. Pos.strip 6 3 11.
Pos.dl (6,12). Pos.dl (7,12). Pos.dl (6,13). Pos.strip 5 3 14. Pos.dr (7,15). Pos.strip 7 3 16. Pos.dl (7,17).
Pos.dr (9,17). Pos.dl (11,4). Pos.dl (11,5). Pos.dl (11,6). Pos.dl (11,7). Pos.dl (11,8). Pos.dl (11,9).
Pos.dl (9,10). Pos.dl (5,15). Pos.strip 3 3 16. Pos.dr (5,17). Pos.dr (4,17). Pos.strip 4 4 18. Pos.dr (7,19).
Pos.dl (4,19). Pos.dl (5,19). Pos.strip 0 8 20. Pos.drill (0,28). Pos.done. Qed.

Ltac fork H := eenough _ as H.
Ltac unfork H := lazymatch goal with
  | [M:Neg.gridm _ _ ?s, R:Neg.reach1 ?s _ |- _] => apply (H s M R) end.
Ltac resume := lazymatch goal with
  | [_:Neg.gridm _ _ ?s |- forall t, _ -> _ -> False] => clear dependent s; intros ? ? ? end.
Ltac stuckleft := Neg.until (Neg.row 0 21 7); Neg.box 0 21 7.
Ltac split2 := lazymatch goal with
  | [M:Neg.gridm _ [?p;?q] _ |- _] => rewrite (Neg.gridm_app _ [p] [q] _) in M; destruct M as [?|?] end.

Lemma neg: ~can_reach_pos g (0,0) (0,28).
Neg.init. Neg.until (Neg.row 0 1 2). Neg.strip 0 1 2. Neg.splitsolid. Neg.until (Neg.row 1 3 3). Neg.strip 1 3 3.
Neg.splitsolid. Neg.until (Neg.row 2 5 3). fork H. Neg.strip 2 5 3. Neg.splitsolid. Neg.until (Neg.row 3 8 3).
Neg.relax (2,6). unfork H. Neg.until (Neg.row 3 8 3). Neg.relax (3,6). unfork H. stuckleft. resume. fork H.
Neg.strip 3 8 3. Neg.splitsolid. Neg.strip 4 9 2. Neg.splitsolid. Neg.until (Neg.row 4 12 3). Neg.strip 4 12 3.
Neg.splitsolid. Neg.until (Neg.row 5 15 3). Neg.strip 5 15 3. Neg.splitsolid. Neg.stuck. split2. stuckleft.
Neg.stuck. stuckleft. Neg.stuck. stuckleft. stuckleft. Neg.until (Neg.row 2 12 3). Neg.relax (4,9).
Neg.relax (4,10). unfork H. Neg.until (Neg.row 2 12 3). Neg.relax (5,9). unfork H. resume. stuckleft. split2.
stuckleft. Neg.until (Neg.row 3 8 3). Neg.strip 3 8 3. Neg.splitsolid. Neg.es (5,9). Neg.col 5 9 5.
Neg.strip 4 9 2. Neg.splitsolid. Neg.until (Neg.row 5 11 2). Neg.col 6 11 7. Neg.until (Neg.row 4 12 3).
Neg.strip 4 12 3. Neg.splitsolid. Neg.until (Neg.row 5 15 3). Neg.es (6,15). Neg.col1 6 15.
Neg.col2 6 [(5,16);(3,18);(4,18)]. Neg.until1 (Neg.row 6 16 2) [(5,16)]. Neg.stuck. Neg.usesolid1.
Neg.col3 (5,16). Neg.until1 [(5,16);(7,16)] [(6,16)]. split2. Neg.until1 (Neg.row 4 18 2) [(3,18)]. stuckleft.
Neg.usesolid1. Neg.col3 (3,18). Neg.until1 ([(5,18);(7,16)]++Neg.row 0 19 4) [(4,18);(6,16)]. Neg.splitapp.
Neg.stuck. stuckleft. Neg.usesolid1. Neg.col1 6 16. Neg.until1 (Neg.row 0 19 7) [(7,16)]. stuckleft.
Neg.col1s 6 16. Neg.stuck. Neg.col3s (5,16). Neg.brickempty (6,15). Neg.col3s (3,18). stuckleft. Neg.usesolid1.
Neg.col3 (4,18). Neg.until1 ([(7,16)]++Neg.row 0 19 4) [(5,18);(6,16)]. Neg.splitapp. Neg.stuck. stuckleft.
Neg.usesolid1. Neg.col1 6 16. Neg.until1 (Neg.row 0 19 7) [(7,16)]. stuckleft. Neg.col1s 6 16. Neg.stuck.
Neg.col3s (5,16). Neg.brickempty (6,15). Neg.col3s (4,18). stuckleft. Neg.col3s (3,18). stuckleft. Neg.stuck.
Neg.usesolid1. Neg.col1 6 16. Neg.until1 (Neg.row 0 19 7) [(7,16)]. stuckleft. Neg.col1s 6 16. Neg.stuck.
Neg.col3s (5,16). Neg.brickempty (6,15). Neg.stuck. Neg.stuck. Neg.es (5,13). Neg.col1 5 13.
Neg.until1 (Neg.row 0 19 7) [(6,13)]. stuckleft. Neg.col1s 5 13. Neg.stuck. Neg.stuck. stuckleft. Neg.stuck.
stuckleft. stuckleft. stuckleft. Neg.stuck. Qed.

Theorem cr: cross g. apply (cross_sym (Logic.eq_refl _) (isrect g) pos neg). Qed.
End BL.

Definition firsteq {A} (a:A) l := hasfirst (Logic.eq a) l.
Definition lasteq {A} (a:A) l := firsteq a (rev l).
Lemma firstin {A l} {a:A}: firsteq a l -> In a l. destruct l; simpl. tauto. intros H. symmetry in H. tauto. Qed.
Lemma lastin {A l} {a:A}: lasteq a l -> In a l. unfold lasteq. rewrite in_rev. apply firstin. Qed.
Lemma nildec {A} {l:list A}: l = [] \/ [] <> l. destruct l as [|a l]. tauto. right. apply nil_cons. Qed.
Lemma firsteq_app {A l m} {a:A}: [] <> l -> (firsteq a l <-> firsteq a (l++m)).
intros H. destruct l as [|b l]; simpl. destruct H. split. tauto. Qed.
Lemma lasteq_app {A l m} {a:A}: [] <> m -> (lasteq a m <-> lasteq a (l++m)).
unfold lasteq. rewrite rev_app_distr. intros H. apply firsteq_app. intros G. apply H. rewrite <- rev_involutive.
rewrite <- G. split. Qed.
Lemma lasteq_con {A l} {a b c:A}: lasteq c (b::l) <-> lasteq c (a::b::l).
replace (a::_) with ([a]++(b::l)). apply lasteq_app. apply nil_cons. split. Qed.
Lemma consecinv {A R a l} {P:A->Prop}: firsteq a l -> consec R l -> (forall b c, R b c -> P b -> P c) ->
  P a -> (forall b, In b l -> P b).
intros H C I. revert a H. induction l. intros ? []. intros b E. rewrite E. intros H x [X|X]. rewrite <- X.
apply H. destruct l as [|c]. destruct X. apply (IHl (proj2 C) c). split. apply (I _ _ (proj1 C) H). tauto. Qed.
Lemma reach_consec {s t}: can_reach s t <-> exists l, consec step l /\ firsteq s l /\ lasteq t l.
split. revert s. apply clos_refl_trans_ind_right. exists [t]. repeat split. intros x y Y [l[C[L R]]] _.
exists (x::l). destruct l as [|z l]. destruct L. simpl in L. rewrite L in Y. split. apply (conj Y C). split.
split. rewrite <- lasteq_con. tauto. intros [l[C[L R]]]. eapply (consecinv L C _ _ t (lastin R)). Unshelve.
intros ?? G H. eapply rt_trans. apply H. apply rt_step. apply G. apply rt_refl. Qed.
Lemma contains_ev {g p t}: ev g p = t -> contains g t \/ t = stone.
destruct p as [x y]. intros E. rewrite <- E. unfold ev. unfold evg. simpl.
epose proof nth_in_or_default as [H|H]. 2:rewrite H. epose proof nth_in_or_default as [G|G]. left. eexists.
split. apply H. apply G. rewrite G in H. destruct H. tauto. Qed.
Require Import ZArith.
Require Import Lia.

Module NeedB.
Definition adj p q := beside p q \/ above p q \/ above q p.
#[local] Instance adj_Symmetric : RelationClasses.Symmetric adj.
intros p q. unfold adj. unfold beside. tauto. Qed.

Lemma move_adj {g p q}: move g p q -> adj p q. unfold adj. intros H. inversion H; tauto. Qed.
Definition inrect w h (p:position) := fst p <= w /\ snd p <= h.
Definition path w h p q l := consec adj l /\ firsteq p l /\ lasteq q l /\ forall r, In r l -> inrect w h r.
Definition intersect {A} l m := exists (a:A), In a l /\ In a m.
Section Intersect.
Definition nb (b:bool):Z := if b then 1 else 0.
Definition delta0 f (p q r:position):Z := nb (PosDec.eqb q p && PosDec.eqb (f r) p).
Definition delta f p q r:Z := delta0 f p q r - delta0 f p r q.
Fixpoint deltal f p l:Z := match l with | q::((r::_) as m) => delta f p q r + deltal f p m | _ => 0 end.
Definition rt (p:position) := match p with | (x,y) => (S x,y) end.
Fixpoint sumy l x y:Z := match y with | 0 => 0 | S y => deltal rt (x,y) l + sumy l x y end.
Definition val l (p:position) := let (x,y) := p in sumy l (S x) y.

Lemma eqb2 {x y z w}: PosDec.eqb (x,y) (z,w) = ((x=?z)&&(y=?w))%bool.
destruct (PosDec.eqb _ _) eqn:B. rewrite PosDec.eqb_eq in B. inversion B. repeat (rewrite eqb_refl). split.
destruct (x=?z) eqn:X. destruct (y=?w) eqn:Y. apply beq_nat_true in X. apply beq_nat_true in Y.
destruct Bool.diff_false_true. rewrite <- B. rewrite PosDec.eqb_eq. rewrite X. rewrite Y. all:split. Qed.
Lemma eqbs {x y}: (S y=?x)=(x=?S y). apply eqb_sym. Qed.
Lemma eqbf1 {x y}: x=?y = true -> x=?S y = false.
destruct (x=?(S y)) eqn:B. revert B. repeat (rewrite eqb_eq). lia. split. Qed.
Lemma eqbf2 {x y}: x=?S y = true -> y=?S x = false.
destruct (y=?_) eqn:B. revert B. repeat (rewrite eqb_eq). lia. split. Qed.
Lemma eqbf3 {x y}: x=?S y = true -> y=?x = false.
destruct (y=?x) eqn:B. revert B. repeat (rewrite eqb_eq). lia. split. Qed.
Lemma eqbf4 {x y}: x=?y = true -> x=?S(S y) = false.
destruct (x=?S _) eqn:B. revert B. repeat (rewrite eqb_eq). lia. split. Qed.
Lemma delta0x {p q r}: adj q r -> nb (PosDec.eqb q p) =
  (delta0 rt p q r + delta0 rt (rt p) r q + delta0 below p q r + delta0 below (below p) r q)%Z.
unfold delta0. destruct p as [x y]. intros [[H|H]|[H|H]]. 1,4:destruct r as [u v]. 3,4:destruct q as [u v].
all: rewrite H; simpl; repeat (rewrite eqb2); destruct (_:bool) eqn:B; repeat (rewrite Bool.andb_false_r);
try split. all: rewrite Bool.andb_true_iff in B; rewrite eqbs in B; simpl in B; destruct B as [X Y];
repeat (rewrite eqbs). rewrite (eqbf3 X). rewrite (eqbf2 X). 2:rewrite (eqbf3 Y);rewrite (eqbf2 Y).
3: rewrite eqb_sym in X;rewrite (eqbf1 X);rewrite (eqbf4 X). 4:rewrite (eqbf1 Y);rewrite (eqbf4 Y).
all:repeat (rewrite Bool.andb_false_r);split. Qed.
Lemma deltax {p q r}: adj q r -> (nb (PosDec.eqb q p) - nb (PosDec.eqb r p))%Z =
  (delta rt p q r - delta rt (rt p) q r + delta below p q r - delta below (below p) q r)%Z.
intros H. rewrite (delta0x H). symmetry in H. rewrite (delta0x H). unfold delta. lia. Qed.
Lemma deltal1 {f l p q r}: deltal f p (q::r::l) = (delta f p q r+deltal f p (r::l))%Z. split. Qed.
Lemma deltalx {w h q r l} p: path w h q r l -> (nb (PosDec.eqb q p) - nb (PosDec.eqb r p))%Z =
  (deltal rt p l - deltal rt (rt p) l + deltal below p l - deltal below (below p) l)%Z.
intros [C[L[R _]]]. revert q L. induction l; intros q L. destruct L. destruct l as [|b l]. rewrite L. rewrite R.
simpl. lia. destruct C as [Q C]. rewrite L. erewrite (_:forall x y,(x-y)%Z=((x-_)+(_-y))%Z). rewrite (deltax Q).
rewrite <- lasteq_con in R. rewrite (IHl C R b). repeat (rewrite deltal1). lia. split. Unshelve. lia. Qed.
Lemma deltaedge {n q r}: delta0 rt (0,n) q r = 0%Z /\ delta0 below (n,0) q r = 0%Z.
unfold delta0. destruct r as [??]. simpl. repeat (rewrite eqb2). simpl. repeat (rewrite Bool.andb_false_r).
repeat split. Qed.
Lemma deltaledge {n l}: deltal rt (0,n) l = 0%Z /\ deltal below (n, 0) l = 0%Z.
induction l. repeat split. destruct l as [|b l]. repeat split. repeat (rewrite deltal1). rewrite (proj1 IHl).
rewrite (proj2 IHl). unfold delta. repeat (rewrite (proj1 deltaedge); rewrite (proj2 deltaedge)). repeat split.
Qed.
Lemma sumx {l w h x y}: path w h (0,0) (w,h) l -> y <= h -> let b := ((x=?0)&&(0<?y))%bool in
  sumy l (S x) y = (sumy l x y - deltal below (x,y) l - nb b)%Z.
intros H. induction y. rewrite (proj2 deltaledge). unfold "<?". rewrite Bool.andb_false_r. split. simpl.
intros Y. rewrite IHy. set (nb _) as b. set (nb _) as c. pose proof (deltalx (x,y) H) as X.
replace (nb _) with ((c-b)%Z) in X. replace (nb _) with (0%Z) in X. simpl in X. lia. 1,2:rewrite eqb2.
destruct (h=?y) eqn:B. rewrite eqb_eq in B. lia. rewrite Bool.andb_false_r. split. unfold b. unfold c.
rewrite (eqb_sym 0). destruct x. destruct y. 1,2,3:split. lia. Qed.

Lemma delta0inx {x y q r}: delta0 below (x,y) q r = 0%Z \/ q = (x,y).
unfold delta0. destruct (PosDec.eqb _ _) eqn:B. rewrite <- PosDec.eqb_eq. all:tauto. Qed.
Lemma deltainx {x y l}: deltal below (x,y) l = 0%Z \/ In (x,y) l.
induction l. left. split. destruct l as [|b l]. left. split. rewrite deltal1. destruct IHl as [H|H].
rewrite H. unfold delta. simpl. epose proof delta0inx as [E|E]. rewrite E. epose proof delta0inx as [F|F].
rewrite F. 1,2,3:tauto. right. right. tauto. Qed.
Lemma cellx {l w h q r}: path w h (0,0) (w,h) l -> (snd r <= h) -> right q r -> val l q = val l r \/ In q l.
destruct r as [x y]. intros P Y Q. rewrite Q. unfold val. rewrite (sumx P Y). epose proof deltainx as [H|H].
rewrite H. simpl. lia. tauto. Qed.

Lemma delta0iny {x y q r}: delta0 rt (S x,y) q r = 0%Z \/ r = (x,y).
unfold delta0. destruct (PosDec.eqb (rt r) _) eqn:B. rewrite PosDec.eqb_eq in B. destruct r as [u v].
inversion B. tauto. rewrite Bool.andb_false_r. tauto. Qed.
Lemma deltainy {x y l}: deltal rt (S x,y) l = 0%Z \/ In (x,y) l.
induction l. left. split. destruct l as [|b l]. left. split. rewrite deltal1. destruct IHl as [H|H].
rewrite H. unfold delta. simpl. epose proof delta0iny as [E|E]. rewrite E. epose proof delta0iny as [F|F].
rewrite F. 1,2,3:tauto. right. right. tauto. Qed.
Lemma celly {q r} l: above q r -> val l q = val l r \/ In q l.
destruct q as [x y]. intros R. rewrite R. unfold val. simpl. epose proof deltainy as [H|H]. rewrite H. simpl.
lia. tauto. Qed.

Lemma celladj {l w h q r}: path w h (0,0) (w,h) l -> inrect w h q -> adj q r ->
  val l q = val l r \/ In q l \/ In r l.
assert (val l r = val l q -> val l q = val l r) as E. symmetry. tauto. intros P [_ Y] [[H|H]|[H|H]].
replace (snd q) with (snd r) in Y. 1,3:pose proof (cellx P Y H); tauto. rewrite H. destruct r. split.
all:pose proof (celly l H); tauto. Qed.
Lemma cellpath {l m w h q r}: path w h (0,0) (w,h) l -> path w h q r m -> val l q = val l r \/ intersect l m.
intros P. revert q. induction m. intros ? [_ [[] _]]. destruct m as [|b m]. intros q [_ [L [R _]]]. rewrite L.
rewrite R. tauto. intros q [[A C] [L[R I]]]. rewrite <- lasteq_con in R. destruct (IHm b) as [H|[x[X Y]]].
unfold path. split. tauto. split. split. split. tauto. intros ? ?. apply I. right. tauto.
epose proof (celladj P _ A) as [K|[K|K]]. rewrite L. rewrite K. tauto. 1,2:right; eexists; split; try apply K;
simpl; tauto. right. eexists. split. apply X. right. tauto. Unshelve. apply I. left. split. Qed.

Lemma sumy0 {y l}: sumy l 0 y = 0%Z.
induction y. split. simpl. rewrite (proj1 deltaledge). lia. Qed.

Theorem rectint {w h l m}: path w h (0,0) (w,h) l -> path w h (w,0) (0,h) m -> intersect l m.
intros L M. eassert _ as I. destruct M as [_[_[R _]]]. apply (lastin R). destruct h. eexists. split. 2:apply I.
apply firstin. unfold path in L. tauto. pose proof (cellpath L M) as [H|H]. revert H. unfold val.
replace (sumy _ _ _) with (0%Z). rewrite (sumx L). rewrite sumy0. epose proof deltainx as [E|E]. rewrite E.
simpl. lia. eexists. apply (conj E I). constructor. split. tauto. Qed.
End Intersect.

Section NeedB.
Context {g:grid tile}.
Hypothesis nobrick: ~contains g brick.
Lemma empty_rect {w h p}: rect (S w) (S h) g -> is_empty (ev g p) -> inrect w h p.
intros R. destruct p as [x y]. unfold ev. destruct (Compare_dec.le_lt_dec x w) as [X|X].
destruct (Compare_dec.le_lt_dec y h) as [Y|Y]. intros _. apply (conj X Y). rewrite (nth_y R Y).
2: rewrite (nth_x R X). all:rewrite empty_equiv; intros H; inversion H. Qed.
Definition ps p := {|sg:=g;sp:=p;sd:=[]|}.
Lemma stepmove {p s}: step (ps p) s -> ps (sp s) = s /\ move g p (sp s) /\ is_empty (ev g (sp s)).
intros H. inversion H. repeat split; tauto. destruct (contains_ev H6) as [C|C]. destruct (nobrick C).
inversion C. apply app_eq_nil in H3. apply proj2 in H3. inversion H3. Qed.
Lemma ginv: Neg.inv (fun s => ps (sp s) = s).
intros s t H E. rewrite <- E in H. apply stepmove in H. tauto. Qed.
Lemma consecmap {A B P Q l} {f:A->B}: consec P l -> (forall a b, In a l -> P a b -> (Q (f a) (f b)):Prop) ->
  consec Q (map f l).
induction l. split. destruct l as [|b l]. split. intros [L C] I. split. apply I. left. split. apply L.
apply (IHl C). intros ???. apply I. right. tauto. Qed.
Lemma mapfirst {A B l a} {f:A->B}: firsteq a l -> firsteq (f a) (map f l).
destruct l. intros []. apply f_equal. Qed.
Lemma maplast {A B l a} {f:A->B}: lasteq a l -> lasteq (f a) (map f l).
unfold lasteq. rewrite <- map_rev. apply mapfirst. Qed.
Lemma consecin {A R l} {a:A}: consec R l -> In a l -> firsteq a l \/ exists b, In b l /\ R b a.
induction l. intros _ []. destruct l. intros _ [E|[]]. left. rewrite E. split. intros [H C] [E|E]. left.
rewrite E. split. right. destruct (IHl C E) as [G|[b[B G]]]. eexists. split. left. split. rewrite G. apply H.
eexists. split. right. apply B. apply G. Qed.
Lemma reachpos1 {p q w h}: rect (S w) (S h) g -> can_reach_pos g p q
  -> inrect w h p -> exists l, consec step (map ps l) /\ path w h p q l.
intros G [d[k R]] P. rewrite reach_consec in R. destruct R as [l[C[L R]]]. exists (map sp l). eenough _ as E.
split. replace _ with l. apply C. rewrite map_map. symmetry. erewrite map_ext_in. apply map_id. simpl. apply E.
split. apply (consecmap C). intros s t I. rewrite <- (E _ I). intros H. apply stepmove in H.
destruct H as [_[H _]]. apply (move_adj H). split. erewrite (_:p=_). apply (mapfirst L). split. erewrite (_:q=_).
apply (maplast R). intros r. rewrite in_map_iff. intros [s[F I]]. rewrite <- F.
destruct (consecin C I) as [H|[t[J H]]]. destruct l. destruct I. rewrite H. rewrite <- L. apply P. apply E in J.
rewrite <- J in H. apply stepmove in H. apply empty_rect. apply G. tauto. apply (consecinv L C ginv). split.
Unshelve. all: split. Qed.
Lemma consec_iff {A P l m} {a:A}: consec P (l++a::m) <-> consec P (l++[a]) /\ consec P (a::m).
split. intros H. split. rewrite nxt in H. 1,2:apply consec1 in H; tauto. intros [??]. apply consec2; tauto. Qed.
Theorem nocross: ~cross g.
intros [w[h[G[H1[H2[H3 _]]]]]]. epose proof (reachpos1 G H1 _) as [l L]. epose proof (reachpos1 G H2 _) as [m M].
destruct (rectint (proj2 L) (proj2 M)) as [p[L1 M1]]. apply in_split in L1. destruct L1 as [l1[l2 L1]].
rewrite L1 in L. rewrite map_app in L. simpl in L. rewrite consec_iff in L. destruct L as [[L2 _] [_[L3 _]]].
apply in_split in M1. destruct M1 as [m1[m2 M1]]. rewrite M1 in M. rewrite map_app in M. simpl in M. apply H3.
rewrite consec_iff in M. destruct M as [[_ M2] [_[_[M3 _]]]]. repeat eexists. rewrite reach_consec.
exists (map ps (l1++p::m2)). split. rewrite map_app. simpl. rewrite consec_iff. apply (conj L2 M2). split.
erewrite (_:_=(ps _)). apply mapfirst. rewrite nxt. eenough _ as N. rewrite <- (firsteq_app N).
erewrite (firsteq_app N). rewrite <- nxt. apply L3. symmetry. intros H. apply app_eq_nil in H. apply proj2 in H.
inversion H. erewrite (_:_=(ps _)). apply maplast. eenough _ as N. rewrite <- (lasteq_app N).
erewrite (lasteq_app N). apply M3. apply nil_cons. Unshelve. 1,2:split; simpl; lia. 3,4:split. Qed.
End NeedB.
End NeedB.

Module NeedL.
Definition canl g x y:bool := supportedb g (S x,y)&&emptyb (ev g (x,y)).
Definition canr g x y:bool := supportedb g (x,y)&&emptyb (ev g (S x,y)).
Fixpoint gl g x y := match x with | 0 => 0 | S u => if canl g u y then gl g u y else x end.
Fixpoint gr g m x y := match m with | 0 => x | S m => if canr g x y then gr g m (S x) y else x end.
Definition sl s := let (x,y) := sp s in gl (sg s) x y.
Definition sr s := match (sp s,sg s) with | (x,y,g) => gr g (length (nth y g [])) x y end.
Lemma sl0 s: sl s <= fst (sp s).
destruct s as [[x?]??]. unfold sl. simpl. induction x. constructor. simpl.
destruct (_:bool); constructor. tauto. Qed.
Lemma sr0 s: sr s >= fst (sp s).
destruct s as [[x?]??]. unfold sr. simpl. generalize x. induction (length _).
constructor. intros u. simpl. destruct (_:bool). eapply le_trans. 2:apply IHn0. all:repeat constructor. Qed.
Lemma sl1 {s x}: sl s = S x -> canl (sg s) x (snd (sp s)) = false.
destruct s as [[u y]??]. unfold sl. simpl. induction u; intros H. inversion H. simpl in H.
destruct (_:bool) eqn:B in H. apply (IHu H). revert B. inversion H. tauto. Qed.
Lemma sr1 {s}: canr (sg s) (sr s) (snd (sp s)) = false.
destruct s as [[u y]??]. unfold sr. simpl. set (length _) as m. assert (m+u>=(length (nth y sg0 []))) as H.
unfold m. lia. revert H. generalize u. clear u. induction m; intros u; simpl; intros U. unfold canr.
replace _ with stone. apply Bool.andb_false_r. unfold ev. unfold evg. symmetry. apply nth_overflow. simpl. lia.
destruct (canr _ u y) eqn:B. rewrite <- add_succ_r in U. apply (IHm _ U). tauto. Qed.
Lemma sl2 {s x}: sl s <= x < fst (sp s) -> canl (sg s) x (snd (sp s)) = true.
destruct s as [[u y]??]. unfold sl. simpl. induction u. lia. simpl. destruct (canl _ u y) eqn:B. intros [L R].
inversion R; tauto. lia. Qed.
Lemma sr2 {s x}: fst (sp s) <= x < sr s -> canr (sg s) x (snd (sp s)) = true.
destruct s as [[u y]??]. unfold sr. simpl. generalize u. clear u. induction (length _); intros u; simpl. lia.
destruct (canr _ u _) eqn:B. intros [L R]. assert (x=u\/u<x) as [H|H]. lia. rewrite H. tauto.
apply (IHn  _ (conj H R)). lia. Qed.
Lemma lrempty {s p}: sl s <= fst p <= sr s -> snd (sp s) = snd p -> p = sp s \/ is_empty (ev (sg s) p).
destruct p as [x y]. rewrite empty_equiv. simpl. intros H Y. rewrite <- Y.
eenough (_\/(x=S(pred x)/\_)\/x=fst(sp s)) as [G|[[X G]|X]]. 2,3:rewrite X. 1,2:right; eapply proj2;
eapply Bool.andb_true_iff. apply (sl2 G). apply (sr2 G). destruct (sp s). tauto. lia. Qed.
Definition withp p s := {|sp:=p;sg:=sg s;sd:=sd s|}.
Lemma movel {u x y g d}: gl g x y <= u <= x -> can_reach {|sp:=(x,y);sg:=g;sd:=d|} {|sp:=(u,y);sg:=g;sd:=d|}.
induction x. intros ?. replace u with 0. apply rt_refl. lia. simpl. intros [L R]. inversion R. apply rt_refl.
destruct (canl _ _ _) eqn:C. unfold canl in C. rewrite Bool.andb_true_iff in C. eapply rt_trans. 2:apply IHx.
apply rt_step. apply step_move. apply move_beside. left. split. rewrite supported_equiv. tauto.
apply empty_equiv. tauto. lia. lia. Qed.
Lemma mover {m u x y g d}: x <= u <= gr g m x y -> can_reach {|sp:=(x,y);sg:=g;sd:=d|} {|sp:=(u,y);sg:=g;sd:=d|}.
generalize x. clear x. induction m. simpl. intros x H. replace u with x. apply rt_refl. lia. simpl. intros x H.
assert (x=u\/x<u) as [E|E]. lia. rewrite E. apply rt_refl. destruct (canr _ _ _) eqn:C. unfold canr in C.
rewrite Bool.andb_true_iff in C. eapply rt_trans. 2:apply IHm. apply rt_step. apply step_move. apply move_beside.
right. split. apply supported_equiv. tauto. apply empty_equiv. tauto. lia. lia. Qed.
Lemma moveh {s p}: snd p = snd (sp s) -> sl s <= fst p <= sr s -> can_reach s (withp p s).
destruct s as [[??]??]. unfold withp. destruct p as [??]. unfold sl. unfold sr. simpl. intros E [L R].
rewrite E. eenough (_\/_) as [H|H]. apply (movel H). apply (mover (conj H R)). lia. Qed.

Section NeedL.
Context {g:grid tile}.
Hypothesis noladder: ~contains g ladder.

Definition valid s := Neg.validd s /\ forall p, (In p (sd s) /\ ev g p = brick) \/
  (~In p (sd s) /\ ev (sg s) p = ev g p).
Lemma validinv: Neg.inv valid.
intros s t H [V E]. eenough _ as T. split. apply T. intros p. destruct (Neg.stepev p H) as
[[F D]|[[F[_ D]]|[F[_[_ D]]]]]. rewrite <- D. rewrite F. apply E. destruct (E p) as [[_ G]|[G _]]. right. split.
erewrite (_:_=_++[]). apply NoDup_remove_2. rewrite <- D. apply (proj1 V). rewrite G. apply F. destruct G.
rewrite D. rewrite in_app_iff. simpl. tauto. destruct (E p) as [[G _]|[_ G]]. apply proj1 in T. rewrite D in T.
inversion T. tauto. left. rewrite D. rewrite <- G. simpl. tauto. apply (Neg.validdinv _ _ H V). Unshelve.
symmetry. apply app_nil_r. Qed.
Lemma valid1 {s} p: valid s -> ev (sg s) p = ev g p \/ (ev (sg s) p = air /\ ev g p = brick).
intros [[_ F] G]. destruct (G p) as [[P Q]|[_ P]]. apply F in P. all:tauto. Qed.
Lemma validladder {s p}: valid s -> ev (sg s) p <> ladder.
intros V. destruct (valid1 p V) as [P|[P _]]; rewrite P; intros H. destruct (contains_ev H) as [K|K].
apply (noladder K). inversion K. inversion H. Qed.
Lemma validdown {s t}: valid s -> step s t -> snd (sp s) <= snd (sp t).
intros V H. inversion H. 2,3:constructor. inversion H0. rewrite H4. destruct p. simpl. lia. rewrite <- H2 in V.
destruct (validladder V H5). simpl. rewrite (Neg.besidey H4). lia. Qed.

Definition dabove y s := forall p, In p (sd s) -> snd p <= y.
Definition yge (p q:position) := snd p >= snd q.
Definition lvl0 y s := valid s /\ snd (sp s) = y /\ dabove y s.
Definition lvl y s := valid s /\ snd (sp s) = y /\ dabove (S y) s.
Lemma lvl1 {y s}: lvl0 y s -> lvl y s.
unfold lvl. intros [?[? D]]. assert (dabove (S y) s). intros p P. constructor. apply (D _ P). tauto. Qed.
Inductive drop y t: state -> Prop :=
  | drop0 s: lvl0 (S y) t -> Neg.free t -> t=withp (below(sp s)) s -> drop y t s
  | predrop s u: step s u -> lvl y u -> drop y t u -> drop y t s.
Lemma abovey {p q}: above p q -> snd q = S (snd p). destruct p. intros H. rewrite H. split. Qed.
Lemma dropf {y s t}: step s t -> lvl y s -> lvl y t \/ drop y t s.
intros T L. pose proof (validinv _ _ T (proj1 L)) as V. inversion T. 1,3:rewrite <- H1 in L; rewrite <- H2 in V.
3:rewrite <- H5 in L; rewrite <- H6 in V; assert (snd pb=S y) as Y. all:unfold lvl in L; simpl in L;
destruct L as [W[Z A]]. inversion H. right. apply drop0. split. apply V. split. simpl. rewrite (abovey H3).
apply f_equal. 1,2,3:tauto. rewrite H3. split. destruct (validladder W H4). 1,2,4:left; split; try (apply V);
repeat split. simpl. rewrite <- (Neg.besidey H3). 1,2,3,5:tauto. intros r R. apply A. simpl.
rewrite in_app_iff. tauto. intros r [R|R]. rewrite <- R. rewrite Y. constructor. apply (A _ R).
rewrite (abovey H0). apply f_equal. rewrite <- Z. symmetry. apply Neg.besidey. tauto. Qed.
Inductive drops p:nat -> state -> Prop :=
  | samelvl y s: lvl y s -> snd p = y -> Neg.reach1 s p -> drops p y s
  | drop1 y t s: lvl y s -> drop y t s -> drops p (S y) t -> drops p y s.
Definition drophelper p s := (forall y, lvl y s -> drops p y s).
Lemma dropt {y s t}: drop y t s -> lvl0 (S y) t /\ Neg.free t. intros H. induction H; tauto. Qed.
Lemma drops1 {s p} y: Neg.reach1 s p -> lvl y s -> drops p y s.
intros [t [R T]]. eenough (drophelper p s) as H. apply H. clear y. revert s R. apply clos_refl_trans_ind_right.
intros y L. apply samelvl. tauto. rewrite <- T. unfold lvl in L. tauto. eexists. split. apply rt_refl. tauto.
intros s u H D R y L. pose proof (dropf H L) as [M|M]. apply D in M.
destruct M as [?? U P [v[V1 V2]]|??? U D1 D2]. apply samelvl; try tauto. exists v. split. eapply rt_trans.
apply rt_step. apply H. 1,2:tauto. eapply drop1. 2:eapply predrop. 4:apply D1. 1,2,3,4:tauto. eapply drop1.
tauto. apply M. apply D. apply lvl1. apply (proj1 (dropt M)). Qed.

Lemma validhold {s p}: valid s -> holdableb (ev (sg s) p) = holdableb (ev g p).
intros V. epose proof (valid1 _ V) as [P|[P Q]]; rewrite P; try (rewrite Q); split. Qed.
Lemma validsupp {s p}: valid s -> supportingb (ev (sg s) p) = supportingb (ev g p) \/
  (In p (sd s) /\ ev g p = brick).
intros V. destruct (proj2 V p) as [H|[_ H]]. tauto. rewrite H. tauto. Qed.
Lemma validsupp1 {s p}: valid s -> supported (sg s) p -> supported g p.
intros V. unfold supported. repeat (rewrite holdable_equiv; rewrite supporting_equiv). rewrite (validhold V).
epose proof (validsupp V) as [H|[_ H]]; rewrite H; tauto. Qed.
Lemma validsupp2 {s p y}: lvl0 y s -> snd p = y -> supportedb (sg s) p = supportedb g p.
unfold supportedb. intros [V[Y D]] P. rewrite (validhold V). epose proof (validsupp V) as [H|[H _]].
rewrite H. split. apply D in H. erewrite abovey in H. rewrite P in H. lia. split. Qed.

Lemma solidinv {x y}: Neg.rinv (fun s => snd (sp s) >= y) (fun s => is_solid (ev (sg s) (x,y))).
intros s t H Y B. destruct (Neg.solidinv H B) as [K|[[Z [E _]] _]]. tauto. apply Neg.besidey in E. destruct y.
inversion Z. rewrite E in Y. simpl in Y. lia. Qed.
Lemma abovex {p q}: above p q -> fst p = fst q. intros H. rewrite H. destruct p. split. Qed.

Definition cantl x y s := valid s /\ (is_solid (ev (sg s) (pred x,y)) \/ ~supported g (x,y) \/ x=0) /\
  snd (sp s)>=y /\ (snd (sp s)=y -> fst (sp s)>=x).
Definition cantr x y s := valid s /\ (is_solid (ev (sg s) (S x,y)) \/ ~supported g (x,y)) /\
  snd (sp s)>=y /\ (snd (sp s)=y -> fst (sp s)<=x).
Lemma cantl_beside {x y s q}: cantl x y s -> beside (sp s) q -> is_empty (ev (sg s) q) -> supported (sg s) (sp s)
  -> snd (sp s) = y -> fst q >= x.
intros [V[H[_ X]]] [B|B] E P Y. destruct q as [u v]. pose proof (X Y) as X1. revert X1 Y P. rewrite B. simpl.
clear X. intros X Y P. revert H. inversion X. rewrite <- Y. intros [C|[C|C]]. destruct (E C). destruct C.
apply (validsupp1 V). tauto. inversion C. tauto. rewrite B. apply X in Y. revert Y. destruct (sp s). simpl.
lia. Qed.
Lemma cantr_beside {x y s q}: cantr x y s -> beside (sp s) q -> is_empty (ev (sg s) q) -> supported (sg s) (sp s)
  -> snd (sp s) = y -> fst q <= x.
intros [V[H[_ X]]] [B|B] E P Y; pose proof (X Y) as X1. revert X1. rewrite B. destruct q. simpl. lia. revert P E.
destruct (sp s). rewrite B. simpl. inversion X1. unfold is_empty. simpl in Y,H0. rewrite Y. rewrite H0. intros J.
apply (validsupp1 V) in J. tauto. simpl in H0. lia. Qed.
Lemma cantlinv {x y}: Neg.inv (cantl x y).
intros s t H C. split. apply (validinv _ _ H (proj1 C)). split. destruct C as [_[[C|C] [Y _]]]. left.
apply (solidinv _ _ H Y C). tauto. pose proof (validdown (proj1 C) H) as J. destruct (proj2 C) as [_ [K L]].
split. lia. intros ?. eenough _ as Y. pose proof (L Y) as X. revert X. inversion H. 2,3:tauto. inversion H1.
1,2:apply abovex in H5; simpl; rewrite H5; tauto. intros X. rewrite <- H3 in C. apply (cantl_beside C).
apply H5. apply H2. apply H6. rewrite H3. apply Y. lia. Qed.
Lemma cantrinv {x y}: Neg.inv (cantr x y).
intros s t H C. split. apply (validinv _ _ H (proj1 C)). split. destruct C as [_[[C|C] [Y _]]]. left.
apply (solidinv _ _ H Y C). tauto. pose proof (validdown (proj1 C) H) as J. destruct (proj2 C) as [_ [K L]].
split. lia. intros ?. eenough _ as Y. pose proof (L Y) as X. revert X. inversion H. 2,3:tauto. inversion H1.
1,2:apply abovex in H5; simpl; rewrite H5; tauto. intros X. rewrite <- H3 in C. apply (cantr_beside C).
apply H5. apply H2. apply H6. rewrite H3. apply Y. lia. Qed.

Lemma natpair {a b c d:nat}: (a,b)=(c,d) <-> (a=c /\ b=d). apply pair_equal_spec. Qed.
Definition minx x (p:position) := (min x (fst p),snd p).
Lemma minxeq {x p}: fst p <= x -> p = minx x p. destruct p. unfold minx. rewrite natpair. simpl. lia. Qed.
Definition droplast {A} n (l:list A) := firstn (length l - n) l.
Lemma firstn_in {A n l} {a:A}: In a (firstn n l) -> In a l.
revert l. induction n. intros ? []. intros [|b l]. intros []. intros [H|H]; simpl. tauto. apply IHn in H.
tauto. Qed.
Lemma droplast_in {A n l} {a:A}: In a (droplast n l) -> In a l. apply firstn_in. Qed.
Lemma droplast_con {A n l} {a:A}: In (droplast n (a::l)) [droplast n l; a::droplast n l].
unfold droplast. set (_-_) as m. replace (_-_) with (pred m). simpl. destruct m; tauto. unfold m.
replace (length _) with (S(length l)). lia. split. Qed.
Lemma dropfilter_conn {A n l f} {a:A}: filter f (droplast n (a::l)) = filter f (droplast n l) \/
  (filter f (droplast n (a::l)) = a::(filter f (droplast n l)) /\ f a = true).
epose proof droplast_con as [H|[H|[]]]; rewrite <- H. tauto. simpl. destruct (f a); tauto. Qed.
Lemma droplast_app {A n l} {a:A}: droplast (S n) (l++[a]) = droplast n l.
unfold droplast. erewrite len1. 2:split. rewrite firstn_app. replace (_-_-_) with 0. simpl. apply app_nil_r.
lia. Qed.
Lemma droplast0 {A} {l:list A}: droplast 0 l = l. unfold droplast. rewrite sub_0_r. apply firstn_all. Qed.
Definition mimic n l r r1 y s t := lvl y s /\ lvl y t /\ cantl l y t /\ cantr r y t /\ sp s = minx r1 (sp t) /\
  filter (fun p => snd p =? S y) (sd s) = (filter (fun p => ((fst p <? r1)&&(snd p =? S y))%bool)
  (droplast n (sd t))) /\ forall x, l<=x<=min r r1 -> is_empty (ev (sg s) (x,y)).
Lemma mimiceq {n l r r1 y s t p}: mimic n l r r1 y s t -> snd p = S y -> In (ev (sg t) p) [ev (sg s) p;air].
intros [[[_ Ks]_][[[[_ Ht]Kt]_][_[_[_[F _]]]]]] Y. simpl. destruct (Kt p) as [[H _]|[H K]]. apply Ht in H.
rewrite H. tauto. rewrite K. destruct (Ks p) as [[L _]|[_ L]]. destruct H. eapply droplast_in. eapply proj1.
rewrite <- filter_In. fold position in F. rewrite <- F. rewrite filter_In. split. tauto. rewrite eqb_eq.
tauto. tauto. Qed.
Lemma mimicsupp {n l r r1 y s t}: mimic n l r r1 y s t -> supported (sg t) (sp s) -> supported (sg s) (sp s).
intros M. unfold supported. repeat (rewrite holdable_equiv; rewrite supporting_equiv). intros [H|H].
destruct M as [[Vs _][[Vt _] _]]. revert H. rewrite (validhold Vs). rewrite (validhold Vt). tauto. right.
epose proof (mimiceq M _) as [E|[E|[]]]. rewrite E. tauto. rewrite <- E in H. inversion H. Unshelve.
destruct M as [[_[Y _]] _]. rewrite <- Y. apply abovey. split. Qed.
Lemma mimicstep {l r r1 y t u} n: step t u -> lvl y u -> exists m, forall s, mimic m l r r1 y s t ->
  exists v, (s=v \/ step s v) /\ mimic n l r r1 y v u.
intros H Lu. epose proof (conj(cantlinv _ _ H)(cantrinv _ _ H)) as K. revert K Lu. inversion H; intros [K J] Lu.
1,2:exists n. 3:exists (S n). all:intros s M; pose proof (mimicsupp M) as SP;
pose proof M as [Ls[Lt[L1[R1[P[F E]]]]]]; pose proof (K L1) as L; pose proof (J R1) as R; clear J K.
inversion H0. apply abovey in H4. apply proj2 in Lt,Lu. simpl in Lt,Lu. lia.
destruct (validladder (proj1 Lt) H5). assert (sp s = minx r1 q \/ (p = sp s /\ q = minx r1 q)) as [J|[J K]].
rewrite P. simpl. destruct p. destruct q. revert H4. unfold beside. unfold right. unfold minx. simpl.
repeat (rewrite natpair). lia. exists s. unfold mimic. simpl. tauto. exists (withp q s). split. right.
destruct s. simpl in J. apply step_move. apply move_beside. rewrite <- J. tauto. apply SP. rewrite <- J.
tauto. simpl. destruct Lu as [_[Y _]]. replace q with (fst q,y). apply E. split. destruct L as [_[_[_ L]]].
apply L. apply Y. destruct R as [_[_[_ R]]]. apply R in Y. destruct q. revert K Y. unfold minx. rewrite natpair.
simpl. lia. rewrite <- Y. destruct q. split. unfold mimic. destruct s. simpl. split. destruct Ls as [?[_ ?]].
destruct Lu as [_[? _]]. unfold lvl. tauto. tauto. epose proof dropfilter_conn as [D|[D X]]. exists s.
unfold mimic. simpl. rewrite D. tauto. rewrite Bool.andb_true_iff in X. assert (fst ps<r1) as P1.
rewrite (abovex H1). rewrite <- ltb_lt. tauto. assert (p=minx r1 p) as P2. apply minxeq. revert H0.
unfold beside. unfold right. destruct ps. destruct p. revert P1. repeat (rewrite natpair). simpl. lia.
destruct s as [o gs ds]. simpl in P. rewrite <- P2 in P. eexists. eenough _ as B. eenough _ as A.
eenough _ as ST. split. right. apply ST. 2:{ eapply step_destroy. rewrite P. apply H0. apply H1.
destruct Lt as [_[W _]]. replace ps with (fst ps,y). apply E. split. apply (cantl_beside L1 H0 H2 H4 W).
pose proof (cantr_beside R1 H0 H2 H4 W). lia. rewrite <- W. simpl. rewrite (Neg.besidey H0). destruct ps. split.
apply B. apply SP. rewrite P. tauto. apply A. } unfold mimic. split. pose proof (dropf ST Ls) as [J|J]. apply J.
apply dropt in J. destruct J as [[_[J _]] _]. revert J. destruct Ls as [_[K _]]. rewrite <- K. simpl. lia. split.
tauto. split. tauto. split. tauto. split. simpl. rewrite P. apply P2. split. simpl. rewrite (proj2 X).
simpl in F. rewrite F. symmetry. apply D. intros v V. simpl. rewrite (Neg.setneq A). apply E. apply V. intros J.
revert X. rewrite eqb_eq. rewrite J. simpl. lia. rewrite set_equiv. epose proof replace_set as [J|J]. 2:apply J.
unfold ev in B. rewrite B in J. inversion J. epose proof (mimiceq M _) as [K|[K|[]]]; simpl in K;
rewrite <- K in H3. apply H3. inversion H3. exists s. unfold mimic. simpl in F. rewrite droplast_app in F. simpl.
tauto. Unshelve. rewrite <- eqb_eq. tauto. Qed.

(* We allowed the player to start in a solid tile to simplify the initial definitions.
That results in an edge case here *)
Definition lvle y s t := lvl0 y s /\ lvl0 y t /\ ((Neg.free s /\ Neg.free t) \/ (sg s = sg t /\ sd s = sd t)).
Definition leftof y s t := lvle y s t /\ sr s <= sr t.
Definition inside y s t := leftof y s t /\ sl s >= sl t.

Lemma mimicinside {y l r r1 t u}: r1 > sr u -> drop y u t -> exists n, forall s, mimic n l r r1 y s t ->
  exists v, can_reach s v /\ inside (S y) u v.
intros R D. induction D. exists 0. intros t [Lt[Ls[_[_[P [D _]]]]]].
assert (forall x, x<r1 -> emptyb (ev (sg s) (x,S y)) = true -> emptyb (ev (sg t) (x,S y)) = true) as E.
intros x X. apply proj1 in Lt. epose proof (proj2 (proj1 Ls) _) as [[I _]|[_ E]]. 2:rewrite E.
rewrite (proj2 (proj1 Lt)). split. eapply proj1. rewrite <- filter_In. fold position in D. rewrite D.
rewrite filter_In. rewrite droplast0. simpl. rewrite eqb_refl. rewrite <- ltb_lt in X. rewrite X. tauto.
epose proof (valid1 _ Lt) as [J|[J _]]; rewrite J; tauto. pose proof (proj1 (proj2 H)) as Y.
exists (withp (sp u) t). destruct t. eenough _ as Lw. eenough _ as A. eenough _ as X1. eenough _ as X.
rewrite <- (minxeq X) in P. assert (sg s=sg u) as G. rewrite H1. destruct s. split. eenough _ as F. split.
apply rt_step. apply step_move. apply move_down. simpl in P. rewrite P. apply A. apply F. unfold withp. simpl.
split. split. split. tauto. split. apply Lw. left. tauto. 1,2:unfold withp; simpl; apply nlt_ge; intros J.
epose proof (sr2 (conj _ J)) as K. apply Bool.diff_false_true. revert K. erewrite <- sr1. unfold canr.
repeat (rewrite Bool.andb_true_iff). erewrite (validsupp2 H). erewrite (validsupp2 Lw). intros [K L]. split.
apply K. simpl. rewrite Y. apply E. eapply le_trans. 2:apply R. lia. rewrite <- Y. rewrite G.
apply L. 1,2:apply Y. destruct (sl {|sp:=_|}) eqn:Z. lia. apply Le.le_S_n in J.
epose proof (sl2 (conj J _)) as K. apply Bool.diff_false_true. revert K. rewrite <- (sl1 Z). unfold canl.
repeat (rewrite Bool.andb_true_iff). erewrite (validsupp2 H). erewrite (validsupp2 Lw). intros [K L]. split.
apply K. simpl. rewrite Y. apply E. unfold "<". rewrite <- Z. eapply le_trans. 2:apply X. rewrite (abovex A).
apply (sl0 {|sg:=_|}). rewrite <- Y. rewrite G. apply L. simpl. 1,2:apply Y.
replace (sp u) with (fst(sp u),S y). eenough (is_empty _) as K. apply K. rewrite empty_equiv. apply E.
rewrite <- (abovex A). apply X1. rewrite <- empty_equiv. rewrite <- Y. rewrite G.
destruct u as [[??]??]. apply H0. rewrite <- Y. destruct u as [[??]??]. split. lia. rewrite (abovex A).
eapply le_trans. 2:apply R. apply Le.le_n_S. apply sr0. rewrite H1.  destruct s. split.
revert H. unfold lvl0. revert Lt. unfold lvl. unfold valid. unfold Neg.validd. simpl. tauto.
destruct IHD as [n IH]. epose proof (mimicstep n H H0) as [m M]. exists m. intros t J.
destruct (M _ J) as [v[V L]]. destruct (IH _ L) as [w[W I]]. exists w. split. destruct V as [V|V]. rewrite V.
tauto. eapply rt_trans. apply rt_step. apply V. tauto. tauto. Unshelve. apply (sr0 {|sg:=_|}). unfold "<".
rewrite <- Z. apply (sl0 {|sg:=_|}). Qed.

Lemma solid_equiv {t} : is_solid t <-> emptyb t = false.
erewrite (_:forall x y,x=y <-> y=x). unfold is_solid. repeat (rewrite tile_dec). destruct t; tauto. Unshelve.
intros ??. split; intros H; symmetry; tauto. Qed.
Lemma lvl0_cantl {s y}: lvl0 y s -> cantl (sl s) y s.
intros L. split. apply (proj1 L). split. destruct (sl s) eqn:X. tauto. apply sl1 in X. rewrite solid_equiv.
rewrite supported_equiv. rewrite Bool.not_true_iff_false. revert X. unfold canl. rewrite Bool.andb_false_iff.
rewrite (proj1 (proj2 L)). rewrite (validsupp2 L). tauto. split. split. rewrite (proj1 (proj2 L)). lia.
intros _. apply sl0. Qed.
Lemma lvl0_cantr {s y}: lvl0 y s -> cantr (sr s) y s.
intros L. split. apply (proj1 L). split. rewrite solid_equiv. rewrite supported_equiv. rewrite <- (validsupp2 L).
rewrite Bool.not_true_iff_false. rewrite <- (proj1 (proj2 L)). apply or_comm. rewrite <- Bool.andb_false_iff.
apply sr1. split. split. rewrite (proj1 (proj2 L)). lia. intros _. apply sr0. Qed.

Lemma lvl_withp {y p s}: lvl y s -> snd p = y -> lvl y (withp p s).
destruct s. unfold withp. unfold lvl. tauto. Qed.
Lemma innil {A l}: (forall a:A, ~In a l) -> l = []. destruct l. split. intros H. exfalso. eapply H.
left. split. Qed.
Lemma dropreach {y s t}: drop y t s -> can_reach s t.
intros D. induction D. apply rt_step. rewrite H1. destruct s. apply step_move. apply move_down. split.
rewrite H1 in H0. apply H0. eapply rt_trans. apply rt_step. apply H. apply IHD. Qed.
Lemma reach1t {s t p}: can_reach s t -> Neg.reach1 t p -> Neg.reach1 s p.
intros R [u[U P]]. exists u. split. eapply rt_trans. apply R. all:tauto. Qed.
Lemma dropsreach {y s p}: drops p y s -> Neg.reach1 s p.
intros D. induction D. tauto. apply (reach1t (dropreach H0) IHD). Qed.
Lemma lvle_inside {y s t u}: drop y u t -> lvle y s t -> sl s <= sl t -> sr s >= min (S(sr u)) (sr t) ->
  exists v, can_reach s v /\ inside (S y) u v.
intros D [Ls[Lt F]] H J. assert (s=t \/ forall x, sl t<=x<=min(sr s)(sr t)->is_empty(ev(sg s)(x,y))) as [E|E].
destruct Ls as [_[Ls _]],Lt as [_[Lt _]]. destruct F as [[F _]|[G F]]. right. intros x X.
epose proof lrempty as [E|E]. 4:apply E. 1,2:simpl; lia. rewrite E. apply F.
destruct (PosDec.eq_dec(sp s)(sp t)) as [N|N]. left. destruct s,t. unfold PosDec.eq in N. simpl in G,F,N.
rewrite G,F,N. split. right. intros x X. epose proof lrempty as [E|E]. 4:apply E. 1,2:simpl; lia. rewrite G.
epose proof lrempty as [K|K]. 4:apply K. 1,2:simpl; lia. destruct N. rewrite <- E. apply K. exists u. rewrite E.
split. apply (dropreach D). apply dropt in D. unfold inside. unfold leftof. unfold lvle. split. split. tauto.
1,2:lia. assert (exists r1, min(sr t)r1<=sr s<=r1/\sr u<r1) as [r1[[??]K]].
exists (max(S(sr u))(sr s)). lia. epose proof (mimicinside K D) as [n M].
epose proof (M (withp (minx r1 (sp t)) s) _) as [v[V I]]. exists v. split. eapply rt_trans. 2:apply V.
apply moveh. 1,2:unfold minx; simpl. revert Ls Lt. unfold lvl0. lia. pose proof (sr0 t). pose proof (sl0 t).
pose proof (sr0 s). pose proof (sl0 s). lia. apply I. Unshelve. split. apply lvl_withp. apply (lvl1 Ls).
unfold minx. unfold lvl0 in Lt. tauto. split. apply (lvl1 Lt). split. apply (lvl0_cantl Lt). split.
apply (lvl0_cantr Lt). split. destruct s. split. split. rewrite innil. symmetry. apply innil. 1,2:intros p;
rewrite filter_In. rewrite Bool.andb_true_iff. 1,2:rewrite eqb_eq. intros [I[_ Y]]. destruct Lt as [_[_ Lt]].
apply droplast_in in I. apply Lt in I. lia. intros [I Y]. destruct Ls as [_[_ Ls]]. destruct s. apply Ls in I.
lia. replace (sg _) with (sg s). intros x X. apply E. lia. destruct s. split. Qed.

Lemma lrreach {s y p}: lvl0 y s -> Neg.reach1 s p -> snd p = y -> sl s <= fst p <= sr s.
intros Ls [t[T P]]. rewrite <- P. intros Y. split. epose proof (Neg.inv1 cantlinv T _) as [_[_[_ H]]].
apply (H Y). epose proof (Neg.inv1 cantrinv T _) as [_[_[_ H]]]. apply (H Y). Unshelve. apply lvl0_cantl.
tauto. apply lvl0_cantr. tauto. Qed.
#[local] Instance lvle_Symmetric (y:nat): RelationClasses.Symmetric (lvle y).
intros s t. unfold lvle. intros [?[?[F|[J K]]]]. tauto. rewrite J,K. tauto. Qed.
Lemma inside_reach {y s t p}: drops p y s -> inside y s t -> Neg.reach1 t p.
intros D. generalize t. clear t. induction D; intros t. intros [[[Ls[[_[Lt _]]_]]R]L]. eexists. split.
eapply moveh. rewrite H0. lia. pose proof (lrreach Ls H1 H0). lia. destruct t. split. intros [[E R]L].
symmetry in E. epose proof (lvle_inside H0 E L _) as [v[V I]]. apply IHD in I. apply (reach1t V I). Unshelve.
lia. Qed.
Lemma dropsy {s y p}: drops p y s -> snd p >= y. intros D. induction D; lia. Qed.
Definition cantrd x y s := cantr x y s /\ forall p, In p (sd s) -> snd p = S y -> fst p <= x.
Lemma cantrdinv {x y}: Neg.inv (cantrd x y).
intros s t R [C D]. split. apply (cantrinv _ _ R C). inversion R. rewrite <- H1 in D. apply D. intros q [Q|Q] Y.
rewrite <- Q. rewrite <- (abovex H0). rewrite <- H5 in C. apply (cantr_beside C H H1 H3). revert Y.
rewrite <- Q. rewrite (abovey H0). rewrite <- (Neg.besidey H). simpl. lia. rewrite <- H5 in D.
apply (D _ Q Y). intros v V Y. apply D. rewrite <- H1. apply in_app_iff. left. apply V. tauto. Qed.
Lemma dropx {s t x y}: drop y t s -> lvl y s -> cantr x y s -> fst (sp t) <= x.
intros D. induction D. intros [_[Y _]] [_[_[_ X]]]. erewrite <- abovex. apply X. apply Y. rewrite H1. destruct s.
split. intros L C. apply IHD. tauto. apply (cantrinv _ _ H C). Qed.
Lemma leftof_reach {x1 x2 y z s t}: x1<=x2 -> leftof y s t -> Neg.reach1 s (x2,z) -> Neg.reach1 t (x1,z) ->
  Neg.reach1 s (x1,z) \/ Neg.reach1 t (x2,z).
intros X L R2 R1. apply (drops1 y) in R1,R2. 2,3:apply lvl1;
destruct L as [[?[? _]]_]; tauto. revert L R1. generalize t. clear t. induction R2; intros t L D.
destruct L as [[Ls[Lt _]]I]. apply dropsreach in D. pose proof (lrreach Ls H1 H0). pose proof (lrreach Lt D H0).
right. eexists. split. eapply moveh. 3:destruct t; split. rewrite (proj1(proj2 Lt)). apply H0. simpl.
simpl in H2,H3. lia. inversion D. apply dropsy in R2. simpl in R2,H2. lia.
destruct (Compare_dec.le_lt_dec(sl t)(sl s)) as [J|J]. right. eapply (inside_reach _ (conj L J)).
destruct (Compare_dec.le_lt_dec(sr t0)(sr t1)) as [K|K]. epose proof (IHR2 t1 _ H3) as [R|R]. left.
apply (reach1t (dropreach H0) R). right. apply (reach1t (dropreach H2) R). left.
epose proof (lvle_inside H2 (proj1 L) _ _) as [v[R I]]. eapply reach1t. apply R. apply (inside_reach H3 I).
Unshelve. apply (drop1 _ _ t0); tauto. apply dropt in H0. apply dropt in H2. unfold leftof. unfold lvle.
tauto. lia. enough (sr t1<sr s). lia. pose proof (dropt H0) as [L1 _]. pose proof (dropt H2) as [L2 _].
pose proof L as [[L0 _]_]. destruct (Compare_dec.le_lt_dec(fst(sp t0))(sr t1)) as [M|M].
pose proof (sr2 (conj M K)) as B. replace (snd _) with (S y) in B. pose proof (@sr1 t1) as C.
replace (snd _) with (S y) in C. unfold canr in B,C. rewrite (validsupp2 L1) in B. rewrite (validsupp2 L2) in C.
rewrite Bool.andb_true_iff in B. destruct B as [B1 B2]. rewrite B1 in C. simpl in C. apply proj1 in L1,L2.
epose proof (proj2 L1 _) as [[I _]|[_ E]]. 2:rewrite E in B2.
epose proof (Neg.inv1 cantrdinv (dropreach H0) _) as [_ N]. apply N in I. apply I. 1,3,4:split.
epose proof (valid1 _ L2) as [F|[_ F]]. rewrite F in C. rewrite B2 in C. inversion C. rewrite F in B2.
inversion B2. 1,2:symmetry; unfold lvl0 in L1,L2; tauto.
pose proof (dropx H0 (lvl1 L0) (lvl0_cantr L0)). lia. Unshelve. split. apply (lvl0_cantr L0). intros p P Y.
destruct L0 as [_[_ L0]]. apply L0 in P. lia. Qed.

Lemma can_reach_pos1 {p q}: can_reach_pos g p q <-> Neg.reach1 {|sp:=p;sg:=g;sd:=[]|} q.
split. intros [?[? R]]. eexists. split. apply R. split. intros [[???][R E]]. rewrite <- E. repeat eexists.
apply R. Qed.
Lemma lvl0g {x y}: lvl0 y {|sp:=(x,y);sg:=g;sd:=[]|}.
split. split. split. apply NoDup_nil. intros ? []. right. split. tauto. split. split. split. intros ? []. Qed.
Theorem nocross1 {x1 x2 y u1 u2 z}: x1<=x2 -> u1 <= u2 -> can_reach_pos g (x1,y) (u2,z) ->
  can_reach_pos g (x2,y) (u1,z) -> can_reach_pos g (x1,y) (u1,z) \/ can_reach_pos g (x2,y) (u2,z).
repeat (rewrite can_reach_pos1). intros X U R1 R2. eapply (leftof_reach U _ R1 R2). Unshelve. exact y. split.
split. apply lvl0g. split. apply lvl0g. right. repeat split. epose proof (Compare_dec.le_lt_dec _ _) as [H|H].
apply H. set ({|sp:=(x2,y)|}) as t. exfalso. apply Bool.diff_false_true. erewrite <- (sr2 (conj _ H)).
erewrite <- (@sr1 t). split. Unshelve. eapply le_trans. apply X. apply (@sr0 t). Qed.
Theorem nocross: ~cross g.
intros [w[h[R[H1[H2 ?]]]]]. epose proof (nocross1 _ _ H1 H2). tauto. Unshelve. all:lia. Qed. 
End NeedL.
End NeedL.

Definition tile_union := ListSet.set_union tile_eq_dec.
Definition tile_mem := ListSet.set_mem tile_eq_dec.
Definition alltiles g := fold_right (fun x y => tile_union y x) [] g.
Lemma alltiles_equiv {g t}: contains g t <-> In t (alltiles g).
induction g; split. intros [?[_[]]]. intros []. intros [?[I[J|J]]]; apply ListSet.set_union_intro. rewrite J.
tauto. left. apply IHg. eexists. apply (conj I J). intros H. apply ListSet.set_union_elim in H.
rewrite <- IHg in H. destruct H as [[r H]|H]. exists r. simpl. tauto. eexists. split. apply H. left. split. Qed.
Lemma tile_mem_equiv {l t}: In t l <-> tile_mem t l = true.
split. apply ListSet.set_mem_correct2. apply ListSet.set_mem_correct1. Qed.
Lemma contains_dec {g t}: contains g t \/ ~contains g t.
rewrite alltiles_equiv. rewrite tile_mem_equiv. pose proof Bool.diff_false_true. destruct (_ t _); tauto. Qed.

Theorem exists_cross_proof: exists_cross. eexists. apply Cross.cr. Qed.
Definition cross_required_tiles_proof: cross_required_tiles.
split. intros [g[C T]]. destruct (@contains_dec g brick) as [B|B]. destruct (@contains_dec g ladder) as [L|L].
intros ? [E|[E|[]]]; rewrite <- E; apply T; tauto. destruct (NeedL.nocross L C). destruct (NeedB.nocross B C).
intros L. eexists. split. apply BL.cr. intros t. rewrite alltiles_equiv. intros [H|[H|[]]]; apply L; simpl;
tauto. Qed.
