From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* TODO: add model to stdlib vector, prove against that model *)
Lemma vec_extract_invariant {T_inner_rt T_rt A_rt} (P : ex_inv_def T_inner_rt T_rt) (T_ty : type T_inner_rt) (A_ty : type A_rt) (A_attrs : Allocator_spec_attrs A_rt) π xs l F :
  lftE ⊆ F →
  l ◁ₗ[π, Owned] #(<#> xs) @ (◁ (Vec_inv_t T_rt A_rt A_attrs <TY> (∃; P, T_ty) <TY> A_ty <INST!>)) ={F}=∗
  ∃ (xs' : list (RT_rt T_inner_rt)), 
  ([∗ list] x1; x2 ∈ xs'; xs, P.(inv_P) π x1 x2) ∗
  (l ◁ₗ[π, Owned] #(<#> xs') @ (◁ (Vec_inv_t T_inner_rt A_rt A_attrs *[] *[T_ty; A_ty]))).
Proof.
Admitted.

Lemma extract_page_token_invariants `{!onceG Σ memory_layout} {S_rt : RT} (S_attrs : core_page_allocator_page_PageState_spec_attrs S_rt) (S_ty : type S_rt) π xs xs' F :
  lftE ⊆ F →
  ([∗ list] x1; x2 ∈ xs'; xs, (core_page_allocator_page_Page_inv_t_inv_spec S_rt S_attrs <TY> S_ty <INST!>).(inv_P) π x1 x2) ={F}=∗
  ([∗ list] p ∈ xs, p.(page_loc) ◁ₗ[π, Owned] # (<#> p.(page_val)) @ ◁ array_t (page_size_in_words_nat p.(page_sz)) (int usize)).
Proof.
  iIntros (?) "Ha".
  iApply big_sepL_fupd.
  iApply (big_sepL2_elim_l xs').
  iApply (big_sepL2_impl with "Ha").
  iModIntro. iIntros (? inner pg Hlook1 Hlook2) "Hinv". 
  simpl. iDestruct "Hinv" as "(%MEM & -> & Hpg & _)".
  rewrite /guarded. iDestruct "Hpg" as "(((Hc1 & _) & _)& Hpg)".
  iApply (lc_fupd_add_later with "Hc1"). iNext. 
  by iFrame. 
Qed.

Lemma core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge_proof (π : thread_id) :
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge_lemma π.
Proof.
  core_page_allocator_page_Page_core_page_allocator_page_UnAllocated_merge_prelude.

  rep <-! liRStep; liShow.
  2: { rep liRStep; liShow. }
  2: { rep liRStep; liShow. }
  opose proof (page_size_multiplier_ge new_size) as ?.
  opose proof (lookup_lt_is_Some_2 from_pages 0%nat _) as [pg_0 Hlook_pg0].
  { lia. }
  destruct pg_0 as [pg_loc_0 pg_sz_0 pg_val_0].
  rep <-! liRStep; liShow.
  opose proof (lookup_lt_is_Some_2 from_pages (length from_pages - 1) _) as [pg_last Hlook_pg_last].
  { lia. }
  destruct pg_last as [pg_loc_last pg_sz_last pg_val_last].
  rep <-! liRStep; liShow.
  2: { rep liRStep; liShow. }
  2: { rep liRStep; liShow. }

  iRename select (arg_from_pages ◁ₗ[π, Owned] _ @ _)%I into "Hvec".
  iApply updateable_add_fupd.
  iMod (vec_extract_invariant with "Hvec") as "(%xs' & Hinv & Hvec)"; first done.
  iMod (extract_page_token_invariants with "Hinv") as "Harrs"; first done.

  iMod (array_t_ofty_merge (int usize) π _ (page_size_in_words_nat pg_sz_0) ((λ p, <#> p.(page_val)) <$> from_pages) (pg_loc_0) with "[Harrs]") as "Harr"; first done.
  { rewrite length_fmap. lia. }
  { rewrite length_fmap. rewrite /size_of_st/use_layout_alg'. simpl.
    erewrite syn_type_has_layout_int; last done.
    simpl. rewrite Hlen.
    rewrite bytes_per_int_usize.
    
    specialize (page_size_in_bytes_nat_in_isize new_size) as [_ Hsz].
    move: Hsz. rewrite /page_size_in_bytes_nat. 
    opose proof * (page_size_multiplier_size_in_words new_size smaller_sz) as Hw. 
    { rewrite Hsmaller//. }
    rewrite Hw. 
    apply Hlook in Hlook_pg0 as [Hsz0 _]. simpl in Hsz0.
    rewrite Hsz0. lia. }
  { rewrite big_sepL_fmap. iApply (big_sepL_impl with "Harrs").
    iModIntro. iIntros (?? Hlook').
    apply Hlook in Hlook'. 
    (* TODO: provenance is problematic.
       Probably for now we should assume a fixed "hardware provenance". Page token invariant says that the prov is fixed to that. 
    *)
    admit. }
  repeat iClear select (page_loc (from_pages !!! Z.to_nat 0) ◁ₗ[ π, Shared _] _ @ _)%I.
  iModIntro.
  rep liRStep; liShow.
  erewrite list_lookup_total_correct; last done. simpl.
  rep liRStep; liShow.
  liInst Hevar_x0 (mjoin (page_val <$> from_pages)).
  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rewrite Hlen. specialize (page_size_multiplier_ge new_size). lia.
  - specialize (page_size_in_words_nat_ge (page_sz (from_pages !!! 0%nat))). lia.
  - specialize (page_size_in_words_nat_ge (page_sz (from_pages !!! 0%nat))). lia.
  - rewrite page_size_multiplier_quot_Z; first solve_goal.
    rewrite Hsmaller.
    opose proof (lookup_lt_is_Some_2 from_pages 0%nat _) as [pg_0 Hlook_pg0]; first lia.
    erewrite list_lookup_total_correct; last done.
    apply Hlook in Hlook_pg0 as [-> _]. done.
  - admit.
  - revert select (_ `quot` _ ≠ length from_pages).
    rewrite page_size_multiplier_quot_Z; first solve_goal.
    rewrite Hsmaller.
    opose proof (lookup_lt_is_Some_2 from_pages 0%nat _) as [pg_0 Hlook_pg0]; first lia.
    erewrite list_lookup_total_correct; last done.
    apply Hlook in Hlook_pg0 as [-> _]. done.
  - revert select (¬ _ `aligned_to` _).
    rewrite -page_size_align_is_size. done.
  - revert select (¬ length from_pages > 2).
    rewrite Hlen.
    revert Hsmaller. clear. 
    destruct new_size; first done.
    all: intros _; unfold page_size_multiplier, page_size_multiplier_log; lia. 
  - admit. 
  - 
    ; simpl. 
    Search page_size_multiplier.

    opose proof (lookup_lt_is_Some_2 from_pages 0%nat _) as [pg_0 Hlook_pg0]; first lia.
    erewrite list_lookup_total_correct; last done.
    apply Hlook in Hlook_pg0 as Ha. done.



    Search Z.quot page_size_multiplier.
    (* this is equal to page

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
